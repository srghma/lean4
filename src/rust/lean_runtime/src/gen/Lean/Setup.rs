// Lean compiler output
// Module: Lean.Setup
// Imports: Lean.Data.Json.Parser Lean.Util.LeanOptions
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::{l_Bool_repr___redArg, l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Meta::Defs::{l_Lean_Name_reprPrec, l_String_toName};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
use crate::r#gen::Init::System::IO::l_IO_FS_readFile;
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getBool_x3f, l_Lean_Json_getObjValD, l_Lean_Json_getStr_x3f, l_Lean_Json_mkObj,
    l_Lean_JsonNumber_fromNat,
};
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::{
    l_Array_fromJson_x3f___redArg, l_Array_toJson___redArg, l_Lean_Name_fromJson_x3f,
    l_Lean_instFromJsonFilePath___lam__0, l_Lean_instToJsonFilePath___lam__0,
};
use crate::r#gen::Lean::Data::Json::Parser::{
    initialize_Lean_Data_Json_Parser, l_Lean_Json_parse, runtime_initialize_Lean_Data_Json_Parser,
};
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_pretty;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg;
use crate::r#gen::Lean::Util::LeanOptions::{
    initialize_Lean_Util_LeanOptions, l_Lean_instReprLeanOptions_repr___redArg,
    runtime_initialize_Lean_Util_LeanOptions,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_lt, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Ord::String::lean_string_compare;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_panic_fn_borrowed, lean_string_dec_eq,
    lean_uint64_mix_hash, lean_uint64_of_nat,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_box_uint64, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once,
    lean_obj_tag, lean_uint64_once, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_instReprImport_repr___redArg___closed__0_value: LeanStringObject<3> =
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
static mut l_Lean_instReprImport_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_instReprImport_repr___redArg___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [109, 111, 100, 117, 108, 101, 0],
    };
static mut l_Lean_instReprImport_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_instReprImport_repr___redArg___closed__2_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprImport_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_instReprImport_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprImport_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lean_instReprImport_repr___redArg___closed__4_value: LeanStringObject<5> =
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
static mut l_Lean_instReprImport_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lean_instReprImport_repr___redArg___closed__5_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprImport_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lean_instReprImport_repr___redArg___closed__6_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprImport_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_instReprImport_repr___redArg___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprImport_repr___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprImport_repr___redArg___closed__8_value: LeanStringObject<2> =
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
static mut l_Lean_instReprImport_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__8_value) as *mut LeanObject;
pub static l_Lean_instReprImport_repr___redArg___closed__9_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprImport_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__9_value) as *mut LeanObject;
pub static l_Lean_instReprImport_repr___redArg___closed__10_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [105, 109, 112, 111, 114, 116, 65, 108, 108, 0],
    };
static mut l_Lean_instReprImport_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__10_value) as *mut LeanObject;
pub static l_Lean_instReprImport_repr___redArg___closed__11_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprImport_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__11_value) as *mut LeanObject;
static mut l_Lean_instReprImport_repr___redArg___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprImport_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprImport_repr___redArg___closed__13_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [105, 115, 69, 120, 112, 111, 114, 116, 101, 100, 0],
    };
static mut l_Lean_instReprImport_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__13_value) as *mut LeanObject;
pub static l_Lean_instReprImport_repr___redArg___closed__14_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprImport_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_instReprImport_repr___redArg___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprImport_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprImport_repr___redArg___closed__16_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [105, 115, 77, 101, 116, 97, 0],
    };
static mut l_Lean_instReprImport_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__16_value) as *mut LeanObject;
pub static l_Lean_instReprImport_repr___redArg___closed__17_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__16_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprImport_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__17_value) as *mut LeanObject;
pub static l_Lean_instReprImport_repr___redArg___closed__18_value: LeanStringObject<3> =
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
static mut l_Lean_instReprImport_repr___redArg___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_instReprImport_repr___redArg___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprImport_repr___redArg___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instReprImport_repr___redArg___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprImport_repr___redArg___closed__20: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprImport_repr___redArg___closed__21_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprImport_repr___redArg___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__21_value) as *mut LeanObject;
pub static l_Lean_instReprImport_repr___redArg___closed__22_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__18_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprImport_repr___redArg___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__22_value) as *mut LeanObject;
pub static l_Lean_instReprImport___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instReprImport_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instReprImport___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImport___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instReprImport: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImport___closed__0_value) as *mut LeanObject;
pub static l_Lean_instInhabitedImport_default___closed__0_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            256 as *mut LeanObject,
        ],
    };
static mut l_Lean_instInhabitedImport_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedImport_default___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instInhabitedImport_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedImport_default___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instInhabitedImport: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedImport_default___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToJsonImport_toJson___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_instToJsonImport_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonImport_toJson___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToJsonImport___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instToJsonImport_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instToJsonImport___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonImport___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instToJsonImport: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonImport___closed__0_value) as *mut LeanObject;
pub static l_Lean_instFromJsonImport_fromJson___closed__0_value: LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_instFromJsonImport_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonImport_fromJson___closed__0_value) as *mut LeanObject;
pub static l_Lean_instFromJsonImport_fromJson___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [73, 109, 112, 111, 114, 116, 0],
    };
static mut l_Lean_instFromJsonImport_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonImport_fromJson___closed__1_value) as *mut LeanObject;
static l_Lean_instFromJsonImport_fromJson___closed__2_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instFromJsonImport_fromJson___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
pub static l_Lean_instFromJsonImport_fromJson___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instFromJsonImport_fromJson___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instFromJsonImport_fromJson___closed__1_value)
                as *mut LeanObject,
            2714575632891916061 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonImport_fromJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonImport_fromJson___closed__2_value) as *mut LeanObject;
static mut l_Lean_instFromJsonImport_fromJson___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonImport_fromJson___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_instFromJsonImport_fromJson___closed__4_value: LeanStringObject<2> =
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
        m_data: [46, 0],
    };
static mut l_Lean_instFromJsonImport_fromJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonImport_fromJson___closed__4_value) as *mut LeanObject;
static mut l_Lean_instFromJsonImport_fromJson___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonImport_fromJson___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_instFromJsonImport_fromJson___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__1_value)
                as *mut LeanObject,
            5134674735115079031 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonImport_fromJson___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonImport_fromJson___closed__6_value) as *mut LeanObject;
static mut l_Lean_instFromJsonImport_fromJson___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonImport_fromJson___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_instFromJsonImport_fromJson___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonImport_fromJson___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_instFromJsonImport_fromJson___closed__9_value: LeanStringObject<3> =
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
        m_data: [58, 32, 0],
    };
static mut l_Lean_instFromJsonImport_fromJson___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonImport_fromJson___closed__9_value) as *mut LeanObject;
static mut l_Lean_instFromJsonImport_fromJson___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonImport_fromJson___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_instFromJsonImport_fromJson___closed__11_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__10_value)
                as *mut LeanObject,
            12346639414013185847 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonImport_fromJson___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonImport_fromJson___closed__11_value) as *mut LeanObject;
static mut l_Lean_instFromJsonImport_fromJson___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonImport_fromJson___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_instFromJsonImport_fromJson___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonImport_fromJson___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_instFromJsonImport_fromJson___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonImport_fromJson___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_instFromJsonImport_fromJson___closed__15_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__13_value)
                as *mut LeanObject,
            16793762265775749650 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonImport_fromJson___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonImport_fromJson___closed__15_value) as *mut LeanObject;
static mut l_Lean_instFromJsonImport_fromJson___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonImport_fromJson___closed__16: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_instFromJsonImport_fromJson___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonImport_fromJson___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_instFromJsonImport_fromJson___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonImport_fromJson___closed__18: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_instFromJsonImport_fromJson___closed__19_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__16_value)
                as *mut LeanObject,
            4016706208181132537 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonImport_fromJson___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonImport_fromJson___closed__19_value) as *mut LeanObject;
static mut l_Lean_instFromJsonImport_fromJson___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonImport_fromJson___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_instFromJsonImport_fromJson___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonImport_fromJson___closed__21: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_instFromJsonImport_fromJson___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonImport_fromJson___closed__22: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_instFromJsonImport___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instFromJsonImport_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instFromJsonImport___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonImport___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instFromJsonImport: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonImport___closed__0_value) as *mut LeanObject;
pub static l_Lean_instBEqImport___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instBEqImport_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instBEqImport___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqImport___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instBEqImport: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqImport___closed__0_value) as *mut LeanObject;
static mut l_Lean_instHashableImport_hash___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instHashableImport_hash___closed__0: u64 = 0;
pub static l_Lean_instHashableImport___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instHashableImport_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instHashableImport___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instHashableImport___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instHashableImport: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instHashableImport___closed__0_value) as *mut LeanObject;
pub static l_Lean_instCoeNameImport___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instCoeNameImport___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instCoeNameImport___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeNameImport___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instCoeNameImport: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeNameImport___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToStringImport___lam__0___closed__0_value: LeanStringObject<8> =
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
        m_data: [105, 109, 112, 111, 114, 116, 32, 0],
    };
static mut l_Lean_instToStringImport___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToStringImport___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToStringImport___lam__0___closed__1_value: LeanStringObject<1> =
    LeanStringObject {
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
static mut l_Lean_instToStringImport___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToStringImport___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_instToStringImport___lam__0___closed__2_value: LeanStringObject<5> =
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
        m_data: [97, 108, 108, 32, 0],
    };
static mut l_Lean_instToStringImport___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToStringImport___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_instToStringImport___lam__0___closed__3_value: LeanStringObject<6> =
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
        m_data: [109, 101, 116, 97, 32, 0],
    };
static mut l_Lean_instToStringImport___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToStringImport___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_instToStringImport___lam__0___closed__4_value: LeanStringObject<8> =
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
        m_data: [112, 117, 98, 108, 105, 99, 32, 0],
    };
static mut l_Lean_instToStringImport___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToStringImport___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_instToStringImport___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instToStringImport___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instToStringImport___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToStringImport___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instToStringImport: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToStringImport___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instInhabitedIRPhases_default: u8 = 0;
pub static mut l_Lean_instInhabitedIRPhases: u8 = 0;
pub static l_Lean_instBEqIRPhases___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instBEqIRPhases_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instBEqIRPhases___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqIRPhases___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instBEqIRPhases: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqIRPhases___closed__0_value) as *mut LeanObject;
pub static l_Lean_instReprIRPhases_repr___closed__0_value: LeanStringObject<22> =
    LeanStringObject {
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
            76, 101, 97, 110, 46, 73, 82, 80, 104, 97, 115, 101, 115, 46, 114, 117, 110, 116, 105,
            109, 101, 0,
        ],
    };
static mut l_Lean_instReprIRPhases_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprIRPhases_repr___closed__0_value) as *mut LeanObject;
pub static l_Lean_instReprIRPhases_repr___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprIRPhases_repr___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_instReprIRPhases_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprIRPhases_repr___closed__1_value) as *mut LeanObject;
pub static l_Lean_instReprIRPhases_repr___closed__2_value: LeanStringObject<23> =
    LeanStringObject {
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
            76, 101, 97, 110, 46, 73, 82, 80, 104, 97, 115, 101, 115, 46, 99, 111, 109, 112, 116,
            105, 109, 101, 0,
        ],
    };
static mut l_Lean_instReprIRPhases_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprIRPhases_repr___closed__2_value) as *mut LeanObject;
pub static l_Lean_instReprIRPhases_repr___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprIRPhases_repr___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_instReprIRPhases_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprIRPhases_repr___closed__3_value) as *mut LeanObject;
pub static l_Lean_instReprIRPhases_repr___closed__4_value: LeanStringObject<18> =
    LeanStringObject {
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
            76, 101, 97, 110, 46, 73, 82, 80, 104, 97, 115, 101, 115, 46, 97, 108, 108, 0,
        ],
    };
static mut l_Lean_instReprIRPhases_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprIRPhases_repr___closed__4_value) as *mut LeanObject;
pub static l_Lean_instReprIRPhases_repr___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprIRPhases_repr___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_instReprIRPhases_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprIRPhases_repr___closed__5_value) as *mut LeanObject;
static mut l_Lean_instReprIRPhases_repr___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprIRPhases_repr___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_instReprIRPhases_repr___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprIRPhases_repr___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprIRPhases___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instReprIRPhases_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instReprIRPhases___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprIRPhases___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instReprIRPhases: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprIRPhases___closed__0_value) as *mut LeanObject;
pub static l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__0_value:
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
    m_data: [35, 91, 0],
};
static mut l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__9_value)
            as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__2_value:
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
    m_data: [93, 0],
};
static mut l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__2_value
) as *mut LeanObject;
static mut l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5_value:
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
        l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6_value:
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
        l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__2_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__7_value:
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
    m_data: [35, 91, 93, 0],
};
static mut l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__7_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8_value:
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
        l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__7_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8_value
) as *mut LeanObject;
pub static l_Lean_instReprModuleHeader_repr___redArg___closed__0_value: LeanStringObject<8> =
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
        m_data: [105, 109, 112, 111, 114, 116, 115, 0],
    };
static mut l_Lean_instReprModuleHeader_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleHeader_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleHeader_repr___redArg___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprModuleHeader_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprModuleHeader_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleHeader_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleHeader_repr___redArg___closed__2_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instReprModuleHeader_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprModuleHeader_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleHeader_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleHeader_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instReprModuleHeader_repr___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprModuleHeader_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleHeader_repr___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_instReprModuleHeader_repr___redArg___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprModuleHeader_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprModuleHeader_repr___redArg___closed__5_value: LeanStringObject<9> =
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
        m_data: [105, 115, 77, 111, 100, 117, 108, 101, 0],
    };
static mut l_Lean_instReprModuleHeader_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleHeader_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleHeader_repr___redArg___closed__6_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprModuleHeader_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprModuleHeader_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleHeader_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_instReprModuleHeader_repr___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprModuleHeader_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprModuleHeader___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprModuleHeader_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprModuleHeader___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleHeader___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instReprModuleHeader: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleHeader___closed__0_value) as *mut LeanObject;
pub static l_Lean_instInhabitedModuleHeader_default___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_instInhabitedModuleHeader_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedModuleHeader_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instInhabitedModuleHeader_default___closed__1_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instInhabitedModuleHeader_default___closed__0_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_instInhabitedModuleHeader_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedModuleHeader_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_instInhabitedModuleHeader_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedModuleHeader_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_instInhabitedModuleHeader: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedModuleHeader_default___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_instToJsonModuleHeader___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instToJsonModuleHeader_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToJsonModuleHeader___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonModuleHeader___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instToJsonModuleHeader: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonModuleHeader___closed__0_value) as *mut LeanObject;
pub static l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_instFromJsonModuleHeader_fromJson___closed__0_value: LeanStringObject<13> =
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
        m_data: [77, 111, 100, 117, 108, 101, 72, 101, 97, 100, 101, 114, 0],
    };
static mut l_Lean_instFromJsonModuleHeader_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleHeader_fromJson___closed__0_value)
        as *mut LeanObject;
static l_Lean_instFromJsonModuleHeader_fromJson___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instFromJsonImport_fromJson___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
pub static l_Lean_instFromJsonModuleHeader_fromJson___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instFromJsonModuleHeader_fromJson___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instFromJsonModuleHeader_fromJson___closed__0_value)
                as *mut LeanObject,
            9855681160333460924 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonModuleHeader_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleHeader_fromJson___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_instFromJsonModuleHeader_fromJson___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleHeader_fromJson___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleHeader_fromJson___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleHeader_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonModuleHeader_fromJson___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprModuleHeader_repr___redArg___closed__0_value)
                as *mut LeanObject,
            12195267273951749211 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonModuleHeader_fromJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleHeader_fromJson___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_instFromJsonModuleHeader_fromJson___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleHeader_fromJson___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleHeader_fromJson___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleHeader_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleHeader_fromJson___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleHeader_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonModuleHeader_fromJson___closed__8_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprModuleHeader_repr___redArg___closed__5_value)
                as *mut LeanObject,
            7302028909095907647 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonModuleHeader_fromJson___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleHeader_fromJson___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_instFromJsonModuleHeader_fromJson___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleHeader_fromJson___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleHeader_fromJson___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleHeader_fromJson___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleHeader_fromJson___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleHeader_fromJson___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonModuleHeader___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instFromJsonModuleHeader_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instFromJsonModuleHeader___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleHeader___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instFromJsonModuleHeader: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleHeader___closed__0_value) as *mut LeanObject;
pub static l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [70, 105, 108, 101, 80, 97, 116, 104, 46, 109, 107, 32, 0]};
static mut l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__0_value) as *mut LeanObject;
pub static l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__0_value) as *mut LeanObject] };
static mut l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__1_value) as *mut LeanObject;
pub static l_Lean_instReprImportArtifacts_repr___redArg___closed__0_value: LeanStringObject<8> =
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
        m_data: [116, 111, 65, 114, 114, 97, 121, 0],
    };
static mut l_Lean_instReprImportArtifacts_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImportArtifacts_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instReprImportArtifacts_repr___redArg___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprImportArtifacts_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprImportArtifacts_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImportArtifacts_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_instReprImportArtifacts_repr___redArg___closed__2_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instReprImportArtifacts_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprImportArtifacts_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImportArtifacts_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_instReprImportArtifacts_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instReprImportArtifacts_repr___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprImportArtifacts_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImportArtifacts_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_instReprImportArtifacts___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprImportArtifacts_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprImportArtifacts___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImportArtifacts___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instReprImportArtifacts: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprImportArtifacts___closed__0_value) as *mut LeanObject;
pub static l_Lean_instInhabitedImportArtifacts_default___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_instInhabitedImportArtifacts_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedImportArtifacts_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_instInhabitedImportArtifacts_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedImportArtifacts_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_instInhabitedImportArtifacts: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedImportArtifacts_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instToJsonImportArtifacts___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instToJsonFilePath___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToJsonImportArtifacts___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonImportArtifacts___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToJsonImportArtifacts___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_instToJsonImportArtifacts___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_instToJsonImportArtifacts___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instToJsonImportArtifacts___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonImportArtifacts___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_instToJsonImportArtifacts: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonImportArtifacts___closed__1_value) as *mut LeanObject;
pub static l_Lean_instFromJsonImportArtifacts___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instFromJsonFilePath___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instFromJsonImportArtifacts___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonImportArtifacts___closed__0_value) as *mut LeanObject;
pub static l_Lean_instFromJsonImportArtifacts___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_instFromJsonImportArtifacts___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_instFromJsonImportArtifacts___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonImportArtifacts___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonImportArtifacts___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_instFromJsonImportArtifacts: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonImportArtifacts___closed__1_value) as *mut LeanObject;
pub static l_Lean_ImportArtifacts_oleanParts___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_ImportArtifacts_oleanParts___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ImportArtifacts_oleanParts___closed__0_value) as *mut LeanObject;
pub static l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__0_value:
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
static mut l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__1_value:
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
        l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__1_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__2_value:
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
static mut l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__2_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__3_value:
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
        l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__2_value
    ) as *mut LeanObject],
};
static mut l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__3_value
) as *mut LeanObject;
pub static l_Lean_instReprModuleArtifacts_repr___redArg___closed__0_value: LeanStringObject<6> =
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
        m_data: [108, 101, 97, 110, 63, 0],
    };
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleArtifacts_repr___redArg___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleArtifacts_repr___redArg___closed__2_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleArtifacts_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprModuleArtifacts_repr___redArg___closed__5_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [111, 108, 101, 97, 110, 63, 0],
    };
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleArtifacts_repr___redArg___closed__6_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleArtifacts_repr___redArg___closed__7_value: LeanStringObject<13> =
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
        m_data: [111, 108, 101, 97, 110, 83, 101, 114, 118, 101, 114, 63, 0],
    };
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleArtifacts_repr___redArg___closed__8_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprModuleArtifacts_repr___redArg___closed__10_value: LeanStringObject<14> =
    LeanStringObject {
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
            111, 108, 101, 97, 110, 80, 114, 105, 118, 97, 116, 101, 63, 0,
        ],
    };
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleArtifacts_repr___redArg___closed__11_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_instReprModuleArtifacts_repr___redArg___closed__10_value
        ) as *mut LeanObject],
    };
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprModuleArtifacts_repr___redArg___closed__13_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [105, 108, 101, 97, 110, 63, 0],
    };
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleArtifacts_repr___redArg___closed__14_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_instReprModuleArtifacts_repr___redArg___closed__13_value
        ) as *mut LeanObject],
    };
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleArtifacts_repr___redArg___closed__15_value: LeanStringObject<4> =
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
        m_data: [105, 114, 63, 0],
    };
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleArtifacts_repr___redArg___closed__16_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_instReprModuleArtifacts_repr___redArg___closed__15_value
        ) as *mut LeanObject],
    };
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__16_value)
        as *mut LeanObject;
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprModuleArtifacts_repr___redArg___closed__18_value: LeanStringObject<3> =
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
        m_data: [99, 63, 0],
    };
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleArtifacts_repr___redArg___closed__19_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_instReprModuleArtifacts_repr___redArg___closed__18_value
        ) as *mut LeanObject],
    };
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__19_value)
        as *mut LeanObject;
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__20: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprModuleArtifacts_repr___redArg___closed__21_value: LeanStringObject<4> =
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
        m_data: [98, 99, 63, 0],
    };
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__21_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleArtifacts_repr___redArg___closed__22_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_instReprModuleArtifacts_repr___redArg___closed__21_value
        ) as *mut LeanObject],
    };
static mut l_Lean_instReprModuleArtifacts_repr___redArg___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__22_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleArtifacts___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprModuleArtifacts_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprModuleArtifacts___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleArtifacts___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instReprModuleArtifacts: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleArtifacts___closed__0_value) as *mut LeanObject;
pub static l_Lean_instInhabitedModuleArtifacts_default___closed__0_value: LeanCtorObject<8> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 8
                + 0) as u16,
            other: 8,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_instInhabitedModuleArtifacts_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedModuleArtifacts_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_instInhabitedModuleArtifacts_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedModuleArtifacts_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_instInhabitedModuleArtifacts: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedModuleArtifacts_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instToJsonModuleArtifacts_toJson___closed__0_value: LeanStringObject<5> =
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
        m_data: [108, 101, 97, 110, 0],
    };
static mut l_Lean_instToJsonModuleArtifacts_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonModuleArtifacts_toJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instToJsonModuleArtifacts_toJson___closed__1_value: LeanStringObject<6> =
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
        m_data: [111, 108, 101, 97, 110, 0],
    };
static mut l_Lean_instToJsonModuleArtifacts_toJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonModuleArtifacts_toJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_instToJsonModuleArtifacts_toJson___closed__2_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [111, 108, 101, 97, 110, 83, 101, 114, 118, 101, 114, 0],
    };
static mut l_Lean_instToJsonModuleArtifacts_toJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonModuleArtifacts_toJson___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_instToJsonModuleArtifacts_toJson___closed__3_value: LeanStringObject<13> =
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
        m_data: [111, 108, 101, 97, 110, 80, 114, 105, 118, 97, 116, 101, 0],
    };
static mut l_Lean_instToJsonModuleArtifacts_toJson___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonModuleArtifacts_toJson___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_instToJsonModuleArtifacts_toJson___closed__4_value: LeanStringObject<6> =
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
        m_data: [105, 108, 101, 97, 110, 0],
    };
static mut l_Lean_instToJsonModuleArtifacts_toJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonModuleArtifacts_toJson___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_instToJsonModuleArtifacts_toJson___closed__5_value: LeanStringObject<3> =
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
        m_data: [105, 114, 0],
    };
static mut l_Lean_instToJsonModuleArtifacts_toJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonModuleArtifacts_toJson___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_instToJsonModuleArtifacts_toJson___closed__6_value: LeanStringObject<2> =
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
        m_data: [99, 0],
    };
static mut l_Lean_instToJsonModuleArtifacts_toJson___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonModuleArtifacts_toJson___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_instToJsonModuleArtifacts_toJson___closed__7_value: LeanStringObject<3> =
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
        m_data: [98, 99, 0],
    };
static mut l_Lean_instToJsonModuleArtifacts_toJson___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonModuleArtifacts_toJson___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_instToJsonModuleArtifacts___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instToJsonModuleArtifacts_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToJsonModuleArtifacts___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonModuleArtifacts___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instToJsonModuleArtifacts: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonModuleArtifacts___closed__0_value) as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_instFromJsonModuleArtifacts_fromJson___closed__0_value: LeanStringObject<16> =
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
            77, 111, 100, 117, 108, 101, 65, 114, 116, 105, 102, 97, 99, 116, 115, 0,
        ],
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__0_value)
        as *mut LeanObject;
static l_Lean_instFromJsonModuleArtifacts_fromJson___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instFromJsonImport_fromJson___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
pub static l_Lean_instFromJsonModuleArtifacts_fromJson___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__0_value)
                as *mut LeanObject,
            6040539107507786078 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonModuleArtifacts_fromJson___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__0_value)
                as *mut LeanObject,
            14275066456763359601 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonModuleArtifacts_fromJson___closed__8_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__5_value)
                as *mut LeanObject,
            5047662755307931996 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonModuleArtifacts_fromJson___closed__12_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__7_value)
                as *mut LeanObject,
            3337100315795085641 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonModuleArtifacts_fromJson___closed__16_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__10_value)
                as *mut LeanObject,
            8736330543362429392 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__16_value)
        as *mut LeanObject;
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonModuleArtifacts_fromJson___closed__20_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__13_value)
                as *mut LeanObject,
            9336940269012239943 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__20_value)
        as *mut LeanObject;
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonModuleArtifacts_fromJson___closed__24_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__15_value)
                as *mut LeanObject,
            1258597405849994859 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__24_value)
        as *mut LeanObject;
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonModuleArtifacts_fromJson___closed__28_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__18_value)
                as *mut LeanObject,
            10267131322705678623 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__28_value)
        as *mut LeanObject;
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonModuleArtifacts_fromJson___closed__32_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__21_value)
                as *mut LeanObject,
            2626745227875379750 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__32_value)
        as *mut LeanObject;
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonModuleArtifacts___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instFromJsonModuleArtifacts_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instFromJsonModuleArtifacts___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleArtifacts___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instFromJsonModuleArtifacts: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleArtifacts___closed__0_value) as *mut LeanObject;
pub static l_Lean_instReprPlugin_repr___redArg___closed__0_value: LeanStringObject<5> =
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
        m_data: [112, 97, 116, 104, 0],
    };
static mut l_Lean_instReprPlugin_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPlugin_repr___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_instReprPlugin_repr___redArg___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprPlugin_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprPlugin_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPlugin_repr___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_instReprPlugin_repr___redArg___closed__2_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instReprPlugin_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprPlugin_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPlugin_repr___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_instReprPlugin_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instReprPlugin_repr___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprPlugin_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPlugin_repr___redArg___closed__3_value) as *mut LeanObject;
static mut l_Lean_instReprPlugin_repr___redArg___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprPlugin_repr___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprPlugin_repr___redArg___closed__5_value: LeanStringObject<8> =
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
        m_data: [105, 110, 105, 116, 70, 110, 63, 0],
    };
static mut l_Lean_instReprPlugin_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPlugin_repr___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lean_instReprPlugin_repr___redArg___closed__6_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprPlugin_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprPlugin_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPlugin_repr___redArg___closed__6_value) as *mut LeanObject;
pub static l_Lean_instReprPlugin___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instReprPlugin_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instReprPlugin___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPlugin___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instReprPlugin: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprPlugin___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToJsonPlugin_toJson___closed__0_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [105, 110, 105, 116, 70, 110, 0],
    };
static mut l_Lean_instToJsonPlugin_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonPlugin_toJson___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToJsonPlugin___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instToJsonPlugin_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instToJsonPlugin___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonPlugin___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instToJsonPlugin: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonPlugin___closed__0_value) as *mut LeanObject;
pub static l_Lean_Plugin_instCoeFilePath___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Plugin_ofFilePath as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Plugin_instCoeFilePath___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Plugin_instCoeFilePath___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Plugin_instCoeFilePath: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Plugin_instCoeFilePath___closed__0_value) as *mut LeanObject;
pub static l_Lean_Plugin_fromJson_x3f___closed__0_value: LeanStringObject<26> = LeanStringObject {
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
        101, 120, 112, 101, 99, 116, 101, 100, 32, 115, 116, 114, 105, 110, 103, 32, 111, 114, 32,
        111, 98, 106, 101, 99, 116, 0,
    ],
};
static mut l_Lean_Plugin_fromJson_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Plugin_fromJson_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Plugin_fromJson_x3f___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Plugin_fromJson_x3f___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_Plugin_fromJson_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Plugin_fromJson_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Plugin_instFromJson___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Plugin_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Plugin_instFromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Plugin_instFromJson___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Plugin_instFromJson: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Plugin_instFromJson___closed__0_value) as *mut LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__1_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__1_value) as *mut LeanObject;
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__4_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__4_value) as *mut LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__5_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__1_value) as *mut LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__5_value) as *mut LeanObject;
pub static l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__0_value:
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
    m_data: [91, 93, 0],
};
static mut l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__0_value
) as *mut LeanObject;
pub static l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__1_value:
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
        l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__1_value
) as *mut LeanObject;
pub static l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__2_value:
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
    m_data: [91, 0],
};
static mut l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__2_value
) as *mut LeanObject;
static mut l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__5_value:
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
        l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__2_value
    ) as *mut LeanObject],
};
static mut l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__5_value
) as *mut LeanObject;
pub static l_Lean_instReprModuleSetup_repr___redArg___closed__0_value: LeanStringObject<5> =
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
        m_data: [110, 97, 109, 101, 0],
    };
static mut l_Lean_instReprModuleSetup_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleSetup_repr___redArg___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprModuleSetup_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleSetup_repr___redArg___closed__2_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprModuleSetup_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleSetup_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprImport_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprModuleSetup_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleSetup_repr___redArg___closed__4_value: LeanStringObject<9> =
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
        m_data: [112, 97, 99, 107, 97, 103, 101, 63, 0],
    };
static mut l_Lean_instReprModuleSetup_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleSetup_repr___redArg___closed__5_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprModuleSetup_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleSetup_repr___redArg___closed__6_value: LeanStringObject<9> =
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
        m_data: [105, 109, 112, 111, 114, 116, 115, 63, 0],
    };
static mut l_Lean_instReprModuleSetup_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleSetup_repr___redArg___closed__7_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprModuleSetup_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleSetup_repr___redArg___closed__8_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [105, 109, 112, 111, 114, 116, 65, 114, 116, 115, 0],
    };
static mut l_Lean_instReprModuleSetup_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleSetup_repr___redArg___closed__9_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprModuleSetup_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleSetup_repr___redArg___closed__10_value: LeanStringObject<20> =
    LeanStringObject {
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
            83, 116, 100, 46, 84, 114, 101, 101, 77, 97, 112, 46, 111, 102, 76, 105, 115, 116, 32,
            0,
        ],
    };
static mut l_Lean_instReprModuleSetup_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleSetup_repr___redArg___closed__11_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprModuleSetup_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleSetup_repr___redArg___closed__12_value: LeanStringObject<8> =
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
        m_data: [100, 121, 110, 108, 105, 98, 115, 0],
    };
static mut l_Lean_instReprModuleSetup_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleSetup_repr___redArg___closed__13_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprModuleSetup_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleSetup_repr___redArg___closed__14_value: LeanStringObject<8> =
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
        m_data: [112, 108, 117, 103, 105, 110, 115, 0],
    };
static mut l_Lean_instReprModuleSetup_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleSetup_repr___redArg___closed__15_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprModuleSetup_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleSetup_repr___redArg___closed__16_value: LeanStringObject<8> =
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
        m_data: [111, 112, 116, 105, 111, 110, 115, 0],
    };
static mut l_Lean_instReprModuleSetup_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleSetup_repr___redArg___closed__17_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__16_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprModuleSetup_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_instReprModuleSetup___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instReprModuleSetup_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instReprModuleSetup___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleSetup___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instReprModuleSetup: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprModuleSetup___closed__0_value) as *mut LeanObject;
pub static l_Lean_instInhabitedModuleSetup_default___closed__0_value: LeanCtorObject<8> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 7
                + 8) as u16,
            other: 7,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_ImportArtifacts_oleanParts___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_ImportArtifacts_oleanParts___closed__0_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_instInhabitedModuleSetup_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedModuleSetup_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_instInhabitedModuleSetup_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedModuleSetup_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_instInhabitedModuleSetup: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedModuleSetup_default___closed__0_value)
        as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__0_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 66, 97, 108, 97, 110, 99, 105, 110, 103, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__1_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 76, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__2_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 76, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__5_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 82, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__5_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__6_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 82, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__6_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_instToJsonModuleSetup_toJson___closed__0_value: LeanStringObject<8> =
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
        m_data: [112, 97, 99, 107, 97, 103, 101, 0],
    };
static mut l_Lean_instToJsonModuleSetup_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonModuleSetup_toJson___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToJsonModuleSetup___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instToJsonModuleSetup_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToJsonModuleSetup___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonModuleSetup___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instToJsonModuleSetup: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonModuleSetup___closed__0_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__0_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 76, 101, 97, 110, 79, 112, 116, 105, 111, 110, 86, 97, 108, 117, 101, 32, 116, 121, 112, 101, 0]};
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__0_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__0_value) as *mut LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__1_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__2_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [91, 97, 110, 111, 110, 121, 109, 111, 117, 115, 93, 0]};
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__2_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__4_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 96, 78, 97, 109, 101, 96, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__4_value) as *mut LeanObject;
pub static l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8___closed__0_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 96, 78, 97, 109, 101, 77, 97, 112, 96, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8___closed__0_value) as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_instFromJsonModuleSetup_fromJson___closed__0_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [77, 111, 100, 117, 108, 101, 83, 101, 116, 117, 112, 0],
    };
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleSetup_fromJson___closed__0_value)
        as *mut LeanObject;
static l_Lean_instFromJsonModuleSetup_fromJson___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instFromJsonImport_fromJson___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
pub static l_Lean_instFromJsonModuleSetup_fromJson___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instFromJsonModuleSetup_fromJson___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instFromJsonModuleSetup_fromJson___closed__0_value)
                as *mut LeanObject,
            16071009932002607347 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleSetup_fromJson___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonModuleSetup_fromJson___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__0_value)
                as *mut LeanObject,
            5949480926448383572 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleSetup_fromJson___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonModuleSetup_fromJson___closed__8_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__4_value)
                as *mut LeanObject,
            5086256975611378159 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleSetup_fromJson___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonModuleSetup_fromJson___closed__14_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__6_value)
                as *mut LeanObject,
            1679314653385413017 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleSetup_fromJson___closed__14_value)
        as *mut LeanObject;
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__16: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__17: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonModuleSetup_fromJson___closed__18_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__8_value)
                as *mut LeanObject,
            9460939286319895314 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleSetup_fromJson___closed__18_value)
        as *mut LeanObject;
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__21: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonModuleSetup_fromJson___closed__22_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__12_value)
                as *mut LeanObject,
            14389191456355811029 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleSetup_fromJson___closed__22_value)
        as *mut LeanObject;
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__25: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonModuleSetup_fromJson___closed__26_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__14_value)
                as *mut LeanObject,
            17008504370970977323 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleSetup_fromJson___closed__26_value)
        as *mut LeanObject;
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__27_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__27: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__28_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__28: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__29_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__29: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonModuleSetup_fromJson___closed__30_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprModuleSetup_repr___redArg___closed__16_value)
                as *mut LeanObject,
            676847746840866063 as *mut LeanObject,
        ],
    };
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleSetup_fromJson___closed__30_value)
        as *mut LeanObject;
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__31_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__31: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__32_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__32: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__33_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instFromJsonModuleSetup_fromJson___closed__33: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instFromJsonModuleSetup___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instFromJsonModuleSetup_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instFromJsonModuleSetup___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleSetup___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instFromJsonModuleSetup: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonModuleSetup___closed__0_value) as *mut LeanObject;
pub static l_Lean_ModuleSetup_load___closed__0_value: LeanStringObject<28> = LeanStringObject {
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
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 108, 111, 97, 100, 32, 104, 101, 97, 100,
        101, 114, 32, 102, 114, 111, 109, 32, 0,
    ],
};
static mut l_Lean_ModuleSetup_load___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ModuleSetup_load___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Nat_cast___at___00Lean_instReprImport_repr_spec__0(
    mut v_a_3429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    v___x_3430_ = lean_nat_to_int(v_a_3429_);
    return v___x_3430_;
}
pub unsafe fn _init_l_Lean_instReprImport_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    v___x_3444_ = lean_unsigned_to_nat(10);
    v___x_3445_ = lean_nat_to_int(v___x_3444_);
    return v___x_3445_;
}
pub unsafe fn _init_l_Lean_instReprImport_repr___redArg___closed__12() -> *mut LeanObject {
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    v___x_3452_ = lean_unsigned_to_nat(13);
    v___x_3453_ = lean_nat_to_int(v___x_3452_);
    return v___x_3453_;
}
pub unsafe fn _init_l_Lean_instReprImport_repr___redArg___closed__15() -> *mut LeanObject {
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    v___x_3457_ = lean_unsigned_to_nat(14);
    v___x_3458_ = lean_nat_to_int(v___x_3457_);
    return v___x_3458_;
}
pub unsafe fn _init_l_Lean_instReprImport_repr___redArg___closed__19() -> *mut LeanObject {
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    v___x_3463_ = l_Lean_instReprImport_repr___redArg___closed__0;
    v___x_3464_ = lean_string_length(v___x_3463_);
    return v___x_3464_;
}
pub unsafe fn _init_l_Lean_instReprImport_repr___redArg___closed__20() -> *mut LeanObject {
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    v___x_3465_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__19),
        core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__19_once),
        _init_l_Lean_instReprImport_repr___redArg___closed__19,
    );
    v___x_3466_ = lean_nat_to_int(v___x_3465_);
    return v___x_3466_;
}
pub unsafe fn l_Lean_instReprImport_repr___redArg(
    mut v_x_3471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_module_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_importAll_3473_: u8 = 0;
    let mut v_isExported_3474_: u8 = 0;
    let mut v_isMeta_3475_: u8 = 0;
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: u8 = 0;
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    v_module_3472_ = lean_ctor_get(v_x_3471_, 0);
    lean_inc(v_module_3472_);
    v_importAll_3473_ = lean_ctor_get_uint8(
        v_x_3471_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v_isExported_3474_ = lean_ctor_get_uint8(
        v_x_3471_,
        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
    );
    v_isMeta_3475_ = lean_ctor_get_uint8(
        v_x_3471_,
        (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
    );
    lean_dec_ref(v_x_3471_);
    v___x_3476_ = l_Lean_instReprImport_repr___redArg___closed__5;
    v___x_3477_ = l_Lean_instReprImport_repr___redArg___closed__6;
    v___x_3478_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__7_once),
        _init_l_Lean_instReprImport_repr___redArg___closed__7,
    );
    v___x_3479_ = lean_unsigned_to_nat(0);
    v___x_3480_ = l_Lean_Name_reprPrec(v_module_3472_, v___x_3479_);
    v___x_3481_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3481_, 0, v___x_3478_);
    lean_ctor_set(v___x_3481_, 1, v___x_3480_);
    v___x_3482_ = 0;
    v___x_3483_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3483_, 0, v___x_3481_);
    lean_ctor_set_uint8(
        v___x_3483_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3482_,
    );
    v___x_3484_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3484_, 0, v___x_3477_);
    lean_ctor_set(v___x_3484_, 1, v___x_3483_);
    v___x_3485_ = l_Lean_instReprImport_repr___redArg___closed__9;
    v___x_3486_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3486_, 0, v___x_3484_);
    lean_ctor_set(v___x_3486_, 1, v___x_3485_);
    v___x_3487_ = lean_box(1);
    v___x_3488_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3488_, 0, v___x_3486_);
    lean_ctor_set(v___x_3488_, 1, v___x_3487_);
    v___x_3489_ = l_Lean_instReprImport_repr___redArg___closed__11;
    v___x_3490_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3490_, 0, v___x_3488_);
    lean_ctor_set(v___x_3490_, 1, v___x_3489_);
    v___x_3491_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3491_, 0, v___x_3490_);
    lean_ctor_set(v___x_3491_, 1, v___x_3476_);
    v___x_3492_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__12_once),
        _init_l_Lean_instReprImport_repr___redArg___closed__12,
    );
    v___x_3493_ = l_Bool_repr___redArg(v_importAll_3473_);
    v___x_3494_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3494_, 0, v___x_3492_);
    lean_ctor_set(v___x_3494_, 1, v___x_3493_);
    v___x_3495_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3495_, 0, v___x_3494_);
    lean_ctor_set_uint8(
        v___x_3495_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3482_,
    );
    v___x_3496_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3496_, 0, v___x_3491_);
    lean_ctor_set(v___x_3496_, 1, v___x_3495_);
    v___x_3497_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3497_, 0, v___x_3496_);
    lean_ctor_set(v___x_3497_, 1, v___x_3485_);
    v___x_3498_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3498_, 0, v___x_3497_);
    lean_ctor_set(v___x_3498_, 1, v___x_3487_);
    v___x_3499_ = l_Lean_instReprImport_repr___redArg___closed__14;
    v___x_3500_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3500_, 0, v___x_3498_);
    lean_ctor_set(v___x_3500_, 1, v___x_3499_);
    v___x_3501_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3501_, 0, v___x_3500_);
    lean_ctor_set(v___x_3501_, 1, v___x_3476_);
    v___x_3502_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__15_once),
        _init_l_Lean_instReprImport_repr___redArg___closed__15,
    );
    v___x_3503_ = l_Bool_repr___redArg(v_isExported_3474_);
    v___x_3504_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3504_, 0, v___x_3502_);
    lean_ctor_set(v___x_3504_, 1, v___x_3503_);
    v___x_3505_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3505_, 0, v___x_3504_);
    lean_ctor_set_uint8(
        v___x_3505_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3482_,
    );
    v___x_3506_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3506_, 0, v___x_3501_);
    lean_ctor_set(v___x_3506_, 1, v___x_3505_);
    v___x_3507_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3507_, 0, v___x_3506_);
    lean_ctor_set(v___x_3507_, 1, v___x_3485_);
    v___x_3508_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3508_, 0, v___x_3507_);
    lean_ctor_set(v___x_3508_, 1, v___x_3487_);
    v___x_3509_ = l_Lean_instReprImport_repr___redArg___closed__17;
    v___x_3510_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3510_, 0, v___x_3508_);
    lean_ctor_set(v___x_3510_, 1, v___x_3509_);
    v___x_3511_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3511_, 0, v___x_3510_);
    lean_ctor_set(v___x_3511_, 1, v___x_3476_);
    v___x_3512_ = l_Bool_repr___redArg(v_isMeta_3475_);
    v___x_3513_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3513_, 0, v___x_3478_);
    lean_ctor_set(v___x_3513_, 1, v___x_3512_);
    v___x_3514_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3514_, 0, v___x_3513_);
    lean_ctor_set_uint8(
        v___x_3514_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3482_,
    );
    v___x_3515_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3515_, 0, v___x_3511_);
    lean_ctor_set(v___x_3515_, 1, v___x_3514_);
    v___x_3516_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__20),
        core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__20_once),
        _init_l_Lean_instReprImport_repr___redArg___closed__20,
    );
    v___x_3517_ = l_Lean_instReprImport_repr___redArg___closed__21;
    v___x_3518_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3518_, 0, v___x_3517_);
    lean_ctor_set(v___x_3518_, 1, v___x_3515_);
    v___x_3519_ = l_Lean_instReprImport_repr___redArg___closed__22;
    v___x_3520_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3520_, 0, v___x_3518_);
    lean_ctor_set(v___x_3520_, 1, v___x_3519_);
    v___x_3521_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3521_, 0, v___x_3516_);
    lean_ctor_set(v___x_3521_, 1, v___x_3520_);
    v___x_3522_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3522_, 0, v___x_3521_);
    lean_ctor_set_uint8(
        v___x_3522_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3482_,
    );
    return v___x_3522_;
}
pub unsafe fn l_Lean_instReprImport_repr(
    mut v_x_3523_: *mut LeanObject,
    mut v_prec_3524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    v___x_3525_ = l_Lean_instReprImport_repr___redArg(v_x_3523_);
    return v___x_3525_;
}
pub unsafe fn l_Lean_instReprImport_repr___boxed(
    mut v_x_3526_: *mut LeanObject,
    mut v_prec_3527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3528_: *mut LeanObject = core::ptr::null_mut();
    v_res_3528_ = l_Lean_instReprImport_repr(v_x_3526_, v_prec_3527_);
    lean_dec(v_prec_3527_);
    return v_res_3528_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(
    mut v_a_3537_: *mut LeanObject,
    mut v_a_3538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3537_) == 0 {
                    v___x_3539_ = lean_array_to_list(v_a_3538_);
                    return v___x_3539_;
                } else {
                    v_head_3540_ = lean_ctor_get(v_a_3537_, 0);
                    lean_inc(v_head_3540_);
                    v_tail_3541_ = lean_ctor_get(v_a_3537_, 1);
                    lean_inc(v_tail_3541_);
                    lean_dec_ref_known(v_a_3537_, 2);
                    v___x_3542_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_3538_,
                        v_head_3540_,
                    );
                    v_a_3537_ = v_tail_3541_;
                    v_a_3538_ = v___x_3542_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instToJsonImport_toJson(mut v_x_3546_: *mut LeanObject) -> *mut LeanObject {
    let mut v_module_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_importAll_3548_: u8 = 0;
    let mut v_isExported_3549_: u8 = 0;
    let mut v_isMeta_3550_: u8 = 0;
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: u8 = 0;
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    v_module_3547_ = lean_ctor_get(v_x_3546_, 0);
    lean_inc(v_module_3547_);
    v_importAll_3548_ = lean_ctor_get_uint8(
        v_x_3546_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v_isExported_3549_ = lean_ctor_get_uint8(
        v_x_3546_,
        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
    );
    v_isMeta_3550_ = lean_ctor_get_uint8(
        v_x_3546_,
        (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
    );
    lean_dec_ref(v_x_3546_);
    v___x_3551_ = l_Lean_instReprImport_repr___redArg___closed__1;
    v___x_3552_ = 1;
    v___x_3553_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_module_3547_,
        v___x_3552_,
    );
    v___x_3554_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_3554_, 0, v___x_3553_);
    v___x_3555_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3555_, 0, v___x_3551_);
    lean_ctor_set(v___x_3555_, 1, v___x_3554_);
    v___x_3556_ = lean_box(0);
    v___x_3557_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3557_, 0, v___x_3555_);
    lean_ctor_set(v___x_3557_, 1, v___x_3556_);
    v___x_3558_ = l_Lean_instReprImport_repr___redArg___closed__10;
    v___x_3559_ = lean_alloc_ctor(1, 0, (1) as u32);
    lean_ctor_set_uint8(v___x_3559_, 0 as u32, v_importAll_3548_);
    v___x_3560_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3560_, 0, v___x_3558_);
    lean_ctor_set(v___x_3560_, 1, v___x_3559_);
    v___x_3561_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3561_, 0, v___x_3560_);
    lean_ctor_set(v___x_3561_, 1, v___x_3556_);
    v___x_3562_ = l_Lean_instReprImport_repr___redArg___closed__13;
    v___x_3563_ = lean_alloc_ctor(1, 0, (1) as u32);
    lean_ctor_set_uint8(v___x_3563_, 0 as u32, v_isExported_3549_);
    v___x_3564_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3564_, 0, v___x_3562_);
    lean_ctor_set(v___x_3564_, 1, v___x_3563_);
    v___x_3565_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3565_, 0, v___x_3564_);
    lean_ctor_set(v___x_3565_, 1, v___x_3556_);
    v___x_3566_ = l_Lean_instReprImport_repr___redArg___closed__16;
    v___x_3567_ = lean_alloc_ctor(1, 0, (1) as u32);
    lean_ctor_set_uint8(v___x_3567_, 0 as u32, v_isMeta_3550_);
    v___x_3568_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3568_, 0, v___x_3566_);
    lean_ctor_set(v___x_3568_, 1, v___x_3567_);
    v___x_3569_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3569_, 0, v___x_3568_);
    lean_ctor_set(v___x_3569_, 1, v___x_3556_);
    v___x_3570_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3570_, 0, v___x_3569_);
    lean_ctor_set(v___x_3570_, 1, v___x_3556_);
    v___x_3571_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3571_, 0, v___x_3565_);
    lean_ctor_set(v___x_3571_, 1, v___x_3570_);
    v___x_3572_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3572_, 0, v___x_3561_);
    lean_ctor_set(v___x_3572_, 1, v___x_3571_);
    v___x_3573_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3573_, 0, v___x_3557_);
    lean_ctor_set(v___x_3573_, 1, v___x_3572_);
    v___x_3574_ = l_Lean_instToJsonImport_toJson___closed__0;
    v___x_3575_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(v___x_3573_, v___x_3574_);
    v___x_3576_ = l_Lean_Json_mkObj(v___x_3575_);
    lean_dec(v___x_3575_);
    return v___x_3576_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__0(
    mut v_j_3579_: *mut LeanObject,
    mut v_k_3580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    v___x_3581_ = l_Lean_Json_getObjValD(v_j_3579_, v_k_3580_);
    v___x_3582_ = l_Lean_Name_fromJson_x3f(v___x_3581_);
    return v___x_3582_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__0___boxed(
    mut v_j_3583_: *mut LeanObject,
    mut v_k_3584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3585_: *mut LeanObject = core::ptr::null_mut();
    v_res_3585_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__0(
        v_j_3583_, v_k_3584_,
    );
    lean_dec_ref(v_k_3584_);
    return v_res_3585_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(
    mut v_j_3586_: *mut LeanObject,
    mut v_k_3587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    v___x_3588_ = l_Lean_Json_getObjValD(v_j_3586_, v_k_3587_);
    v___x_3589_ = l_Lean_Json_getBool_x3f(v___x_3588_);
    lean_dec(v___x_3588_);
    return v___x_3589_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1___boxed(
    mut v_j_3590_: *mut LeanObject,
    mut v_k_3591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3592_: *mut LeanObject = core::ptr::null_mut();
    v_res_3592_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(
        v_j_3590_, v_k_3591_,
    );
    lean_dec_ref(v_k_3591_);
    return v_res_3592_;
}
pub unsafe fn _init_l_Lean_instFromJsonImport_fromJson___closed__3() -> *mut LeanObject {
    let mut v___x_3598_: u8 = 0;
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    v___x_3598_ = 1;
    v___x_3599_ = l_Lean_instFromJsonImport_fromJson___closed__2;
    v___x_3600_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3599_, v___x_3598_);
    return v___x_3600_;
}
pub unsafe fn _init_l_Lean_instFromJsonImport_fromJson___closed__5() -> *mut LeanObject {
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    v___x_3602_ = l_Lean_instFromJsonImport_fromJson___closed__4;
    v___x_3603_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__3_once),
        _init_l_Lean_instFromJsonImport_fromJson___closed__3,
    );
    v___x_3604_ = lean_string_append(v___x_3603_, v___x_3602_);
    return v___x_3604_;
}
pub unsafe fn _init_l_Lean_instFromJsonImport_fromJson___closed__7() -> *mut LeanObject {
    let mut v___x_3607_: u8 = 0;
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    v___x_3607_ = 1;
    v___x_3608_ = l_Lean_instFromJsonImport_fromJson___closed__6;
    v___x_3609_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3608_, v___x_3607_);
    return v___x_3609_;
}
pub unsafe fn _init_l_Lean_instFromJsonImport_fromJson___closed__8() -> *mut LeanObject {
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    v___x_3610_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__7),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__7_once),
        _init_l_Lean_instFromJsonImport_fromJson___closed__7,
    );
    v___x_3611_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__5),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__5_once),
        _init_l_Lean_instFromJsonImport_fromJson___closed__5,
    );
    v___x_3612_ = lean_string_append(v___x_3611_, v___x_3610_);
    return v___x_3612_;
}
pub unsafe fn _init_l_Lean_instFromJsonImport_fromJson___closed__10() -> *mut LeanObject {
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    v___x_3614_ = l_Lean_instFromJsonImport_fromJson___closed__9;
    v___x_3615_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__8_once),
        _init_l_Lean_instFromJsonImport_fromJson___closed__8,
    );
    v___x_3616_ = lean_string_append(v___x_3615_, v___x_3614_);
    return v___x_3616_;
}
pub unsafe fn _init_l_Lean_instFromJsonImport_fromJson___closed__12() -> *mut LeanObject {
    let mut v___x_3619_: u8 = 0;
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    v___x_3619_ = 1;
    v___x_3620_ = l_Lean_instFromJsonImport_fromJson___closed__11;
    v___x_3621_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3620_, v___x_3619_);
    return v___x_3621_;
}
pub unsafe fn _init_l_Lean_instFromJsonImport_fromJson___closed__13() -> *mut LeanObject {
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    v___x_3622_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__12),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__12_once),
        _init_l_Lean_instFromJsonImport_fromJson___closed__12,
    );
    v___x_3623_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__5),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__5_once),
        _init_l_Lean_instFromJsonImport_fromJson___closed__5,
    );
    v___x_3624_ = lean_string_append(v___x_3623_, v___x_3622_);
    return v___x_3624_;
}
pub unsafe fn _init_l_Lean_instFromJsonImport_fromJson___closed__14() -> *mut LeanObject {
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    v___x_3625_ = l_Lean_instFromJsonImport_fromJson___closed__9;
    v___x_3626_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__13),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__13_once),
        _init_l_Lean_instFromJsonImport_fromJson___closed__13,
    );
    v___x_3627_ = lean_string_append(v___x_3626_, v___x_3625_);
    return v___x_3627_;
}
pub unsafe fn _init_l_Lean_instFromJsonImport_fromJson___closed__16() -> *mut LeanObject {
    let mut v___x_3630_: u8 = 0;
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    v___x_3630_ = 1;
    v___x_3631_ = l_Lean_instFromJsonImport_fromJson___closed__15;
    v___x_3632_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3631_, v___x_3630_);
    return v___x_3632_;
}
pub unsafe fn _init_l_Lean_instFromJsonImport_fromJson___closed__17() -> *mut LeanObject {
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    v___x_3633_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__16),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__16_once),
        _init_l_Lean_instFromJsonImport_fromJson___closed__16,
    );
    v___x_3634_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__5),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__5_once),
        _init_l_Lean_instFromJsonImport_fromJson___closed__5,
    );
    v___x_3635_ = lean_string_append(v___x_3634_, v___x_3633_);
    return v___x_3635_;
}
pub unsafe fn _init_l_Lean_instFromJsonImport_fromJson___closed__18() -> *mut LeanObject {
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    v___x_3636_ = l_Lean_instFromJsonImport_fromJson___closed__9;
    v___x_3637_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__17),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__17_once),
        _init_l_Lean_instFromJsonImport_fromJson___closed__17,
    );
    v___x_3638_ = lean_string_append(v___x_3637_, v___x_3636_);
    return v___x_3638_;
}
pub unsafe fn _init_l_Lean_instFromJsonImport_fromJson___closed__20() -> *mut LeanObject {
    let mut v___x_3641_: u8 = 0;
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    v___x_3641_ = 1;
    v___x_3642_ = l_Lean_instFromJsonImport_fromJson___closed__19;
    v___x_3643_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3642_, v___x_3641_);
    return v___x_3643_;
}
pub unsafe fn _init_l_Lean_instFromJsonImport_fromJson___closed__21() -> *mut LeanObject {
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    v___x_3644_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__20),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__20_once),
        _init_l_Lean_instFromJsonImport_fromJson___closed__20,
    );
    v___x_3645_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__5),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__5_once),
        _init_l_Lean_instFromJsonImport_fromJson___closed__5,
    );
    v___x_3646_ = lean_string_append(v___x_3645_, v___x_3644_);
    return v___x_3646_;
}
pub unsafe fn _init_l_Lean_instFromJsonImport_fromJson___closed__22() -> *mut LeanObject {
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    v___x_3647_ = l_Lean_instFromJsonImport_fromJson___closed__9;
    v___x_3648_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__21),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__21_once),
        _init_l_Lean_instFromJsonImport_fromJson___closed__21,
    );
    v___x_3649_ = lean_string_append(v___x_3648_, v___x_3647_);
    return v___x_3649_;
}
pub unsafe fn l_Lean_instFromJsonImport_fromJson(
    mut v_json_3650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3656_: u8 = 0;
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3662_: u8 = 0;
    let mut v_a_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3666_: u8 = 0;
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3670_: u8 = 0;
    let mut v_a_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3677_: u8 = 0;
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3683_: u8 = 0;
    let mut v_a_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3687_: u8 = 0;
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3691_: u8 = 0;
    let mut v_a_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3698_: u8 = 0;
    let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3704_: u8 = 0;
    let mut v_a_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3708_: u8 = 0;
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3712_: u8 = 0;
    let mut v_a_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3719_: u8 = 0;
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3725_: u8 = 0;
    let mut v_a_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3729_: u8 = 0;
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3733_: u8 = 0;
    let mut v_a_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3737_: u8 = 0;
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: u8 = 0;
    let mut v___x_3740_: u8 = 0;
    let mut v___x_3741_: u8 = 0;
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3745_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3651_ = l_Lean_instReprImport_repr___redArg___closed__1;
                lean_inc(v_json_3650_);
                v___x_3652_ =
                    l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__0(
                        v_json_3650_,
                        v___x_3651_,
                    );
                if lean_obj_tag(v___x_3652_) == 0 {
                    lean_dec(v_json_3650_);
                    v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
                    v_isSharedCheck_3662_ = (!lean_is_exclusive(v___x_3652_)) as u8;
                    if v_isSharedCheck_3662_ == 0 {
                        v___x_3655_ = v___x_3652_;
                        v_isShared_3656_ = v_isSharedCheck_3662_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3653_);
                        lean_dec(v___x_3652_);
                        v___x_3655_ = lean_box(0);
                        v_isShared_3656_ = v_isSharedCheck_3662_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_3652_) == 0 {
                        lean_dec(v_json_3650_);
                        v_a_3663_ = lean_ctor_get(v___x_3652_, 0);
                        v_isSharedCheck_3670_ = (!lean_is_exclusive(v___x_3652_)) as u8;
                        if v_isSharedCheck_3670_ == 0 {
                            v___x_3665_ = v___x_3652_;
                            v_isShared_3666_ = v_isSharedCheck_3670_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3663_);
                            lean_dec(v___x_3652_);
                            v___x_3665_ = lean_box(0);
                            v_isShared_3666_ = v_isSharedCheck_3670_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3671_ = lean_ctor_get(v___x_3652_, 0);
                        lean_inc(v_a_3671_);
                        lean_dec_ref_known(v___x_3652_, 1);
                        v___x_3672_ = l_Lean_instReprImport_repr___redArg___closed__10;
                        lean_inc(v_json_3650_);
                        v___x_3673_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(v_json_3650_, v___x_3672_);
                        if lean_obj_tag(v___x_3673_) == 0 {
                            lean_dec(v_a_3671_);
                            lean_dec(v_json_3650_);
                            v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
                            v_isSharedCheck_3683_ = (!lean_is_exclusive(v___x_3673_)) as u8;
                            if v_isSharedCheck_3683_ == 0 {
                                v___x_3676_ = v___x_3673_;
                                v_isShared_3677_ = v_isSharedCheck_3683_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_3674_);
                                lean_dec(v___x_3673_);
                                v___x_3676_ = lean_box(0);
                                v_isShared_3677_ = v_isSharedCheck_3683_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_3673_) == 0 {
                                lean_dec(v_a_3671_);
                                lean_dec(v_json_3650_);
                                v_a_3684_ = lean_ctor_get(v___x_3673_, 0);
                                v_isSharedCheck_3691_ = (!lean_is_exclusive(v___x_3673_)) as u8;
                                if v_isSharedCheck_3691_ == 0 {
                                    v___x_3686_ = v___x_3673_;
                                    v_isShared_3687_ = v_isSharedCheck_3691_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_3684_);
                                    lean_dec(v___x_3673_);
                                    v___x_3686_ = lean_box(0);
                                    v_isShared_3687_ = v_isSharedCheck_3691_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_3692_ = lean_ctor_get(v___x_3673_, 0);
                                lean_inc(v_a_3692_);
                                lean_dec_ref_known(v___x_3673_, 1);
                                v___x_3693_ = l_Lean_instReprImport_repr___redArg___closed__13;
                                lean_inc(v_json_3650_);
                                v___x_3694_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(v_json_3650_, v___x_3693_);
                                if lean_obj_tag(v___x_3694_) == 0 {
                                    lean_dec(v_a_3692_);
                                    lean_dec(v_a_3671_);
                                    lean_dec(v_json_3650_);
                                    v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
                                    v_isSharedCheck_3704_ = (!lean_is_exclusive(v___x_3694_)) as u8;
                                    if v_isSharedCheck_3704_ == 0 {
                                        v___x_3697_ = v___x_3694_;
                                        v_isShared_3698_ = v_isSharedCheck_3704_;
                                        state = 9;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3695_);
                                        lean_dec(v___x_3694_);
                                        v___x_3697_ = lean_box(0);
                                        v_isShared_3698_ = v_isSharedCheck_3704_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if lean_obj_tag(v___x_3694_) == 0 {
                                        lean_dec(v_a_3692_);
                                        lean_dec(v_a_3671_);
                                        lean_dec(v_json_3650_);
                                        v_a_3705_ = lean_ctor_get(v___x_3694_, 0);
                                        v_isSharedCheck_3712_ =
                                            (!lean_is_exclusive(v___x_3694_)) as u8;
                                        if v_isSharedCheck_3712_ == 0 {
                                            v___x_3707_ = v___x_3694_;
                                            v_isShared_3708_ = v_isSharedCheck_3712_;
                                            state = 11;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3705_);
                                            lean_dec(v___x_3694_);
                                            v___x_3707_ = lean_box(0);
                                            v_isShared_3708_ = v_isSharedCheck_3712_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_3713_ = lean_ctor_get(v___x_3694_, 0);
                                        lean_inc(v_a_3713_);
                                        lean_dec_ref_known(v___x_3694_, 1);
                                        v___x_3714_ =
                                            l_Lean_instReprImport_repr___redArg___closed__16;
                                        v___x_3715_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(v_json_3650_, v___x_3714_);
                                        if lean_obj_tag(v___x_3715_) == 0 {
                                            lean_dec(v_a_3713_);
                                            lean_dec(v_a_3692_);
                                            lean_dec(v_a_3671_);
                                            v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
                                            v_isSharedCheck_3725_ =
                                                (!lean_is_exclusive(v___x_3715_)) as u8;
                                            if v_isSharedCheck_3725_ == 0 {
                                                v___x_3718_ = v___x_3715_;
                                                v_isShared_3719_ = v_isSharedCheck_3725_;
                                                state = 13;
                                                continue;
                                            } else {
                                                lean_inc(v_a_3716_);
                                                lean_dec(v___x_3715_);
                                                v___x_3718_ = lean_box(0);
                                                v_isShared_3719_ = v_isSharedCheck_3725_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            if lean_obj_tag(v___x_3715_) == 0 {
                                                lean_dec(v_a_3713_);
                                                lean_dec(v_a_3692_);
                                                lean_dec(v_a_3671_);
                                                v_a_3726_ = lean_ctor_get(v___x_3715_, 0);
                                                v_isSharedCheck_3733_ =
                                                    (!lean_is_exclusive(v___x_3715_)) as u8;
                                                if v_isSharedCheck_3733_ == 0 {
                                                    v___x_3728_ = v___x_3715_;
                                                    v_isShared_3729_ = v_isSharedCheck_3733_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_3726_);
                                                    lean_dec(v___x_3715_);
                                                    v___x_3728_ = lean_box(0);
                                                    v_isShared_3729_ = v_isSharedCheck_3733_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_3734_ = lean_ctor_get(v___x_3715_, 0);
                                                v_isSharedCheck_3745_ =
                                                    (!lean_is_exclusive(v___x_3715_)) as u8;
                                                if v_isSharedCheck_3745_ == 0 {
                                                    v___x_3736_ = v___x_3715_;
                                                    v_isShared_3737_ = v_isSharedCheck_3745_;
                                                    state = 17;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_3734_);
                                                    lean_dec(v___x_3715_);
                                                    v___x_3736_ = lean_box(0);
                                                    v_isShared_3737_ = v_isSharedCheck_3745_;
                                                    state = 17;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3657_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__10),
                    core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__10_once),
                    _init_l_Lean_instFromJsonImport_fromJson___closed__10,
                );
                v___x_3658_ = lean_string_append(v___x_3657_, v_a_3653_);
                lean_dec(v_a_3653_);
                if v_isShared_3656_ == 0 {
                    lean_ctor_set(v___x_3655_, 0, v___x_3658_);
                    v___x_3660_ = v___x_3655_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3658_);
                    v___x_3660_ = v_reuseFailAlloc_3661_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3660_;
            }
            3 => {
                if v_isShared_3666_ == 0 {
                    lean_ctor_set_tag(v___x_3665_, 0);
                    v___x_3668_ = v___x_3665_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
                    v___x_3668_ = v_reuseFailAlloc_3669_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3668_;
            }
            5 => {
                v___x_3678_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__14),
                    core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__14_once),
                    _init_l_Lean_instFromJsonImport_fromJson___closed__14,
                );
                v___x_3679_ = lean_string_append(v___x_3678_, v_a_3674_);
                lean_dec(v_a_3674_);
                if v_isShared_3677_ == 0 {
                    lean_ctor_set(v___x_3676_, 0, v___x_3679_);
                    v___x_3681_ = v___x_3676_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3682_, 0, v___x_3679_);
                    v___x_3681_ = v_reuseFailAlloc_3682_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3681_;
            }
            7 => {
                if v_isShared_3687_ == 0 {
                    lean_ctor_set_tag(v___x_3686_, 0);
                    v___x_3689_ = v___x_3686_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3684_);
                    v___x_3689_ = v_reuseFailAlloc_3690_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3689_;
            }
            9 => {
                v___x_3699_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__18),
                    core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__18_once),
                    _init_l_Lean_instFromJsonImport_fromJson___closed__18,
                );
                v___x_3700_ = lean_string_append(v___x_3699_, v_a_3695_);
                lean_dec(v_a_3695_);
                if v_isShared_3698_ == 0 {
                    lean_ctor_set(v___x_3697_, 0, v___x_3700_);
                    v___x_3702_ = v___x_3697_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3703_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3700_);
                    v___x_3702_ = v_reuseFailAlloc_3703_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3702_;
            }
            11 => {
                if v_isShared_3708_ == 0 {
                    lean_ctor_set_tag(v___x_3707_, 0);
                    v___x_3710_ = v___x_3707_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_a_3705_);
                    v___x_3710_ = v_reuseFailAlloc_3711_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3710_;
            }
            13 => {
                v___x_3720_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__22),
                    core::ptr::addr_of_mut!(l_Lean_instFromJsonImport_fromJson___closed__22_once),
                    _init_l_Lean_instFromJsonImport_fromJson___closed__22,
                );
                v___x_3721_ = lean_string_append(v___x_3720_, v_a_3716_);
                lean_dec(v_a_3716_);
                if v_isShared_3719_ == 0 {
                    lean_ctor_set(v___x_3718_, 0, v___x_3721_);
                    v___x_3723_ = v___x_3718_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3721_);
                    v___x_3723_ = v_reuseFailAlloc_3724_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3723_;
            }
            15 => {
                if v_isShared_3729_ == 0 {
                    lean_ctor_set_tag(v___x_3728_, 0);
                    v___x_3731_ = v___x_3728_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_a_3726_);
                    v___x_3731_ = v_reuseFailAlloc_3732_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3731_;
            }
            17 => {
                v___x_3738_ = lean_alloc_ctor(0, 1, (3) as u32);
                lean_ctor_set(v___x_3738_, 0, v_a_3671_);
                v___x_3739_ = (lean_unbox(v_a_3692_) as u8);
                lean_dec(v_a_3692_);
                lean_ctor_set_uint8(
                    v___x_3738_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3739_,
                );
                v___x_3740_ = (lean_unbox(v_a_3713_) as u8);
                lean_dec(v_a_3713_);
                lean_ctor_set_uint8(
                    v___x_3738_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v___x_3740_,
                );
                v___x_3741_ = (lean_unbox(v_a_3734_) as u8);
                lean_dec(v_a_3734_);
                lean_ctor_set_uint8(
                    v___x_3738_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                    v___x_3741_,
                );
                if v_isShared_3737_ == 0 {
                    lean_ctor_set(v___x_3736_, 0, v___x_3738_);
                    v___x_3743_ = v___x_3736_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3744_, 0, v___x_3738_);
                    v___x_3743_ = v_reuseFailAlloc_3744_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3743_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instBEqImport_beq(
    mut v_x_3748_: *mut LeanObject,
    mut v_x_3749_: *mut LeanObject,
) -> u8 {
    let mut v_module_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_importAll_3751_: u8 = 0;
    let mut v_isExported_3752_: u8 = 0;
    let mut v_isMeta_3753_: u8 = 0;
    let mut v_module_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_importAll_3755_: u8 = 0;
    let mut v_isExported_3756_: u8 = 0;
    let mut v_isMeta_3757_: u8 = 0;
    let mut v___y_3759_: u8 = 0;
    let mut v___y_3761_: u8 = 0;
    let mut v___x_3762_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_module_3750_ = lean_ctor_get(v_x_3748_, 0);
                v_importAll_3751_ = lean_ctor_get_uint8(
                    v_x_3748_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isExported_3752_ = lean_ctor_get_uint8(
                    v_x_3748_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v_isMeta_3753_ = lean_ctor_get_uint8(
                    v_x_3748_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                v_module_3754_ = lean_ctor_get(v_x_3749_, 0);
                v_importAll_3755_ = lean_ctor_get_uint8(
                    v_x_3749_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isExported_3756_ = lean_ctor_get_uint8(
                    v_x_3749_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v_isMeta_3757_ = lean_ctor_get_uint8(
                    v_x_3749_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                v___x_3762_ = lean_name_eq(v_module_3750_, v_module_3754_);
                if v___x_3762_ == 0 {
                    return v___x_3762_;
                } else {
                    if v_importAll_3751_ == 0 {
                        if v_importAll_3755_ == 0 {
                            v___y_3761_ = v___x_3762_;
                            state = 2;
                            continue;
                        } else {
                            return v_importAll_3751_;
                        }
                    } else {
                        v___y_3761_ = v_importAll_3755_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                if v_isMeta_3753_ == 0 {
                    if v_isMeta_3757_ == 0 {
                        return v___y_3759_;
                    } else {
                        return v_isMeta_3753_;
                    }
                } else {
                    return v_isMeta_3757_;
                }
            }
            2 => {
                if v___y_3761_ == 0 {
                    return v___y_3761_;
                } else {
                    if v_isExported_3752_ == 0 {
                        if v_isExported_3756_ == 0 {
                            v___y_3759_ = v___y_3761_;
                            state = 1;
                            continue;
                        } else {
                            return v_isExported_3752_;
                        }
                    } else {
                        if v_isExported_3756_ == 0 {
                            return v_isExported_3756_;
                        } else {
                            v___y_3759_ = v_isExported_3756_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instBEqImport_beq___boxed(
    mut v_x_3763_: *mut LeanObject,
    mut v_x_3764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3765_: u8 = 0;
    let mut v_r_3766_: *mut LeanObject = core::ptr::null_mut();
    v_res_3765_ = l_Lean_instBEqImport_beq(v_x_3763_, v_x_3764_);
    lean_dec_ref(v_x_3764_);
    lean_dec_ref(v_x_3763_);
    v_r_3766_ = lean_box((v_res_3765_) as usize);
    return v_r_3766_;
}
pub unsafe fn _init_l_Lean_instHashableImport_hash___closed__0() -> u64 {
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: u64 = 0;
    v___x_3769_ = lean_unsigned_to_nat(1723);
    v___x_3770_ = lean_uint64_of_nat(v___x_3769_);
    return v___x_3770_;
}
pub unsafe fn l_Lean_instHashableImport_hash(mut v_x_3771_: *mut LeanObject) -> u64 {
    let mut v_module_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_importAll_3773_: u8 = 0;
    let mut v_isExported_3774_: u8 = 0;
    let mut v_isMeta_3775_: u8 = 0;
    let mut v___y_3777_: u64 = 0;
    let mut v___y_3778_: u64 = 0;
    let mut v___x_3779_: u64 = 0;
    let mut v___x_3780_: u64 = 0;
    let mut v___x_3781_: u64 = 0;
    let mut v___x_3782_: u64 = 0;
    let mut v___x_3783_: u64 = 0;
    let mut v___y_3785_: u64 = 0;
    let mut v___y_3786_: u64 = 0;
    let mut v___x_3787_: u64 = 0;
    let mut v___x_3788_: u64 = 0;
    let mut v___x_3789_: u64 = 0;
    let mut v___x_3790_: u64 = 0;
    let mut v___y_3792_: u64 = 0;
    let mut v___x_3793_: u64 = 0;
    let mut v___x_3794_: u64 = 0;
    let mut v___x_3795_: u64 = 0;
    let mut v___x_3796_: u64 = 0;
    let mut v_hash_3797_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_module_3772_ = lean_ctor_get(v_x_3771_, 0);
                v_importAll_3773_ = lean_ctor_get_uint8(
                    v_x_3771_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isExported_3774_ = lean_ctor_get_uint8(
                    v_x_3771_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v_isMeta_3775_ = lean_ctor_get_uint8(
                    v_x_3771_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                v___x_3790_ = 0u64;
                if lean_obj_tag(v_module_3772_) == 0 {
                    v___x_3796_ = lean_uint64_once(
                        core::ptr::addr_of_mut!(l_Lean_instHashableImport_hash___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_instHashableImport_hash___closed__0_once),
                        _init_l_Lean_instHashableImport_hash___closed__0,
                    );
                    v___y_3792_ = v___x_3796_;
                    state = 3;
                    continue;
                } else {
                    v_hash_3797_ = lean_ctor_get_uint64(
                        v_module_3772_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3792_ = v_hash_3797_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_3779_ = lean_uint64_mix_hash(v___y_3777_, v___y_3778_);
                if v_isMeta_3775_ == 0 {
                    v___x_3780_ = 13u64;
                    v___x_3781_ = lean_uint64_mix_hash(v___x_3779_, v___x_3780_);
                    return v___x_3781_;
                } else {
                    v___x_3782_ = 11u64;
                    v___x_3783_ = lean_uint64_mix_hash(v___x_3779_, v___x_3782_);
                    return v___x_3783_;
                }
            }
            2 => {
                v___x_3787_ = lean_uint64_mix_hash(v___y_3785_, v___y_3786_);
                if v_isExported_3774_ == 0 {
                    v___x_3788_ = 13u64;
                    v___y_3777_ = v___x_3787_;
                    v___y_3778_ = v___x_3788_;
                    state = 1;
                    continue;
                } else {
                    v___x_3789_ = 11u64;
                    v___y_3777_ = v___x_3787_;
                    v___y_3778_ = v___x_3789_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3793_ = lean_uint64_mix_hash(v___x_3790_, v___y_3792_);
                if v_importAll_3773_ == 0 {
                    v___x_3794_ = 13u64;
                    v___y_3785_ = v___x_3793_;
                    v___y_3786_ = v___x_3794_;
                    state = 2;
                    continue;
                } else {
                    v___x_3795_ = 11u64;
                    v___y_3785_ = v___x_3793_;
                    v___y_3786_ = v___x_3795_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instHashableImport_hash___boxed(
    mut v_x_3798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3799_: u64 = 0;
    let mut v_r_3800_: *mut LeanObject = core::ptr::null_mut();
    v_res_3799_ = l_Lean_instHashableImport_hash(v_x_3798_);
    lean_dec_ref(v_x_3798_);
    v_r_3800_ = lean_box_uint64(v_res_3799_);
    return v_r_3800_;
}
pub unsafe fn l_Lean_Idbg_idbgClientLoop___boxed(
    mut v_00_u03b1_3809_: *mut LeanObject,
    mut v_inst_00___x40_Lean_Setup_1068012781____hygCtx___hyg_3810_: *mut LeanObject,
    mut v_siteId_3811_: *mut LeanObject,
    mut v_imports_3812_: *mut LeanObject,
    mut v_apply_3813_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_3814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3815_: *mut LeanObject = core::ptr::null_mut();
    v_res_3815_ = lean_idbg_client_loop(v_siteId_3811_, v_imports_3812_, v_apply_3813_);
    return v_res_3815_;
}
pub unsafe fn l_Lean_instCoeNameImport___lam__0(mut v_x_3816_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3817_: u8 = 0;
    let mut v___x_3818_: u8 = 0;
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    v___x_3817_ = 0;
    v___x_3818_ = 1;
    v___x_3819_ = lean_alloc_ctor(0, 1, (3) as u32);
    lean_ctor_set(v___x_3819_, 0, v_x_3816_);
    lean_ctor_set_uint8(
        v___x_3819_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3817_,
    );
    lean_ctor_set_uint8(
        v___x_3819_,
        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
        v___x_3818_,
    );
    lean_ctor_set_uint8(
        v___x_3819_,
        (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
        v___x_3817_,
    );
    return v___x_3819_;
}
pub unsafe fn l_Lean_instToStringImport___lam__0(
    mut v_imp_3827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_module_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_importAll_3829_: u8 = 0;
    let mut v_isExported_3830_: u8 = 0;
    let mut v_isMeta_3831_: u8 = 0;
    let mut v___y_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: u8 = 0;
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_module_3828_ = lean_ctor_get(v_imp_3827_, 0);
                lean_inc(v_module_3828_);
                v_importAll_3829_ = lean_ctor_get_uint8(
                    v_imp_3827_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isExported_3830_ = lean_ctor_get_uint8(
                    v_imp_3827_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v_isMeta_3831_ = lean_ctor_get_uint8(
                    v_imp_3827_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                lean_dec_ref(v_imp_3827_);
                if v_isExported_3830_ == 0 {
                    v___x_3851_ = l_Lean_instToStringImport___lam__0___closed__1;
                    v___y_3848_ = v___x_3851_;
                    state = 3;
                    continue;
                } else {
                    v___x_3852_ = l_Lean_instToStringImport___lam__0___closed__4;
                    v___y_3848_ = v___x_3852_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_3835_ = lean_string_append(v___y_3833_, v___y_3834_);
                v___x_3836_ = 1;
                v___x_3837_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_module_3828_,
                    v___x_3836_,
                );
                v___x_3838_ = lean_string_append(v___x_3835_, v___x_3837_);
                lean_dec_ref(v___x_3837_);
                return v___x_3838_;
            }
            2 => {
                lean_inc_ref(v___y_3840_);
                v___x_3842_ = lean_string_append(v___y_3840_, v___y_3841_);
                v___x_3843_ = l_Lean_instToStringImport___lam__0___closed__0;
                v___x_3844_ = lean_string_append(v___x_3842_, v___x_3843_);
                if v_importAll_3829_ == 0 {
                    v___x_3845_ = l_Lean_instToStringImport___lam__0___closed__1;
                    v___y_3833_ = v___x_3844_;
                    v___y_3834_ = v___x_3845_;
                    state = 1;
                    continue;
                } else {
                    v___x_3846_ = l_Lean_instToStringImport___lam__0___closed__2;
                    v___y_3833_ = v___x_3844_;
                    v___y_3834_ = v___x_3846_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isMeta_3831_ == 0 {
                    v___x_3849_ = l_Lean_instToStringImport___lam__0___closed__1;
                    v___y_3840_ = v___y_3848_;
                    v___y_3841_ = v___x_3849_;
                    state = 2;
                    continue;
                } else {
                    v___x_3850_ = l_Lean_instToStringImport___lam__0___closed__3;
                    v___y_3840_ = v___y_3848_;
                    v___y_3841_ = v___x_3850_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IRPhases_ctorIdx(mut v_x_3855_: u8) -> *mut LeanObject {
    match v_x_3855_ {
        0 => {
            let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
            v___x_3856_ = lean_unsigned_to_nat(0);
            return v___x_3856_;
        }
        1 => {
            let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
            v___x_3857_ = lean_unsigned_to_nat(1);
            return v___x_3857_;
        }
        _ => {
            let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
            v___x_3858_ = lean_unsigned_to_nat(2);
            return v___x_3858_;
        }
    }
}
pub unsafe fn l_Lean_IRPhases_ctorIdx___boxed(mut v_x_3859_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_3860_: u8 = 0;
    let mut v_res_3861_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_3860_ = (lean_unbox(v_x_3859_) as u8);
    v_res_3861_ = l_Lean_IRPhases_ctorIdx(v_x_boxed_3860_);
    return v_res_3861_;
}
pub unsafe fn l_Lean_IRPhases_toCtorIdx(mut v_x_3862_: u8) -> *mut LeanObject {
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    v___x_3863_ = l_Lean_IRPhases_ctorIdx(v_x_3862_);
    return v___x_3863_;
}
pub unsafe fn l_Lean_IRPhases_toCtorIdx___boxed(mut v_x_3864_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_4__boxed_3865_: u8 = 0;
    let mut v_res_3866_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_3865_ = (lean_unbox(v_x_3864_) as u8);
    v_res_3866_ = l_Lean_IRPhases_toCtorIdx(v_x_4__boxed_3865_);
    return v_res_3866_;
}
pub unsafe fn l_Lean_IRPhases_ctorElim___redArg(mut v_k_3867_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_k_3867_);
    return v_k_3867_;
}
pub unsafe fn l_Lean_IRPhases_ctorElim___redArg___boxed(
    mut v_k_3868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3869_: *mut LeanObject = core::ptr::null_mut();
    v_res_3869_ = l_Lean_IRPhases_ctorElim___redArg(v_k_3868_);
    lean_dec(v_k_3868_);
    return v_res_3869_;
}
pub unsafe fn l_Lean_IRPhases_ctorElim(
    mut v_motive_3870_: *mut LeanObject,
    mut v_ctorIdx_3871_: *mut LeanObject,
    mut v_t_3872_: u8,
    mut v_h_3873_: *mut LeanObject,
    mut v_k_3874_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_3874_);
    return v_k_3874_;
}
pub unsafe fn l_Lean_IRPhases_ctorElim___boxed(
    mut v_motive_3875_: *mut LeanObject,
    mut v_ctorIdx_3876_: *mut LeanObject,
    mut v_t_3877_: *mut LeanObject,
    mut v_h_3878_: *mut LeanObject,
    mut v_k_3879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_3880_: u8 = 0;
    let mut v_res_3881_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_3880_ = (lean_unbox(v_t_3877_) as u8);
    v_res_3881_ = l_Lean_IRPhases_ctorElim(
        v_motive_3875_,
        v_ctorIdx_3876_,
        v_t_boxed_3880_,
        v_h_3878_,
        v_k_3879_,
    );
    lean_dec(v_k_3879_);
    lean_dec(v_ctorIdx_3876_);
    return v_res_3881_;
}
pub unsafe fn l_Lean_IRPhases_runtime_elim___redArg(
    mut v_runtime_3882_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_runtime_3882_);
    return v_runtime_3882_;
}
pub unsafe fn l_Lean_IRPhases_runtime_elim___redArg___boxed(
    mut v_runtime_3883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3884_: *mut LeanObject = core::ptr::null_mut();
    v_res_3884_ = l_Lean_IRPhases_runtime_elim___redArg(v_runtime_3883_);
    lean_dec(v_runtime_3883_);
    return v_res_3884_;
}
pub unsafe fn l_Lean_IRPhases_runtime_elim(
    mut v_motive_3885_: *mut LeanObject,
    mut v_t_3886_: u8,
    mut v_h_3887_: *mut LeanObject,
    mut v_runtime_3888_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_runtime_3888_);
    return v_runtime_3888_;
}
pub unsafe fn l_Lean_IRPhases_runtime_elim___boxed(
    mut v_motive_3889_: *mut LeanObject,
    mut v_t_3890_: *mut LeanObject,
    mut v_h_3891_: *mut LeanObject,
    mut v_runtime_3892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_3893_: u8 = 0;
    let mut v_res_3894_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_3893_ = (lean_unbox(v_t_3890_) as u8);
    v_res_3894_ =
        l_Lean_IRPhases_runtime_elim(v_motive_3889_, v_t_boxed_3893_, v_h_3891_, v_runtime_3892_);
    lean_dec(v_runtime_3892_);
    return v_res_3894_;
}
pub unsafe fn l_Lean_IRPhases_comptime_elim___redArg(
    mut v_comptime_3895_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_comptime_3895_);
    return v_comptime_3895_;
}
pub unsafe fn l_Lean_IRPhases_comptime_elim___redArg___boxed(
    mut v_comptime_3896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3897_: *mut LeanObject = core::ptr::null_mut();
    v_res_3897_ = l_Lean_IRPhases_comptime_elim___redArg(v_comptime_3896_);
    lean_dec(v_comptime_3896_);
    return v_res_3897_;
}
pub unsafe fn l_Lean_IRPhases_comptime_elim(
    mut v_motive_3898_: *mut LeanObject,
    mut v_t_3899_: u8,
    mut v_h_3900_: *mut LeanObject,
    mut v_comptime_3901_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_comptime_3901_);
    return v_comptime_3901_;
}
pub unsafe fn l_Lean_IRPhases_comptime_elim___boxed(
    mut v_motive_3902_: *mut LeanObject,
    mut v_t_3903_: *mut LeanObject,
    mut v_h_3904_: *mut LeanObject,
    mut v_comptime_3905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_3906_: u8 = 0;
    let mut v_res_3907_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_3906_ = (lean_unbox(v_t_3903_) as u8);
    v_res_3907_ =
        l_Lean_IRPhases_comptime_elim(v_motive_3902_, v_t_boxed_3906_, v_h_3904_, v_comptime_3905_);
    lean_dec(v_comptime_3905_);
    return v_res_3907_;
}
pub unsafe fn l_Lean_IRPhases_all_elim___redArg(
    mut v_all_3908_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_all_3908_);
    return v_all_3908_;
}
pub unsafe fn l_Lean_IRPhases_all_elim___redArg___boxed(
    mut v_all_3909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3910_: *mut LeanObject = core::ptr::null_mut();
    v_res_3910_ = l_Lean_IRPhases_all_elim___redArg(v_all_3909_);
    lean_dec(v_all_3909_);
    return v_res_3910_;
}
pub unsafe fn l_Lean_IRPhases_all_elim(
    mut v_motive_3911_: *mut LeanObject,
    mut v_t_3912_: u8,
    mut v_h_3913_: *mut LeanObject,
    mut v_all_3914_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_all_3914_);
    return v_all_3914_;
}
pub unsafe fn l_Lean_IRPhases_all_elim___boxed(
    mut v_motive_3915_: *mut LeanObject,
    mut v_t_3916_: *mut LeanObject,
    mut v_h_3917_: *mut LeanObject,
    mut v_all_3918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_3919_: u8 = 0;
    let mut v_res_3920_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_3919_ = (lean_unbox(v_t_3916_) as u8);
    v_res_3920_ = l_Lean_IRPhases_all_elim(v_motive_3915_, v_t_boxed_3919_, v_h_3917_, v_all_3918_);
    lean_dec(v_all_3918_);
    return v_res_3920_;
}
pub unsafe fn _init_l_Lean_instInhabitedIRPhases_default() -> u8 {
    let mut v___x_3921_: u8 = 0;
    v___x_3921_ = 0;
    return v___x_3921_;
}
pub unsafe fn _init_l_Lean_instInhabitedIRPhases() -> u8 {
    let mut v___x_3922_: u8 = 0;
    v___x_3922_ = 0;
    return v___x_3922_;
}
pub unsafe fn l_Lean_instBEqIRPhases_beq(mut v_x_3923_: u8, mut v_y_3924_: u8) -> u8 {
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: u8 = 0;
    v___x_3925_ = l_Lean_IRPhases_ctorIdx(v_x_3923_);
    v___x_3926_ = l_Lean_IRPhases_ctorIdx(v_y_3924_);
    v___x_3927_ = lean_nat_dec_eq(v___x_3925_, v___x_3926_);
    lean_dec(v___x_3926_);
    lean_dec(v___x_3925_);
    return v___x_3927_;
}
pub unsafe fn l_Lean_instBEqIRPhases_beq___boxed(
    mut v_x_3928_: *mut LeanObject,
    mut v_y_3929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_17__boxed_3930_: u8 = 0;
    let mut v_y_18__boxed_3931_: u8 = 0;
    let mut v_res_3932_: u8 = 0;
    let mut v_r_3933_: *mut LeanObject = core::ptr::null_mut();
    v_x_17__boxed_3930_ = (lean_unbox(v_x_3928_) as u8);
    v_y_18__boxed_3931_ = (lean_unbox(v_y_3929_) as u8);
    v_res_3932_ = l_Lean_instBEqIRPhases_beq(v_x_17__boxed_3930_, v_y_18__boxed_3931_);
    v_r_3933_ = lean_box((v_res_3932_) as usize);
    return v_r_3933_;
}
pub unsafe fn _init_l_Lean_instReprIRPhases_repr___closed__6() -> *mut LeanObject {
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    v___x_3945_ = lean_unsigned_to_nat(2);
    v___x_3946_ = lean_nat_to_int(v___x_3945_);
    return v___x_3946_;
}
pub unsafe fn _init_l_Lean_instReprIRPhases_repr___closed__7() -> *mut LeanObject {
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    v___x_3947_ = lean_unsigned_to_nat(1);
    v___x_3948_ = lean_nat_to_int(v___x_3947_);
    return v___x_3948_;
}
pub unsafe fn l_Lean_instReprIRPhases_repr(
    mut v_x_3949_: u8,
    mut v_prec_3950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: u8 = 0;
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: u8 = 0;
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: u8 = 0;
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: u8 = 0;
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: u8 = 0;
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: u8 = 0;
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_3949_ {
                0 => {
                    v___x_3972_ = lean_unsigned_to_nat(1024);
                    v___x_3973_ = lean_nat_dec_le(v___x_3972_, v_prec_3950_);
                    if v___x_3973_ == 0 {
                        v___x_3974_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprIRPhases_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lean_instReprIRPhases_repr___closed__6_once),
                            _init_l_Lean_instReprIRPhases_repr___closed__6,
                        );
                        v___y_3952_ = v___x_3974_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3975_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprIRPhases_repr___closed__7),
                            core::ptr::addr_of_mut!(l_Lean_instReprIRPhases_repr___closed__7_once),
                            _init_l_Lean_instReprIRPhases_repr___closed__7,
                        );
                        v___y_3952_ = v___x_3975_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_3976_ = lean_unsigned_to_nat(1024);
                    v___x_3977_ = lean_nat_dec_le(v___x_3976_, v_prec_3950_);
                    if v___x_3977_ == 0 {
                        v___x_3978_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprIRPhases_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lean_instReprIRPhases_repr___closed__6_once),
                            _init_l_Lean_instReprIRPhases_repr___closed__6,
                        );
                        v___y_3959_ = v___x_3978_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3979_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprIRPhases_repr___closed__7),
                            core::ptr::addr_of_mut!(l_Lean_instReprIRPhases_repr___closed__7_once),
                            _init_l_Lean_instReprIRPhases_repr___closed__7,
                        );
                        v___y_3959_ = v___x_3979_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v___x_3980_ = lean_unsigned_to_nat(1024);
                    v___x_3981_ = lean_nat_dec_le(v___x_3980_, v_prec_3950_);
                    if v___x_3981_ == 0 {
                        v___x_3982_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprIRPhases_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lean_instReprIRPhases_repr___closed__6_once),
                            _init_l_Lean_instReprIRPhases_repr___closed__6,
                        );
                        v___y_3966_ = v___x_3982_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3983_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprIRPhases_repr___closed__7),
                            core::ptr::addr_of_mut!(l_Lean_instReprIRPhases_repr___closed__7_once),
                            _init_l_Lean_instReprIRPhases_repr___closed__7,
                        );
                        v___y_3966_ = v___x_3983_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_3953_ = l_Lean_instReprIRPhases_repr___closed__1;
                lean_inc(v___y_3952_);
                v___x_3954_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3954_, 0, v___y_3952_);
                lean_ctor_set(v___x_3954_, 1, v___x_3953_);
                v___x_3955_ = 0;
                v___x_3956_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3956_, 0, v___x_3954_);
                lean_ctor_set_uint8(
                    v___x_3956_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3955_,
                );
                v___x_3957_ = l_Repr_addAppParen(v___x_3956_, v_prec_3950_);
                return v___x_3957_;
            }
            2 => {
                v___x_3960_ = l_Lean_instReprIRPhases_repr___closed__3;
                lean_inc(v___y_3959_);
                v___x_3961_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3961_, 0, v___y_3959_);
                lean_ctor_set(v___x_3961_, 1, v___x_3960_);
                v___x_3962_ = 0;
                v___x_3963_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3963_, 0, v___x_3961_);
                lean_ctor_set_uint8(
                    v___x_3963_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3962_,
                );
                v___x_3964_ = l_Repr_addAppParen(v___x_3963_, v_prec_3950_);
                return v___x_3964_;
            }
            3 => {
                v___x_3967_ = l_Lean_instReprIRPhases_repr___closed__5;
                lean_inc(v___y_3966_);
                v___x_3968_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3968_, 0, v___y_3966_);
                lean_ctor_set(v___x_3968_, 1, v___x_3967_);
                v___x_3969_ = 0;
                v___x_3970_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3970_, 0, v___x_3968_);
                lean_ctor_set_uint8(
                    v___x_3970_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3969_,
                );
                v___x_3971_ = l_Repr_addAppParen(v___x_3970_, v_prec_3950_);
                return v___x_3971_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instReprIRPhases_repr___boxed(
    mut v_x_3984_: *mut LeanObject,
    mut v_prec_3985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_177__boxed_3986_: u8 = 0;
    let mut v_res_3987_: *mut LeanObject = core::ptr::null_mut();
    v_x_177__boxed_3986_ = (lean_unbox(v_x_3984_) as u8);
    v_res_3987_ = l_Lean_instReprIRPhases_repr(v_x_177__boxed_3986_, v_prec_3985_);
    lean_dec(v_prec_3985_);
    return v_res_3987_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0_spec__1_spec__2(
    mut v_x_3990_: *mut LeanObject,
    mut v_x_3991_: *mut LeanObject,
    mut v_x_3992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3997_: u8 = 0;
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4004_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3992_) == 0 {
                    lean_dec(v_x_3990_);
                    return v_x_3991_;
                } else {
                    v_head_3993_ = lean_ctor_get(v_x_3992_, 0);
                    v_tail_3994_ = lean_ctor_get(v_x_3992_, 1);
                    v_isSharedCheck_4004_ = (!lean_is_exclusive(v_x_3992_)) as u8;
                    if v_isSharedCheck_4004_ == 0 {
                        v___x_3996_ = v_x_3992_;
                        v_isShared_3997_ = v_isSharedCheck_4004_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3994_);
                        lean_inc(v_head_3993_);
                        lean_dec(v_x_3992_);
                        v___x_3996_ = lean_box(0);
                        v_isShared_3997_ = v_isSharedCheck_4004_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_3990_);
                if v_isShared_3997_ == 0 {
                    lean_ctor_set_tag(v___x_3996_, 5);
                    lean_ctor_set(v___x_3996_, 1, v_x_3990_);
                    lean_ctor_set(v___x_3996_, 0, v_x_3991_);
                    v___x_3999_ = v___x_3996_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4003_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_x_3991_);
                    lean_ctor_set(v_reuseFailAlloc_4003_, 1, v_x_3990_);
                    v___x_3999_ = v_reuseFailAlloc_4003_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4000_ = l_Lean_instReprImport_repr___redArg(v_head_3993_);
                v___x_4001_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4001_, 0, v___x_3999_);
                lean_ctor_set(v___x_4001_, 1, v___x_4000_);
                v_x_3991_ = v___x_4001_;
                v_x_3992_ = v_tail_3994_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0_spec__1(
    mut v_x_4005_: *mut LeanObject,
    mut v_x_4006_: *mut LeanObject,
    mut v_x_4007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4012_: u8 = 0;
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4019_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4007_) == 0 {
                    lean_dec(v_x_4005_);
                    return v_x_4006_;
                } else {
                    v_head_4008_ = lean_ctor_get(v_x_4007_, 0);
                    v_tail_4009_ = lean_ctor_get(v_x_4007_, 1);
                    v_isSharedCheck_4019_ = (!lean_is_exclusive(v_x_4007_)) as u8;
                    if v_isSharedCheck_4019_ == 0 {
                        v___x_4011_ = v_x_4007_;
                        v_isShared_4012_ = v_isSharedCheck_4019_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4009_);
                        lean_inc(v_head_4008_);
                        lean_dec(v_x_4007_);
                        v___x_4011_ = lean_box(0);
                        v_isShared_4012_ = v_isSharedCheck_4019_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_4005_);
                if v_isShared_4012_ == 0 {
                    lean_ctor_set_tag(v___x_4011_, 5);
                    lean_ctor_set(v___x_4011_, 1, v_x_4005_);
                    lean_ctor_set(v___x_4011_, 0, v_x_4006_);
                    v___x_4014_ = v___x_4011_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4018_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_x_4006_);
                    lean_ctor_set(v_reuseFailAlloc_4018_, 1, v_x_4005_);
                    v___x_4014_ = v_reuseFailAlloc_4018_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4015_ = l_Lean_instReprImport_repr___redArg(v_head_4008_);
                v___x_4016_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4016_, 0, v___x_4014_);
                lean_ctor_set(v___x_4016_, 1, v___x_4015_);
                v___x_4017_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0_spec__1_spec__2(v_x_4005_, v___x_4016_, v_tail_4009_);
                return v___x_4017_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0(
    mut v_x_4020_: *mut LeanObject,
    mut v_x_4021_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4020_) == 0 {
        let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4021_);
        v___x_4022_ = lean_box(0);
        return v___x_4022_;
    } else {
        let mut v_tail_4023_: *mut LeanObject = core::ptr::null_mut();
        v_tail_4023_ = lean_ctor_get(v_x_4020_, 1);
        if lean_obj_tag(v_tail_4023_) == 0 {
            let mut v_head_4024_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_4021_);
            v_head_4024_ = lean_ctor_get(v_x_4020_, 0);
            lean_inc(v_head_4024_);
            lean_dec_ref_known(v_x_4020_, 2);
            v___x_4025_ = l_Lean_instReprImport_repr___redArg(v_head_4024_);
            return v___x_4025_;
        } else {
            let mut v_head_4026_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_4023_);
            v_head_4026_ = lean_ctor_get(v_x_4020_, 0);
            lean_inc(v_head_4026_);
            lean_dec_ref_known(v_x_4020_, 2);
            v___x_4027_ = l_Lean_instReprImport_repr___redArg(v_head_4026_);
            v___x_4028_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0_spec__1(v_x_4021_, v___x_4027_, v_tail_4023_);
            return v___x_4028_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    v___x_4034_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__0;
    v___x_4035_ = lean_string_length(v___x_4034_);
    return v___x_4035_;
}
pub unsafe fn _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    v___x_4036_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3_once
        ),
        _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__3,
    );
    v___x_4037_ = lean_nat_to_int(v___x_4036_);
    return v___x_4037_;
}
pub unsafe fn l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0(
    mut v_xs_4045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: u8 = 0;
    v___x_4046_ = lean_array_get_size(v_xs_4045_);
    v___x_4047_ = lean_unsigned_to_nat(0);
    v___x_4048_ = lean_nat_dec_eq(v___x_4046_, v___x_4047_);
    if v___x_4048_ == 0 {
        let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
        v___x_4049_ = lean_array_to_list(v_xs_4045_);
        v___x_4050_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1;
        v___x_4051_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0_spec__0(v___x_4049_, v___x_4050_);
        v___x_4052_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4_once
            ),
            _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4,
        );
        v___x_4053_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5;
        v___x_4054_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_4054_, 0, v___x_4053_);
        lean_ctor_set(v___x_4054_, 1, v___x_4051_);
        v___x_4055_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6;
        v___x_4056_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_4056_, 0, v___x_4054_);
        lean_ctor_set(v___x_4056_, 1, v___x_4055_);
        v___x_4057_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_4057_, 0, v___x_4052_);
        lean_ctor_set(v___x_4057_, 1, v___x_4056_);
        v___x_4058_ = l_Std_Format_fill(v___x_4057_);
        return v___x_4058_;
    } else {
        let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_4045_);
        v___x_4059_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8;
        return v___x_4059_;
    }
}
pub unsafe fn _init_l_Lean_instReprModuleHeader_repr___redArg___closed__4() -> *mut LeanObject {
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    v___x_4069_ = lean_unsigned_to_nat(11);
    v___x_4070_ = lean_nat_to_int(v___x_4069_);
    return v___x_4070_;
}
pub unsafe fn _init_l_Lean_instReprModuleHeader_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    v___x_4074_ = lean_unsigned_to_nat(12);
    v___x_4075_ = lean_nat_to_int(v___x_4074_);
    return v___x_4075_;
}
pub unsafe fn l_Lean_instReprModuleHeader_repr___redArg(
    mut v_x_4076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_imports_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_4078_: u8 = 0;
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4081_: u8 = 0;
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: u8 = 0;
    let mut v___x_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4111_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_imports_4077_ = lean_ctor_get(v_x_4076_, 0);
                v_isModule_4078_ = lean_ctor_get_uint8(
                    v_x_4076_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_4111_ = (!lean_is_exclusive(v_x_4076_)) as u8;
                if v_isSharedCheck_4111_ == 0 {
                    v___x_4080_ = v_x_4076_;
                    v_isShared_4081_ = v_isSharedCheck_4111_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_imports_4077_);
                    lean_dec(v_x_4076_);
                    v___x_4080_ = lean_box(0);
                    v_isShared_4081_ = v_isSharedCheck_4111_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4082_ = l_Lean_instReprImport_repr___redArg___closed__5;
                v___x_4083_ = l_Lean_instReprModuleHeader_repr___redArg___closed__3;
                v___x_4084_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instReprModuleHeader_repr___redArg___closed__4),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprModuleHeader_repr___redArg___closed__4_once
                    ),
                    _init_l_Lean_instReprModuleHeader_repr___redArg___closed__4,
                );
                v___x_4085_ =
                    l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0(v_imports_4077_);
                v___x_4086_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4086_, 0, v___x_4084_);
                lean_ctor_set(v___x_4086_, 1, v___x_4085_);
                v___x_4087_ = 0;
                if v_isShared_4081_ == 0 {
                    lean_ctor_set_tag(v___x_4080_, 6);
                    lean_ctor_set(v___x_4080_, 0, v___x_4086_);
                    v___x_4089_ = v___x_4080_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4110_ = lean_alloc_ctor(6, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4110_, 0, v___x_4086_);
                    v___x_4089_ = v_reuseFailAlloc_4110_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_4089_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4087_,
                );
                v___x_4090_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4090_, 0, v___x_4083_);
                lean_ctor_set(v___x_4090_, 1, v___x_4089_);
                v___x_4091_ = l_Lean_instReprImport_repr___redArg___closed__9;
                v___x_4092_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4092_, 0, v___x_4090_);
                lean_ctor_set(v___x_4092_, 1, v___x_4091_);
                v___x_4093_ = lean_box(1);
                v___x_4094_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4094_, 0, v___x_4092_);
                lean_ctor_set(v___x_4094_, 1, v___x_4093_);
                v___x_4095_ = l_Lean_instReprModuleHeader_repr___redArg___closed__6;
                v___x_4096_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4096_, 0, v___x_4094_);
                lean_ctor_set(v___x_4096_, 1, v___x_4095_);
                v___x_4097_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4097_, 0, v___x_4096_);
                lean_ctor_set(v___x_4097_, 1, v___x_4082_);
                v___x_4098_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instReprModuleHeader_repr___redArg___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprModuleHeader_repr___redArg___closed__7_once
                    ),
                    _init_l_Lean_instReprModuleHeader_repr___redArg___closed__7,
                );
                v___x_4099_ = l_Bool_repr___redArg(v_isModule_4078_);
                v___x_4100_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4100_, 0, v___x_4098_);
                lean_ctor_set(v___x_4100_, 1, v___x_4099_);
                v___x_4101_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4101_, 0, v___x_4100_);
                lean_ctor_set_uint8(
                    v___x_4101_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4087_,
                );
                v___x_4102_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4102_, 0, v___x_4097_);
                lean_ctor_set(v___x_4102_, 1, v___x_4101_);
                v___x_4103_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__20),
                    core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__20_once),
                    _init_l_Lean_instReprImport_repr___redArg___closed__20,
                );
                v___x_4104_ = l_Lean_instReprImport_repr___redArg___closed__21;
                v___x_4105_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4105_, 0, v___x_4104_);
                lean_ctor_set(v___x_4105_, 1, v___x_4102_);
                v___x_4106_ = l_Lean_instReprImport_repr___redArg___closed__22;
                v___x_4107_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4107_, 0, v___x_4105_);
                lean_ctor_set(v___x_4107_, 1, v___x_4106_);
                v___x_4108_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4108_, 0, v___x_4103_);
                lean_ctor_set(v___x_4108_, 1, v___x_4107_);
                v___x_4109_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4109_, 0, v___x_4108_);
                lean_ctor_set_uint8(
                    v___x_4109_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4087_,
                );
                return v___x_4109_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instReprModuleHeader_repr(
    mut v_x_4112_: *mut LeanObject,
    mut v_prec_4113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    v___x_4114_ = l_Lean_instReprModuleHeader_repr___redArg(v_x_4112_);
    return v___x_4114_;
}
pub unsafe fn l_Lean_instReprModuleHeader_repr___boxed(
    mut v_x_4115_: *mut LeanObject,
    mut v_prec_4116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4117_: *mut LeanObject = core::ptr::null_mut();
    v_res_4117_ = l_Lean_instReprModuleHeader_repr(v_x_4115_, v_prec_4116_);
    lean_dec(v_prec_4116_);
    return v_res_4117_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0(
    mut v_sz_4127_: usize,
    mut v_i_4128_: usize,
    mut v_bs_4129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4130_: u8 = 0;
    let mut v_v_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: usize = 0;
    let mut v___x_4136_: usize = 0;
    let mut v___x_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4130_ = lean_usize_dec_lt(v_i_4128_, v_sz_4127_);
                if v___x_4130_ == 0 {
                    return v_bs_4129_;
                } else {
                    v_v_4131_ = lean_array_uget(v_bs_4129_, v_i_4128_);
                    v___x_4132_ = lean_unsigned_to_nat(0);
                    v_bs_x27_4133_ = lean_array_uset(v_bs_4129_, v_i_4128_, v___x_4132_);
                    v___x_4134_ = l_Lean_instToJsonImport_toJson(v_v_4131_);
                    v___x_4135_ = 1usize;
                    v___x_4136_ = lean_usize_add(v_i_4128_, v___x_4135_);
                    v___x_4137_ = lean_array_uset(v_bs_x27_4133_, v_i_4128_, v___x_4134_);
                    v_i_4128_ = v___x_4136_;
                    v_bs_4129_ = v___x_4137_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0___boxed(
    mut v_sz_4139_: *mut LeanObject,
    mut v_i_4140_: *mut LeanObject,
    mut v_bs_4141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4142_: usize = 0;
    let mut v_i_boxed_4143_: usize = 0;
    let mut v_res_4144_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4142_ = lean_unbox_usize(v_sz_4139_);
    lean_dec(v_sz_4139_);
    v_i_boxed_4143_ = lean_unbox_usize(v_i_4140_);
    lean_dec(v_i_4140_);
    v_res_4144_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0(v_sz_boxed_4142_, v_i_boxed_4143_, v_bs_4141_);
    return v_res_4144_;
}
pub unsafe fn l_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0(
    mut v_a_4145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_4146_: usize = 0;
    let mut v___x_4147_: usize = 0;
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    v_sz_4146_ = lean_array_size(v_a_4145_);
    v___x_4147_ = 0usize;
    v___x_4148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0_spec__0(v_sz_4146_, v___x_4147_, v_a_4145_);
    v___x_4149_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_4149_, 0, v___x_4148_);
    return v___x_4149_;
}
pub unsafe fn l_Lean_instToJsonModuleHeader_toJson(
    mut v_x_4150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_imports_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_4152_: u8 = 0;
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    v_imports_4151_ = lean_ctor_get(v_x_4150_, 0);
    lean_inc_ref(v_imports_4151_);
    v_isModule_4152_ = lean_ctor_get_uint8(
        v_x_4150_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    lean_dec_ref(v_x_4150_);
    v___x_4153_ = l_Lean_instReprModuleHeader_repr___redArg___closed__0;
    v___x_4154_ =
        l_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0(v_imports_4151_);
    v___x_4155_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4155_, 0, v___x_4153_);
    lean_ctor_set(v___x_4155_, 1, v___x_4154_);
    v___x_4156_ = lean_box(0);
    v___x_4157_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4157_, 0, v___x_4155_);
    lean_ctor_set(v___x_4157_, 1, v___x_4156_);
    v___x_4158_ = l_Lean_instReprModuleHeader_repr___redArg___closed__5;
    v___x_4159_ = lean_alloc_ctor(1, 0, (1) as u32);
    lean_ctor_set_uint8(v___x_4159_, 0 as u32, v_isModule_4152_);
    v___x_4160_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4160_, 0, v___x_4158_);
    lean_ctor_set(v___x_4160_, 1, v___x_4159_);
    v___x_4161_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4161_, 0, v___x_4160_);
    lean_ctor_set(v___x_4161_, 1, v___x_4156_);
    v___x_4162_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4162_, 0, v___x_4161_);
    lean_ctor_set(v___x_4162_, 1, v___x_4156_);
    v___x_4163_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4163_, 0, v___x_4157_);
    lean_ctor_set(v___x_4163_, 1, v___x_4162_);
    v___x_4164_ = l_Lean_instToJsonImport_toJson___closed__0;
    v___x_4165_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(v___x_4163_, v___x_4164_);
    v___x_4166_ = l_Lean_Json_mkObj(v___x_4165_);
    lean_dec(v___x_4165_);
    return v___x_4166_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1(
    mut v_sz_4169_: usize,
    mut v_i_4170_: usize,
    mut v_bs_4171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4172_: u8 = 0;
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4179_: u8 = 0;
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4183_: u8 = 0;
    let mut v_a_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: usize = 0;
    let mut v___x_4188_: usize = 0;
    let mut v___x_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4172_ = lean_usize_dec_lt(v_i_4170_, v_sz_4169_);
                if v___x_4172_ == 0 {
                    v___x_4173_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4173_, 0, v_bs_4171_);
                    return v___x_4173_;
                } else {
                    v_v_4174_ = lean_array_uget_borrowed(v_bs_4171_, v_i_4170_);
                    lean_inc(v_v_4174_);
                    v___x_4175_ = l_Lean_instFromJsonImport_fromJson(v_v_4174_);
                    if lean_obj_tag(v___x_4175_) == 0 {
                        lean_dec_ref(v_bs_4171_);
                        v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
                        v_isSharedCheck_4183_ = (!lean_is_exclusive(v___x_4175_)) as u8;
                        if v_isSharedCheck_4183_ == 0 {
                            v___x_4178_ = v___x_4175_;
                            v_isShared_4179_ = v_isSharedCheck_4183_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4176_);
                            lean_dec(v___x_4175_);
                            v___x_4178_ = lean_box(0);
                            v_isShared_4179_ = v_isSharedCheck_4183_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4184_ = lean_ctor_get(v___x_4175_, 0);
                        lean_inc(v_a_4184_);
                        lean_dec_ref_known(v___x_4175_, 1);
                        v___x_4185_ = lean_unsigned_to_nat(0);
                        v_bs_x27_4186_ = lean_array_uset(v_bs_4171_, v_i_4170_, v___x_4185_);
                        v___x_4187_ = 1usize;
                        v___x_4188_ = lean_usize_add(v_i_4170_, v___x_4187_);
                        v___x_4189_ = lean_array_uset(v_bs_x27_4186_, v_i_4170_, v_a_4184_);
                        v_i_4170_ = v___x_4188_;
                        v_bs_4171_ = v___x_4189_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4179_ == 0 {
                    v___x_4181_ = v___x_4178_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4182_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4176_);
                    v___x_4181_ = v_reuseFailAlloc_4182_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4181_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1___boxed(
    mut v_sz_4191_: *mut LeanObject,
    mut v_i_4192_: *mut LeanObject,
    mut v_bs_4193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4194_: usize = 0;
    let mut v_i_boxed_4195_: usize = 0;
    let mut v_res_4196_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4194_ = lean_unbox_usize(v_sz_4191_);
    lean_dec(v_sz_4191_);
    v_i_boxed_4195_ = lean_unbox_usize(v_i_4192_);
    lean_dec(v_i_4192_);
    v_res_4196_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_4194_, v_i_boxed_4195_, v_bs_4193_);
    return v_res_4196_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0(
    mut v_x_4199_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4199_) == 4 {
        let mut v_elems_4200_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_4201_: usize = 0;
        let mut v___x_4202_: usize = 0;
        let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
        v_elems_4200_ = lean_ctor_get(v_x_4199_, 0);
        lean_inc_ref(v_elems_4200_);
        lean_dec_ref_known(v_x_4199_, 1);
        v_sz_4201_ = lean_array_size(v_elems_4200_);
        v___x_4202_ = 0usize;
        v___x_4203_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0_spec__1(v_sz_4201_, v___x_4202_, v_elems_4200_);
        return v___x_4203_;
    } else {
        let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
        v___x_4204_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0;
        v___x_4205_ = lean_unsigned_to_nat(80);
        v___x_4206_ = l_Lean_Json_pretty(v_x_4199_, v___x_4205_);
        v___x_4207_ = lean_string_append(v___x_4204_, v___x_4206_);
        lean_dec_ref(v___x_4206_);
        v___x_4208_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1;
        v___x_4209_ = lean_string_append(v___x_4207_, v___x_4208_);
        v___x_4210_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4210_, 0, v___x_4209_);
        return v___x_4210_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0(
    mut v_j_4211_: *mut LeanObject,
    mut v_k_4212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    v___x_4213_ = l_Lean_Json_getObjValD(v_j_4211_, v_k_4212_);
    v___x_4214_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0(v___x_4213_);
    return v___x_4214_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0___boxed(
    mut v_j_4215_: *mut LeanObject,
    mut v_k_4216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4217_: *mut LeanObject = core::ptr::null_mut();
    v_res_4217_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0(
            v_j_4215_, v_k_4216_,
        );
    lean_dec_ref(v_k_4216_);
    return v_res_4217_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__2() -> *mut LeanObject {
    let mut v___x_4222_: u8 = 0;
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    v___x_4222_ = 1;
    v___x_4223_ = l_Lean_instFromJsonModuleHeader_fromJson___closed__1;
    v___x_4224_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4223_, v___x_4222_);
    return v___x_4224_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__3() -> *mut LeanObject {
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    v___x_4225_ = l_Lean_instFromJsonImport_fromJson___closed__4;
    v___x_4226_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleHeader_fromJson___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleHeader_fromJson___closed__2_once),
        _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__2,
    );
    v___x_4227_ = lean_string_append(v___x_4226_, v___x_4225_);
    return v___x_4227_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__5() -> *mut LeanObject {
    let mut v___x_4230_: u8 = 0;
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    v___x_4230_ = 1;
    v___x_4231_ = l_Lean_instFromJsonModuleHeader_fromJson___closed__4;
    v___x_4232_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4231_, v___x_4230_);
    return v___x_4232_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__6() -> *mut LeanObject {
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    v___x_4233_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleHeader_fromJson___closed__5),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleHeader_fromJson___closed__5_once),
        _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__5,
    );
    v___x_4234_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleHeader_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleHeader_fromJson___closed__3_once),
        _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__3,
    );
    v___x_4235_ = lean_string_append(v___x_4234_, v___x_4233_);
    return v___x_4235_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__7() -> *mut LeanObject {
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    v___x_4236_ = l_Lean_instFromJsonImport_fromJson___closed__9;
    v___x_4237_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleHeader_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleHeader_fromJson___closed__6_once),
        _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__6,
    );
    v___x_4238_ = lean_string_append(v___x_4237_, v___x_4236_);
    return v___x_4238_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__9() -> *mut LeanObject {
    let mut v___x_4241_: u8 = 0;
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut LeanObject = core::ptr::null_mut();
    v___x_4241_ = 1;
    v___x_4242_ = l_Lean_instFromJsonModuleHeader_fromJson___closed__8;
    v___x_4243_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4242_, v___x_4241_);
    return v___x_4243_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__10() -> *mut LeanObject {
    let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    v___x_4244_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleHeader_fromJson___closed__9),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleHeader_fromJson___closed__9_once),
        _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__9,
    );
    v___x_4245_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleHeader_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleHeader_fromJson___closed__3_once),
        _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__3,
    );
    v___x_4246_ = lean_string_append(v___x_4245_, v___x_4244_);
    return v___x_4246_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__11() -> *mut LeanObject {
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    v___x_4247_ = l_Lean_instFromJsonImport_fromJson___closed__9;
    v___x_4248_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleHeader_fromJson___closed__10),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleHeader_fromJson___closed__10_once),
        _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__10,
    );
    v___x_4249_ = lean_string_append(v___x_4248_, v___x_4247_);
    return v___x_4249_;
}
pub unsafe fn l_Lean_instFromJsonModuleHeader_fromJson(
    mut v_json_4250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4256_: u8 = 0;
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4262_: u8 = 0;
    let mut v_a_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4266_: u8 = 0;
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4270_: u8 = 0;
    let mut v_a_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4277_: u8 = 0;
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4283_: u8 = 0;
    let mut v_a_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4287_: u8 = 0;
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4291_: u8 = 0;
    let mut v_a_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4295_: u8 = 0;
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: u8 = 0;
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4301_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4251_ = l_Lean_instReprModuleHeader_repr___redArg___closed__0;
                lean_inc(v_json_4250_);
                v___x_4252_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0(v_json_4250_, v___x_4251_);
                if lean_obj_tag(v___x_4252_) == 0 {
                    lean_dec(v_json_4250_);
                    v_a_4253_ = lean_ctor_get(v___x_4252_, 0);
                    v_isSharedCheck_4262_ = (!lean_is_exclusive(v___x_4252_)) as u8;
                    if v_isSharedCheck_4262_ == 0 {
                        v___x_4255_ = v___x_4252_;
                        v_isShared_4256_ = v_isSharedCheck_4262_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4253_);
                        lean_dec(v___x_4252_);
                        v___x_4255_ = lean_box(0);
                        v_isShared_4256_ = v_isSharedCheck_4262_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_4252_) == 0 {
                        lean_dec(v_json_4250_);
                        v_a_4263_ = lean_ctor_get(v___x_4252_, 0);
                        v_isSharedCheck_4270_ = (!lean_is_exclusive(v___x_4252_)) as u8;
                        if v_isSharedCheck_4270_ == 0 {
                            v___x_4265_ = v___x_4252_;
                            v_isShared_4266_ = v_isSharedCheck_4270_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4263_);
                            lean_dec(v___x_4252_);
                            v___x_4265_ = lean_box(0);
                            v_isShared_4266_ = v_isSharedCheck_4270_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4271_ = lean_ctor_get(v___x_4252_, 0);
                        lean_inc(v_a_4271_);
                        lean_dec_ref_known(v___x_4252_, 1);
                        v___x_4272_ = l_Lean_instReprModuleHeader_repr___redArg___closed__5;
                        v___x_4273_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(v_json_4250_, v___x_4272_);
                        if lean_obj_tag(v___x_4273_) == 0 {
                            lean_dec(v_a_4271_);
                            v_a_4274_ = lean_ctor_get(v___x_4273_, 0);
                            v_isSharedCheck_4283_ = (!lean_is_exclusive(v___x_4273_)) as u8;
                            if v_isSharedCheck_4283_ == 0 {
                                v___x_4276_ = v___x_4273_;
                                v_isShared_4277_ = v_isSharedCheck_4283_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_4274_);
                                lean_dec(v___x_4273_);
                                v___x_4276_ = lean_box(0);
                                v_isShared_4277_ = v_isSharedCheck_4283_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_4273_) == 0 {
                                lean_dec(v_a_4271_);
                                v_a_4284_ = lean_ctor_get(v___x_4273_, 0);
                                v_isSharedCheck_4291_ = (!lean_is_exclusive(v___x_4273_)) as u8;
                                if v_isSharedCheck_4291_ == 0 {
                                    v___x_4286_ = v___x_4273_;
                                    v_isShared_4287_ = v_isSharedCheck_4291_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_4284_);
                                    lean_dec(v___x_4273_);
                                    v___x_4286_ = lean_box(0);
                                    v_isShared_4287_ = v_isSharedCheck_4291_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_4292_ = lean_ctor_get(v___x_4273_, 0);
                                v_isSharedCheck_4301_ = (!lean_is_exclusive(v___x_4273_)) as u8;
                                if v_isSharedCheck_4301_ == 0 {
                                    v___x_4294_ = v___x_4273_;
                                    v_isShared_4295_ = v_isSharedCheck_4301_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_4292_);
                                    lean_dec(v___x_4273_);
                                    v___x_4294_ = lean_box(0);
                                    v_isShared_4295_ = v_isSharedCheck_4301_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4257_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleHeader_fromJson___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleHeader_fromJson___closed__7_once
                    ),
                    _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__7,
                );
                v___x_4258_ = lean_string_append(v___x_4257_, v_a_4253_);
                lean_dec(v_a_4253_);
                if v_isShared_4256_ == 0 {
                    lean_ctor_set(v___x_4255_, 0, v___x_4258_);
                    v___x_4260_ = v___x_4255_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4261_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4261_, 0, v___x_4258_);
                    v___x_4260_ = v_reuseFailAlloc_4261_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4260_;
            }
            3 => {
                if v_isShared_4266_ == 0 {
                    lean_ctor_set_tag(v___x_4265_, 0);
                    v___x_4268_ = v___x_4265_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4269_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4263_);
                    v___x_4268_ = v_reuseFailAlloc_4269_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4268_;
            }
            5 => {
                v___x_4278_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleHeader_fromJson___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleHeader_fromJson___closed__11_once
                    ),
                    _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__11,
                );
                v___x_4279_ = lean_string_append(v___x_4278_, v_a_4274_);
                lean_dec(v_a_4274_);
                if v_isShared_4277_ == 0 {
                    lean_ctor_set(v___x_4276_, 0, v___x_4279_);
                    v___x_4281_ = v___x_4276_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4282_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4282_, 0, v___x_4279_);
                    v___x_4281_ = v_reuseFailAlloc_4282_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4281_;
            }
            7 => {
                if v_isShared_4287_ == 0 {
                    lean_ctor_set_tag(v___x_4286_, 0);
                    v___x_4289_ = v___x_4286_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4290_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4284_);
                    v___x_4289_ = v_reuseFailAlloc_4290_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4289_;
            }
            9 => {
                v___x_4296_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_4296_, 0, v_a_4271_);
                v___x_4297_ = (lean_unbox(v_a_4292_) as u8);
                lean_dec(v_a_4292_);
                lean_ctor_set_uint8(
                    v___x_4296_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4297_,
                );
                if v_isShared_4295_ == 0 {
                    lean_ctor_set(v___x_4294_, 0, v___x_4296_);
                    v___x_4299_ = v___x_4294_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4300_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4300_, 0, v___x_4296_);
                    v___x_4299_ = v_reuseFailAlloc_4300_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4299_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2(
    mut v_x_4307_: *mut LeanObject,
    mut v_x_4308_: *mut LeanObject,
    mut v_x_4309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4314_: u8 = 0;
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4326_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4309_) == 0 {
                    lean_dec(v_x_4307_);
                    return v_x_4308_;
                } else {
                    v_head_4310_ = lean_ctor_get(v_x_4309_, 0);
                    v_tail_4311_ = lean_ctor_get(v_x_4309_, 1);
                    v_isSharedCheck_4326_ = (!lean_is_exclusive(v_x_4309_)) as u8;
                    if v_isSharedCheck_4326_ == 0 {
                        v___x_4313_ = v_x_4309_;
                        v_isShared_4314_ = v_isSharedCheck_4326_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4311_);
                        lean_inc(v_head_4310_);
                        lean_dec(v_x_4309_);
                        v___x_4313_ = lean_box(0);
                        v_isShared_4314_ = v_isSharedCheck_4326_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_4307_);
                if v_isShared_4314_ == 0 {
                    lean_ctor_set_tag(v___x_4313_, 5);
                    lean_ctor_set(v___x_4313_, 1, v_x_4307_);
                    lean_ctor_set(v___x_4313_, 0, v_x_4308_);
                    v___x_4316_ = v___x_4313_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4325_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_x_4308_);
                    lean_ctor_set(v_reuseFailAlloc_4325_, 1, v_x_4307_);
                    v___x_4316_ = v_reuseFailAlloc_4325_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4317_ = lean_unsigned_to_nat(0);
                v___x_4318_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__1;
                v___x_4319_ = l_String_quote(v_head_4310_);
                v___x_4320_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_4320_, 0, v___x_4319_);
                v___x_4321_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4321_, 0, v___x_4318_);
                lean_ctor_set(v___x_4321_, 1, v___x_4320_);
                v___x_4322_ = l_Repr_addAppParen(v___x_4321_, v___x_4317_);
                v___x_4323_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4323_, 0, v___x_4316_);
                lean_ctor_set(v___x_4323_, 1, v___x_4322_);
                v_x_4308_ = v___x_4323_;
                v_x_4309_ = v_tail_4311_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1(
    mut v_x_4327_: *mut LeanObject,
    mut v_x_4328_: *mut LeanObject,
    mut v_x_4329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4334_: u8 = 0;
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4346_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4329_) == 0 {
                    lean_dec(v_x_4327_);
                    return v_x_4328_;
                } else {
                    v_head_4330_ = lean_ctor_get(v_x_4329_, 0);
                    v_tail_4331_ = lean_ctor_get(v_x_4329_, 1);
                    v_isSharedCheck_4346_ = (!lean_is_exclusive(v_x_4329_)) as u8;
                    if v_isSharedCheck_4346_ == 0 {
                        v___x_4333_ = v_x_4329_;
                        v_isShared_4334_ = v_isSharedCheck_4346_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4331_);
                        lean_inc(v_head_4330_);
                        lean_dec(v_x_4329_);
                        v___x_4333_ = lean_box(0);
                        v_isShared_4334_ = v_isSharedCheck_4346_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_4327_);
                if v_isShared_4334_ == 0 {
                    lean_ctor_set_tag(v___x_4333_, 5);
                    lean_ctor_set(v___x_4333_, 1, v_x_4327_);
                    lean_ctor_set(v___x_4333_, 0, v_x_4328_);
                    v___x_4336_ = v___x_4333_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4345_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_x_4328_);
                    lean_ctor_set(v_reuseFailAlloc_4345_, 1, v_x_4327_);
                    v___x_4336_ = v_reuseFailAlloc_4345_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4337_ = lean_unsigned_to_nat(0);
                v___x_4338_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__1;
                v___x_4339_ = l_String_quote(v_head_4330_);
                v___x_4340_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_4340_, 0, v___x_4339_);
                v___x_4341_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4341_, 0, v___x_4338_);
                lean_ctor_set(v___x_4341_, 1, v___x_4340_);
                v___x_4342_ = l_Repr_addAppParen(v___x_4341_, v___x_4337_);
                v___x_4343_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4343_, 0, v___x_4336_);
                lean_ctor_set(v___x_4343_, 1, v___x_4342_);
                v___x_4344_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2(v_x_4327_, v___x_4343_, v_tail_4331_);
                return v___x_4344_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0___lam__0(
    mut v___y_4347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    v___x_4348_ = lean_unsigned_to_nat(0);
    v___x_4349_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__1;
    v___x_4350_ = l_String_quote(v___y_4347_);
    v___x_4351_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_4351_, 0, v___x_4350_);
    v___x_4352_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4352_, 0, v___x_4349_);
    lean_ctor_set(v___x_4352_, 1, v___x_4351_);
    v___x_4353_ = l_Repr_addAppParen(v___x_4352_, v___x_4348_);
    return v___x_4353_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0(
    mut v_x_4354_: *mut LeanObject,
    mut v_x_4355_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4354_) == 0 {
        let mut v___x_4356_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4355_);
        v___x_4356_ = lean_box(0);
        return v___x_4356_;
    } else {
        let mut v_tail_4357_: *mut LeanObject = core::ptr::null_mut();
        v_tail_4357_ = lean_ctor_get(v_x_4354_, 1);
        if lean_obj_tag(v_tail_4357_) == 0 {
            let mut v_head_4358_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_4355_);
            v_head_4358_ = lean_ctor_get(v_x_4354_, 0);
            lean_inc(v_head_4358_);
            lean_dec_ref_known(v_x_4354_, 2);
            v___x_4359_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0___lam__0(v_head_4358_);
            return v___x_4359_;
        } else {
            let mut v_head_4360_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_4357_);
            v_head_4360_ = lean_ctor_get(v_x_4354_, 0);
            lean_inc(v_head_4360_);
            lean_dec_ref_known(v_x_4354_, 2);
            v___x_4361_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0___lam__0(v_head_4360_);
            v___x_4362_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1(v_x_4355_, v___x_4361_, v_tail_4357_);
            return v___x_4362_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0(
    mut v_xs_4363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: u8 = 0;
    v___x_4364_ = lean_array_get_size(v_xs_4363_);
    v___x_4365_ = lean_unsigned_to_nat(0);
    v___x_4366_ = lean_nat_dec_eq(v___x_4364_, v___x_4365_);
    if v___x_4366_ == 0 {
        let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4375_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
        v___x_4367_ = lean_array_to_list(v_xs_4363_);
        v___x_4368_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1;
        v___x_4369_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0(v___x_4367_, v___x_4368_);
        v___x_4370_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4_once
            ),
            _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4,
        );
        v___x_4371_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5;
        v___x_4372_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_4372_, 0, v___x_4371_);
        lean_ctor_set(v___x_4372_, 1, v___x_4369_);
        v___x_4373_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6;
        v___x_4374_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_4374_, 0, v___x_4372_);
        lean_ctor_set(v___x_4374_, 1, v___x_4373_);
        v___x_4375_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_4375_, 0, v___x_4370_);
        lean_ctor_set(v___x_4375_, 1, v___x_4374_);
        v___x_4376_ = l_Std_Format_fill(v___x_4375_);
        return v___x_4376_;
    } else {
        let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_4363_);
        v___x_4377_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8;
        return v___x_4377_;
    }
}
pub unsafe fn l_Lean_instReprImportArtifacts_repr___redArg(
    mut v_x_4387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: u8 = 0;
    let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    v___x_4388_ = l_Lean_instReprImportArtifacts_repr___redArg___closed__3;
    v___x_4389_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprModuleHeader_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instReprModuleHeader_repr___redArg___closed__4_once),
        _init_l_Lean_instReprModuleHeader_repr___redArg___closed__4,
    );
    v___x_4390_ = l_Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0(v_x_4387_);
    v___x_4391_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4391_, 0, v___x_4389_);
    lean_ctor_set(v___x_4391_, 1, v___x_4390_);
    v___x_4392_ = 0;
    v___x_4393_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4393_, 0, v___x_4391_);
    lean_ctor_set_uint8(
        v___x_4393_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4392_,
    );
    v___x_4394_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4394_, 0, v___x_4388_);
    lean_ctor_set(v___x_4394_, 1, v___x_4393_);
    v___x_4395_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__20),
        core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__20_once),
        _init_l_Lean_instReprImport_repr___redArg___closed__20,
    );
    v___x_4396_ = l_Lean_instReprImport_repr___redArg___closed__21;
    v___x_4397_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4397_, 0, v___x_4396_);
    lean_ctor_set(v___x_4397_, 1, v___x_4394_);
    v___x_4398_ = l_Lean_instReprImport_repr___redArg___closed__22;
    v___x_4399_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4399_, 0, v___x_4397_);
    lean_ctor_set(v___x_4399_, 1, v___x_4398_);
    v___x_4400_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4400_, 0, v___x_4395_);
    lean_ctor_set(v___x_4400_, 1, v___x_4399_);
    v___x_4401_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4401_, 0, v___x_4400_);
    lean_ctor_set_uint8(
        v___x_4401_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4392_,
    );
    return v___x_4401_;
}
pub unsafe fn l_Lean_instReprImportArtifacts_repr(
    mut v_x_4402_: *mut LeanObject,
    mut v_prec_4403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    v___x_4404_ = l_Lean_instReprImportArtifacts_repr___redArg(v_x_4402_);
    return v___x_4404_;
}
pub unsafe fn l_Lean_instReprImportArtifacts_repr___boxed(
    mut v_x_4405_: *mut LeanObject,
    mut v_prec_4406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4407_: *mut LeanObject = core::ptr::null_mut();
    v_res_4407_ = l_Lean_instReprImportArtifacts_repr(v_x_4405_, v_prec_4406_);
    lean_dec(v_prec_4406_);
    return v_res_4407_;
}
pub unsafe fn l_Lean_instToJsonImportArtifacts___lam__0(
    mut v___f_4414_: *mut LeanObject,
    mut v_x_4415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    v___x_4416_ = l_Array_toJson___redArg(v___f_4414_, v_x_4415_);
    return v___x_4416_;
}
pub unsafe fn l_Lean_instFromJsonImportArtifacts___lam__0(
    mut v___f_4421_: *mut LeanObject,
    mut v_x_4422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4427_: u8 = 0;
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4431_: u8 = 0;
    let mut v_a_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4435_: u8 = 0;
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4439_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4423_ = l_Array_fromJson_x3f___redArg(v___f_4421_, v_x_4422_);
                if lean_obj_tag(v___x_4423_) == 0 {
                    v_a_4424_ = lean_ctor_get(v___x_4423_, 0);
                    v_isSharedCheck_4431_ = (!lean_is_exclusive(v___x_4423_)) as u8;
                    if v_isSharedCheck_4431_ == 0 {
                        v___x_4426_ = v___x_4423_;
                        v_isShared_4427_ = v_isSharedCheck_4431_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4424_);
                        lean_dec(v___x_4423_);
                        v___x_4426_ = lean_box(0);
                        v_isShared_4427_ = v_isSharedCheck_4431_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4432_ = lean_ctor_get(v___x_4423_, 0);
                    v_isSharedCheck_4439_ = (!lean_is_exclusive(v___x_4423_)) as u8;
                    if v_isSharedCheck_4439_ == 0 {
                        v___x_4434_ = v___x_4423_;
                        v_isShared_4435_ = v_isSharedCheck_4439_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4432_);
                        lean_dec(v___x_4423_);
                        v___x_4434_ = lean_box(0);
                        v_isShared_4435_ = v_isSharedCheck_4439_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4427_ == 0 {
                    v___x_4429_ = v___x_4426_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4430_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_a_4424_);
                    v___x_4429_ = v_reuseFailAlloc_4430_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4429_;
            }
            3 => {
                if v_isShared_4435_ == 0 {
                    v___x_4437_ = v___x_4434_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4438_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4438_, 0, v_a_4432_);
                    v___x_4437_ = v_reuseFailAlloc_4438_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4437_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ImportArtifacts_size(mut v_arts_4444_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    v___x_4445_ = lean_array_get_size(v_arts_4444_);
    return v___x_4445_;
}
pub unsafe fn l_Lean_ImportArtifacts_size___boxed(
    mut v_arts_4446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4447_: *mut LeanObject = core::ptr::null_mut();
    v_res_4447_ = l_Lean_ImportArtifacts_size(v_arts_4446_);
    lean_dec_ref(v_arts_4446_);
    return v_res_4447_;
}
pub unsafe fn l_Lean_ImportArtifacts_olean_x3f(
    mut v_arts_4448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: u8 = 0;
    v___x_4449_ = lean_unsigned_to_nat(0);
    v___x_4450_ = lean_array_get_size(v_arts_4448_);
    v___x_4451_ = lean_nat_dec_lt(v___x_4449_, v___x_4450_);
    if v___x_4451_ == 0 {
        let mut v___x_4452_: *mut LeanObject = core::ptr::null_mut();
        v___x_4452_ = lean_box(0);
        return v___x_4452_;
    } else {
        let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
        v___x_4453_ = lean_array_fget_borrowed(v_arts_4448_, v___x_4449_);
        lean_inc(v___x_4453_);
        v___x_4454_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4454_, 0, v___x_4453_);
        return v___x_4454_;
    }
}
pub unsafe fn l_Lean_ImportArtifacts_olean_x3f___boxed(
    mut v_arts_4455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4456_: *mut LeanObject = core::ptr::null_mut();
    v_res_4456_ = l_Lean_ImportArtifacts_olean_x3f(v_arts_4455_);
    lean_dec_ref(v_arts_4455_);
    return v_res_4456_;
}
pub unsafe fn l_Lean_ImportArtifacts_ir_x3f(mut v_arts_4457_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: u8 = 0;
    v___x_4458_ = lean_unsigned_to_nat(1);
    v___x_4459_ = lean_array_get_size(v_arts_4457_);
    v___x_4460_ = lean_nat_dec_lt(v___x_4458_, v___x_4459_);
    if v___x_4460_ == 0 {
        let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
        v___x_4461_ = lean_box(0);
        return v___x_4461_;
    } else {
        let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
        v___x_4462_ = lean_array_fget_borrowed(v_arts_4457_, v___x_4458_);
        lean_inc(v___x_4462_);
        v___x_4463_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4463_, 0, v___x_4462_);
        return v___x_4463_;
    }
}
pub unsafe fn l_Lean_ImportArtifacts_ir_x3f___boxed(
    mut v_arts_4464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4465_: *mut LeanObject = core::ptr::null_mut();
    v_res_4465_ = l_Lean_ImportArtifacts_ir_x3f(v_arts_4464_);
    lean_dec_ref(v_arts_4464_);
    return v_res_4465_;
}
pub unsafe fn l_Lean_ImportArtifacts_oleanServer_x3f(
    mut v_arts_4466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: u8 = 0;
    v___x_4467_ = lean_unsigned_to_nat(2);
    v___x_4468_ = lean_array_get_size(v_arts_4466_);
    v___x_4469_ = lean_nat_dec_lt(v___x_4467_, v___x_4468_);
    if v___x_4469_ == 0 {
        let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
        v___x_4470_ = lean_box(0);
        return v___x_4470_;
    } else {
        let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
        v___x_4471_ = lean_array_fget_borrowed(v_arts_4466_, v___x_4467_);
        lean_inc(v___x_4471_);
        v___x_4472_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4472_, 0, v___x_4471_);
        return v___x_4472_;
    }
}
pub unsafe fn l_Lean_ImportArtifacts_oleanServer_x3f___boxed(
    mut v_arts_4473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4474_: *mut LeanObject = core::ptr::null_mut();
    v_res_4474_ = l_Lean_ImportArtifacts_oleanServer_x3f(v_arts_4473_);
    lean_dec_ref(v_arts_4473_);
    return v_res_4474_;
}
pub unsafe fn l_Lean_ImportArtifacts_oleanPrivate_x3f(
    mut v_arts_4475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: u8 = 0;
    v___x_4476_ = lean_unsigned_to_nat(3);
    v___x_4477_ = lean_array_get_size(v_arts_4475_);
    v___x_4478_ = lean_nat_dec_lt(v___x_4476_, v___x_4477_);
    if v___x_4478_ == 0 {
        let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
        v___x_4479_ = lean_box(0);
        return v___x_4479_;
    } else {
        let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4481_: *mut LeanObject = core::ptr::null_mut();
        v___x_4480_ = lean_array_fget_borrowed(v_arts_4475_, v___x_4476_);
        lean_inc(v___x_4480_);
        v___x_4481_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4481_, 0, v___x_4480_);
        return v___x_4481_;
    }
}
pub unsafe fn l_Lean_ImportArtifacts_oleanPrivate_x3f___boxed(
    mut v_arts_4482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4483_: *mut LeanObject = core::ptr::null_mut();
    v_res_4483_ = l_Lean_ImportArtifacts_oleanPrivate_x3f(v_arts_4482_);
    lean_dec_ref(v_arts_4482_);
    return v_res_4483_;
}
pub unsafe fn l_Lean_ImportArtifacts_oleanParts(
    mut v_inServer_4486_: u8,
    mut v_arts_4487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fnames_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fnames_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fnames_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fnames_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fnames_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fnames_4493_ = l_Lean_ImportArtifacts_oleanParts___closed__0;
                v___x_4494_ = l_Lean_ImportArtifacts_olean_x3f(v_arts_4487_);
                if lean_obj_tag(v___x_4494_) == 1 {
                    v_val_4495_ = lean_ctor_get(v___x_4494_, 0);
                    lean_inc(v_val_4495_);
                    lean_dec_ref_known(v___x_4494_, 1);
                    v_fnames_4496_ = lean_array_push(v_fnames_4493_, v_val_4495_);
                    v___x_4497_ = l_Lean_ImportArtifacts_oleanServer_x3f(v_arts_4487_);
                    if lean_obj_tag(v___x_4497_) == 1 {
                        v_val_4498_ = lean_ctor_get(v___x_4497_, 0);
                        lean_inc(v_val_4498_);
                        lean_dec_ref_known(v___x_4497_, 1);
                        if v_inServer_4486_ == 0 {
                            v___x_4501_ = l_Lean_ImportArtifacts_oleanPrivate_x3f(v_arts_4487_);
                            if lean_obj_tag(v___x_4501_) == 0 {
                                lean_dec(v_val_4498_);
                                v_fnames_4489_ = v_fnames_4496_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref_known(v___x_4501_, 1);
                                state = 2;
                                continue;
                            }
                        } else {
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_4497_);
                        return v_fnames_4496_;
                    }
                } else {
                    lean_dec(v___x_4494_);
                    return v_fnames_4493_;
                }
            }
            1 => {
                v___x_4490_ = l_Lean_ImportArtifacts_oleanPrivate_x3f(v_arts_4487_);
                if lean_obj_tag(v___x_4490_) == 1 {
                    v_val_4491_ = lean_ctor_get(v___x_4490_, 0);
                    lean_inc(v_val_4491_);
                    lean_dec_ref_known(v___x_4490_, 1);
                    v_fnames_4492_ = lean_array_push(v_fnames_4489_, v_val_4491_);
                    return v_fnames_4492_;
                } else {
                    lean_dec(v___x_4490_);
                    return v_fnames_4489_;
                }
            }
            2 => {
                v_fnames_4500_ = lean_array_push(v_fnames_4496_, v_val_4498_);
                v_fnames_4489_ = v_fnames_4500_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ImportArtifacts_oleanParts___boxed(
    mut v_inServer_4502_: *mut LeanObject,
    mut v_arts_4503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inServer_boxed_4504_: u8 = 0;
    let mut v_res_4505_: *mut LeanObject = core::ptr::null_mut();
    v_inServer_boxed_4504_ = (lean_unbox(v_inServer_4502_) as u8);
    v_res_4505_ = l_Lean_ImportArtifacts_oleanParts(v_inServer_boxed_4504_, v_arts_4503_);
    lean_dec_ref(v_arts_4503_);
    return v_res_4505_;
}
pub unsafe fn l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(
    mut v_x_4512_: *mut LeanObject,
    mut v_x_4513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4518_: u8 = 0;
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4530_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4512_) == 0 {
                    v___x_4514_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__1;
                    return v___x_4514_;
                } else {
                    v_val_4515_ = lean_ctor_get(v_x_4512_, 0);
                    v_isSharedCheck_4530_ = (!lean_is_exclusive(v_x_4512_)) as u8;
                    if v_isSharedCheck_4530_ == 0 {
                        v___x_4517_ = v_x_4512_;
                        v_isShared_4518_ = v_isSharedCheck_4530_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_4515_);
                        lean_dec(v_x_4512_);
                        v___x_4517_ = lean_box(0);
                        v_isShared_4518_ = v_isSharedCheck_4530_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4519_ =
                    l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__3;
                v___x_4520_ = lean_unsigned_to_nat(1024);
                v___x_4521_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__1;
                v___x_4522_ = l_String_quote(v_val_4515_);
                if v_isShared_4518_ == 0 {
                    lean_ctor_set_tag(v___x_4517_, 3);
                    lean_ctor_set(v___x_4517_, 0, v___x_4522_);
                    v___x_4524_ = v___x_4517_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4529_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4529_, 0, v___x_4522_);
                    v___x_4524_ = v_reuseFailAlloc_4529_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4525_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4525_, 0, v___x_4521_);
                lean_ctor_set(v___x_4525_, 1, v___x_4524_);
                v___x_4526_ = l_Repr_addAppParen(v___x_4525_, v___x_4520_);
                v___x_4527_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4527_, 0, v___x_4519_);
                lean_ctor_set(v___x_4527_, 1, v___x_4526_);
                v___x_4528_ = l_Repr_addAppParen(v___x_4527_, v_x_4513_);
                return v___x_4528_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___boxed(
    mut v_x_4531_: *mut LeanObject,
    mut v_x_4532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4533_: *mut LeanObject = core::ptr::null_mut();
    v_res_4533_ =
        l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(v_x_4531_, v_x_4532_);
    lean_dec(v_x_4532_);
    return v_res_4533_;
}
pub unsafe fn _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__4() -> *mut LeanObject {
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    v___x_4543_ = lean_unsigned_to_nat(9);
    v___x_4544_ = lean_nat_to_int(v___x_4543_);
    return v___x_4544_;
}
pub unsafe fn _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__9() -> *mut LeanObject {
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut LeanObject = core::ptr::null_mut();
    v___x_4551_ = lean_unsigned_to_nat(16);
    v___x_4552_ = lean_nat_to_int(v___x_4551_);
    return v___x_4552_;
}
pub unsafe fn _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__12() -> *mut LeanObject {
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    v___x_4556_ = lean_unsigned_to_nat(17);
    v___x_4557_ = lean_nat_to_int(v___x_4556_);
    return v___x_4557_;
}
pub unsafe fn _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__17() -> *mut LeanObject {
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    v___x_4564_ = lean_unsigned_to_nat(7);
    v___x_4565_ = lean_nat_to_int(v___x_4564_);
    return v___x_4565_;
}
pub unsafe fn _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__20() -> *mut LeanObject {
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut LeanObject = core::ptr::null_mut();
    v___x_4569_ = lean_unsigned_to_nat(6);
    v___x_4570_ = lean_nat_to_int(v___x_4569_);
    return v___x_4570_;
}
pub unsafe fn l_Lean_instReprModuleArtifacts_repr___redArg(
    mut v_x_4574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lean_x3f_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_olean_x3f_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_oleanServer_x3f_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_oleanPrivate_x3f_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ilean_x3f_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ir_x3f_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_x3f_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bc_x3f_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: u8 = 0;
    let mut v___x_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
    v_lean_x3f_4575_ = lean_ctor_get(v_x_4574_, 0);
    lean_inc(v_lean_x3f_4575_);
    v_olean_x3f_4576_ = lean_ctor_get(v_x_4574_, 1);
    lean_inc(v_olean_x3f_4576_);
    v_oleanServer_x3f_4577_ = lean_ctor_get(v_x_4574_, 2);
    lean_inc(v_oleanServer_x3f_4577_);
    v_oleanPrivate_x3f_4578_ = lean_ctor_get(v_x_4574_, 3);
    lean_inc(v_oleanPrivate_x3f_4578_);
    v_ilean_x3f_4579_ = lean_ctor_get(v_x_4574_, 4);
    lean_inc(v_ilean_x3f_4579_);
    v_ir_x3f_4580_ = lean_ctor_get(v_x_4574_, 5);
    lean_inc(v_ir_x3f_4580_);
    v_c_x3f_4581_ = lean_ctor_get(v_x_4574_, 6);
    lean_inc(v_c_x3f_4581_);
    v_bc_x3f_4582_ = lean_ctor_get(v_x_4574_, 7);
    lean_inc(v_bc_x3f_4582_);
    lean_dec_ref(v_x_4574_);
    v___x_4583_ = l_Lean_instReprImport_repr___redArg___closed__5;
    v___x_4584_ = l_Lean_instReprModuleArtifacts_repr___redArg___closed__3;
    v___x_4585_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__4_once),
        _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__4,
    );
    v___x_4586_ = lean_unsigned_to_nat(0);
    v___x_4587_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(
        v_lean_x3f_4575_,
        v___x_4586_,
    );
    v___x_4588_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4588_, 0, v___x_4585_);
    lean_ctor_set(v___x_4588_, 1, v___x_4587_);
    v___x_4589_ = 0;
    v___x_4590_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4590_, 0, v___x_4588_);
    lean_ctor_set_uint8(
        v___x_4590_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4589_,
    );
    v___x_4591_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4591_, 0, v___x_4584_);
    lean_ctor_set(v___x_4591_, 1, v___x_4590_);
    v___x_4592_ = l_Lean_instReprImport_repr___redArg___closed__9;
    v___x_4593_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4593_, 0, v___x_4591_);
    lean_ctor_set(v___x_4593_, 1, v___x_4592_);
    v___x_4594_ = lean_box(1);
    v___x_4595_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4595_, 0, v___x_4593_);
    lean_ctor_set(v___x_4595_, 1, v___x_4594_);
    v___x_4596_ = l_Lean_instReprModuleArtifacts_repr___redArg___closed__6;
    v___x_4597_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4597_, 0, v___x_4595_);
    lean_ctor_set(v___x_4597_, 1, v___x_4596_);
    v___x_4598_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4598_, 0, v___x_4597_);
    lean_ctor_set(v___x_4598_, 1, v___x_4583_);
    v___x_4599_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__7_once),
        _init_l_Lean_instReprImport_repr___redArg___closed__7,
    );
    v___x_4600_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(
        v_olean_x3f_4576_,
        v___x_4586_,
    );
    v___x_4601_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4601_, 0, v___x_4599_);
    lean_ctor_set(v___x_4601_, 1, v___x_4600_);
    v___x_4602_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4602_, 0, v___x_4601_);
    lean_ctor_set_uint8(
        v___x_4602_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4589_,
    );
    v___x_4603_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4603_, 0, v___x_4598_);
    lean_ctor_set(v___x_4603_, 1, v___x_4602_);
    v___x_4604_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4604_, 0, v___x_4603_);
    lean_ctor_set(v___x_4604_, 1, v___x_4592_);
    v___x_4605_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4605_, 0, v___x_4604_);
    lean_ctor_set(v___x_4605_, 1, v___x_4594_);
    v___x_4606_ = l_Lean_instReprModuleArtifacts_repr___redArg___closed__8;
    v___x_4607_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4607_, 0, v___x_4605_);
    lean_ctor_set(v___x_4607_, 1, v___x_4606_);
    v___x_4608_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4608_, 0, v___x_4607_);
    lean_ctor_set(v___x_4608_, 1, v___x_4583_);
    v___x_4609_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__9),
        core::ptr::addr_of_mut!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__9_once),
        _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__9,
    );
    v___x_4610_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(
        v_oleanServer_x3f_4577_,
        v___x_4586_,
    );
    v___x_4611_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4611_, 0, v___x_4609_);
    lean_ctor_set(v___x_4611_, 1, v___x_4610_);
    v___x_4612_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4612_, 0, v___x_4611_);
    lean_ctor_set_uint8(
        v___x_4612_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4589_,
    );
    v___x_4613_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4613_, 0, v___x_4608_);
    lean_ctor_set(v___x_4613_, 1, v___x_4612_);
    v___x_4614_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4614_, 0, v___x_4613_);
    lean_ctor_set(v___x_4614_, 1, v___x_4592_);
    v___x_4615_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4615_, 0, v___x_4614_);
    lean_ctor_set(v___x_4615_, 1, v___x_4594_);
    v___x_4616_ = l_Lean_instReprModuleArtifacts_repr___redArg___closed__11;
    v___x_4617_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4617_, 0, v___x_4615_);
    lean_ctor_set(v___x_4617_, 1, v___x_4616_);
    v___x_4618_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4618_, 0, v___x_4617_);
    lean_ctor_set(v___x_4618_, 1, v___x_4583_);
    v___x_4619_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__12_once),
        _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__12,
    );
    v___x_4620_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(
        v_oleanPrivate_x3f_4578_,
        v___x_4586_,
    );
    v___x_4621_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4621_, 0, v___x_4619_);
    lean_ctor_set(v___x_4621_, 1, v___x_4620_);
    v___x_4622_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4622_, 0, v___x_4621_);
    lean_ctor_set_uint8(
        v___x_4622_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4589_,
    );
    v___x_4623_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4623_, 0, v___x_4618_);
    lean_ctor_set(v___x_4623_, 1, v___x_4622_);
    v___x_4624_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4624_, 0, v___x_4623_);
    lean_ctor_set(v___x_4624_, 1, v___x_4592_);
    v___x_4625_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4625_, 0, v___x_4624_);
    lean_ctor_set(v___x_4625_, 1, v___x_4594_);
    v___x_4626_ = l_Lean_instReprModuleArtifacts_repr___redArg___closed__14;
    v___x_4627_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4627_, 0, v___x_4625_);
    lean_ctor_set(v___x_4627_, 1, v___x_4626_);
    v___x_4628_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4628_, 0, v___x_4627_);
    lean_ctor_set(v___x_4628_, 1, v___x_4583_);
    v___x_4629_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(
        v_ilean_x3f_4579_,
        v___x_4586_,
    );
    v___x_4630_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4630_, 0, v___x_4599_);
    lean_ctor_set(v___x_4630_, 1, v___x_4629_);
    v___x_4631_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4631_, 0, v___x_4630_);
    lean_ctor_set_uint8(
        v___x_4631_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4589_,
    );
    v___x_4632_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4632_, 0, v___x_4628_);
    lean_ctor_set(v___x_4632_, 1, v___x_4631_);
    v___x_4633_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4633_, 0, v___x_4632_);
    lean_ctor_set(v___x_4633_, 1, v___x_4592_);
    v___x_4634_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4634_, 0, v___x_4633_);
    lean_ctor_set(v___x_4634_, 1, v___x_4594_);
    v___x_4635_ = l_Lean_instReprModuleArtifacts_repr___redArg___closed__16;
    v___x_4636_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4636_, 0, v___x_4634_);
    lean_ctor_set(v___x_4636_, 1, v___x_4635_);
    v___x_4637_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4637_, 0, v___x_4636_);
    lean_ctor_set(v___x_4637_, 1, v___x_4583_);
    v___x_4638_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__17),
        core::ptr::addr_of_mut!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__17_once),
        _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__17,
    );
    v___x_4639_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(
        v_ir_x3f_4580_,
        v___x_4586_,
    );
    v___x_4640_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4640_, 0, v___x_4638_);
    lean_ctor_set(v___x_4640_, 1, v___x_4639_);
    v___x_4641_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4641_, 0, v___x_4640_);
    lean_ctor_set_uint8(
        v___x_4641_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4589_,
    );
    v___x_4642_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4642_, 0, v___x_4637_);
    lean_ctor_set(v___x_4642_, 1, v___x_4641_);
    v___x_4643_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4643_, 0, v___x_4642_);
    lean_ctor_set(v___x_4643_, 1, v___x_4592_);
    v___x_4644_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4644_, 0, v___x_4643_);
    lean_ctor_set(v___x_4644_, 1, v___x_4594_);
    v___x_4645_ = l_Lean_instReprModuleArtifacts_repr___redArg___closed__19;
    v___x_4646_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4646_, 0, v___x_4644_);
    lean_ctor_set(v___x_4646_, 1, v___x_4645_);
    v___x_4647_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4647_, 0, v___x_4646_);
    lean_ctor_set(v___x_4647_, 1, v___x_4583_);
    v___x_4648_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__20),
        core::ptr::addr_of_mut!(l_Lean_instReprModuleArtifacts_repr___redArg___closed__20_once),
        _init_l_Lean_instReprModuleArtifacts_repr___redArg___closed__20,
    );
    v___x_4649_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(
        v_c_x3f_4581_,
        v___x_4586_,
    );
    v___x_4650_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4650_, 0, v___x_4648_);
    lean_ctor_set(v___x_4650_, 1, v___x_4649_);
    v___x_4651_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4651_, 0, v___x_4650_);
    lean_ctor_set_uint8(
        v___x_4651_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4589_,
    );
    v___x_4652_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4652_, 0, v___x_4647_);
    lean_ctor_set(v___x_4652_, 1, v___x_4651_);
    v___x_4653_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4653_, 0, v___x_4652_);
    lean_ctor_set(v___x_4653_, 1, v___x_4592_);
    v___x_4654_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4654_, 0, v___x_4653_);
    lean_ctor_set(v___x_4654_, 1, v___x_4594_);
    v___x_4655_ = l_Lean_instReprModuleArtifacts_repr___redArg___closed__22;
    v___x_4656_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4656_, 0, v___x_4654_);
    lean_ctor_set(v___x_4656_, 1, v___x_4655_);
    v___x_4657_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4657_, 0, v___x_4656_);
    lean_ctor_set(v___x_4657_, 1, v___x_4583_);
    v___x_4658_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0(
        v_bc_x3f_4582_,
        v___x_4586_,
    );
    v___x_4659_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4659_, 0, v___x_4638_);
    lean_ctor_set(v___x_4659_, 1, v___x_4658_);
    v___x_4660_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4660_, 0, v___x_4659_);
    lean_ctor_set_uint8(
        v___x_4660_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4589_,
    );
    v___x_4661_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4661_, 0, v___x_4657_);
    lean_ctor_set(v___x_4661_, 1, v___x_4660_);
    v___x_4662_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__20),
        core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__20_once),
        _init_l_Lean_instReprImport_repr___redArg___closed__20,
    );
    v___x_4663_ = l_Lean_instReprImport_repr___redArg___closed__21;
    v___x_4664_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4664_, 0, v___x_4663_);
    lean_ctor_set(v___x_4664_, 1, v___x_4661_);
    v___x_4665_ = l_Lean_instReprImport_repr___redArg___closed__22;
    v___x_4666_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4666_, 0, v___x_4664_);
    lean_ctor_set(v___x_4666_, 1, v___x_4665_);
    v___x_4667_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4667_, 0, v___x_4662_);
    lean_ctor_set(v___x_4667_, 1, v___x_4666_);
    v___x_4668_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4668_, 0, v___x_4667_);
    lean_ctor_set_uint8(
        v___x_4668_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4589_,
    );
    return v___x_4668_;
}
pub unsafe fn l_Lean_instReprModuleArtifacts_repr(
    mut v_x_4669_: *mut LeanObject,
    mut v_prec_4670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4671_: *mut LeanObject = core::ptr::null_mut();
    v___x_4671_ = l_Lean_instReprModuleArtifacts_repr___redArg(v_x_4669_);
    return v___x_4671_;
}
pub unsafe fn l_Lean_instReprModuleArtifacts_repr___boxed(
    mut v_x_4672_: *mut LeanObject,
    mut v_prec_4673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4674_: *mut LeanObject = core::ptr::null_mut();
    v_res_4674_ = l_Lean_instReprModuleArtifacts_repr(v_x_4672_, v_prec_4673_);
    lean_dec(v_prec_4673_);
    return v_res_4674_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(
    mut v_k_4681_: *mut LeanObject,
    mut v_x_4682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4687_: u8 = 0;
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4682_) == 0 {
                    lean_dec_ref(v_k_4681_);
                    v___x_4683_ = lean_box(0);
                    return v___x_4683_;
                } else {
                    v_val_4684_ = lean_ctor_get(v_x_4682_, 0);
                    v_isSharedCheck_4694_ = (!lean_is_exclusive(v_x_4682_)) as u8;
                    if v_isSharedCheck_4694_ == 0 {
                        v___x_4686_ = v_x_4682_;
                        v_isShared_4687_ = v_isSharedCheck_4694_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_4684_);
                        lean_dec(v_x_4682_);
                        v___x_4686_ = lean_box(0);
                        v_isShared_4687_ = v_isSharedCheck_4694_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4687_ == 0 {
                    lean_ctor_set_tag(v___x_4686_, 3);
                    v___x_4689_ = v___x_4686_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4693_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_val_4684_);
                    v___x_4689_ = v_reuseFailAlloc_4693_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4690_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4690_, 0, v_k_4681_);
                lean_ctor_set(v___x_4690_, 1, v___x_4689_);
                v___x_4691_ = lean_box(0);
                v___x_4692_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4692_, 0, v___x_4690_);
                lean_ctor_set(v___x_4692_, 1, v___x_4691_);
                return v___x_4692_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instToJsonModuleArtifacts_toJson(
    mut v_x_4703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lean_x3f_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_olean_x3f_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_oleanServer_x3f_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_oleanPrivate_x3f_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ilean_x3f_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ir_x3f_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_x3f_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bc_x3f_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut LeanObject = core::ptr::null_mut();
    v_lean_x3f_4704_ = lean_ctor_get(v_x_4703_, 0);
    lean_inc(v_lean_x3f_4704_);
    v_olean_x3f_4705_ = lean_ctor_get(v_x_4703_, 1);
    lean_inc(v_olean_x3f_4705_);
    v_oleanServer_x3f_4706_ = lean_ctor_get(v_x_4703_, 2);
    lean_inc(v_oleanServer_x3f_4706_);
    v_oleanPrivate_x3f_4707_ = lean_ctor_get(v_x_4703_, 3);
    lean_inc(v_oleanPrivate_x3f_4707_);
    v_ilean_x3f_4708_ = lean_ctor_get(v_x_4703_, 4);
    lean_inc(v_ilean_x3f_4708_);
    v_ir_x3f_4709_ = lean_ctor_get(v_x_4703_, 5);
    lean_inc(v_ir_x3f_4709_);
    v_c_x3f_4710_ = lean_ctor_get(v_x_4703_, 6);
    lean_inc(v_c_x3f_4710_);
    v_bc_x3f_4711_ = lean_ctor_get(v_x_4703_, 7);
    lean_inc(v_bc_x3f_4711_);
    lean_dec_ref(v_x_4703_);
    v___x_4712_ = l_Lean_instToJsonModuleArtifacts_toJson___closed__0;
    v___x_4713_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(
        v___x_4712_,
        v_lean_x3f_4704_,
    );
    v___x_4714_ = l_Lean_instToJsonModuleArtifacts_toJson___closed__1;
    v___x_4715_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(
        v___x_4714_,
        v_olean_x3f_4705_,
    );
    v___x_4716_ = l_Lean_instToJsonModuleArtifacts_toJson___closed__2;
    v___x_4717_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(
        v___x_4716_,
        v_oleanServer_x3f_4706_,
    );
    v___x_4718_ = l_Lean_instToJsonModuleArtifacts_toJson___closed__3;
    v___x_4719_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(
        v___x_4718_,
        v_oleanPrivate_x3f_4707_,
    );
    v___x_4720_ = l_Lean_instToJsonModuleArtifacts_toJson___closed__4;
    v___x_4721_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(
        v___x_4720_,
        v_ilean_x3f_4708_,
    );
    v___x_4722_ = l_Lean_instToJsonModuleArtifacts_toJson___closed__5;
    v___x_4723_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(
        v___x_4722_,
        v_ir_x3f_4709_,
    );
    v___x_4724_ = l_Lean_instToJsonModuleArtifacts_toJson___closed__6;
    v___x_4725_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(
        v___x_4724_,
        v_c_x3f_4710_,
    );
    v___x_4726_ = l_Lean_instToJsonModuleArtifacts_toJson___closed__7;
    v___x_4727_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleArtifacts_toJson_spec__0(
        v___x_4726_,
        v_bc_x3f_4711_,
    );
    v___x_4728_ = lean_box(0);
    v___x_4729_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4729_, 0, v___x_4727_);
    lean_ctor_set(v___x_4729_, 1, v___x_4728_);
    v___x_4730_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4730_, 0, v___x_4725_);
    lean_ctor_set(v___x_4730_, 1, v___x_4729_);
    v___x_4731_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4731_, 0, v___x_4723_);
    lean_ctor_set(v___x_4731_, 1, v___x_4730_);
    v___x_4732_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4732_, 0, v___x_4721_);
    lean_ctor_set(v___x_4732_, 1, v___x_4731_);
    v___x_4733_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4733_, 0, v___x_4719_);
    lean_ctor_set(v___x_4733_, 1, v___x_4732_);
    v___x_4734_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4734_, 0, v___x_4717_);
    lean_ctor_set(v___x_4734_, 1, v___x_4733_);
    v___x_4735_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4735_, 0, v___x_4715_);
    lean_ctor_set(v___x_4735_, 1, v___x_4734_);
    v___x_4736_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4736_, 0, v___x_4713_);
    lean_ctor_set(v___x_4736_, 1, v___x_4735_);
    v___x_4737_ = l_Lean_instToJsonImport_toJson___closed__0;
    v___x_4738_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(v___x_4736_, v___x_4737_);
    v___x_4739_ = l_Lean_Json_mkObj(v___x_4738_);
    lean_dec(v___x_4738_);
    return v___x_4739_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0(
    mut v_x_4744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4750_: u8 = 0;
    let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4754_: u8 = 0;
    let mut v_a_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4758_: u8 = 0;
    let mut v___x_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4763_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4744_) == 0 {
                    v___x_4745_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0___closed__0;
                    return v___x_4745_;
                } else {
                    v___x_4746_ = l_Lean_Json_getStr_x3f(v_x_4744_);
                    if lean_obj_tag(v___x_4746_) == 0 {
                        v_a_4747_ = lean_ctor_get(v___x_4746_, 0);
                        v_isSharedCheck_4754_ = (!lean_is_exclusive(v___x_4746_)) as u8;
                        if v_isSharedCheck_4754_ == 0 {
                            v___x_4749_ = v___x_4746_;
                            v_isShared_4750_ = v_isSharedCheck_4754_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4747_);
                            lean_dec(v___x_4746_);
                            v___x_4749_ = lean_box(0);
                            v_isShared_4750_ = v_isSharedCheck_4754_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4755_ = lean_ctor_get(v___x_4746_, 0);
                        v_isSharedCheck_4763_ = (!lean_is_exclusive(v___x_4746_)) as u8;
                        if v_isSharedCheck_4763_ == 0 {
                            v___x_4757_ = v___x_4746_;
                            v_isShared_4758_ = v_isSharedCheck_4763_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4755_);
                            lean_dec(v___x_4746_);
                            v___x_4757_ = lean_box(0);
                            v_isShared_4758_ = v_isSharedCheck_4763_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4750_ == 0 {
                    v___x_4752_ = v___x_4749_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4753_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4753_, 0, v_a_4747_);
                    v___x_4752_ = v_reuseFailAlloc_4753_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4752_;
            }
            3 => {
                v___x_4759_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4759_, 0, v_a_4755_);
                if v_isShared_4758_ == 0 {
                    lean_ctor_set(v___x_4757_, 0, v___x_4759_);
                    v___x_4761_ = v___x_4757_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4762_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4762_, 0, v___x_4759_);
                    v___x_4761_ = v_reuseFailAlloc_4762_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4761_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(
    mut v_j_4764_: *mut LeanObject,
    mut v_k_4765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
    v___x_4766_ = l_Lean_Json_getObjValD(v_j_4764_, v_k_4765_);
    v___x_4767_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0(v___x_4766_);
    return v___x_4767_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0___boxed(
    mut v_j_4768_: *mut LeanObject,
    mut v_k_4769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4770_: *mut LeanObject = core::ptr::null_mut();
    v_res_4770_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(
            v_j_4768_, v_k_4769_,
        );
    lean_dec_ref(v_k_4769_);
    return v_res_4770_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2() -> *mut LeanObject {
    let mut v___x_4775_: u8 = 0;
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    v___x_4775_ = 1;
    v___x_4776_ = l_Lean_instFromJsonModuleArtifacts_fromJson___closed__1;
    v___x_4777_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4776_, v___x_4775_);
    return v___x_4777_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3() -> *mut LeanObject {
    let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut LeanObject = core::ptr::null_mut();
    v___x_4778_ = l_Lean_instFromJsonImport_fromJson___closed__4;
    v___x_4779_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__2,
    );
    v___x_4780_ = lean_string_append(v___x_4779_, v___x_4778_);
    return v___x_4780_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5() -> *mut LeanObject {
    let mut v___x_4783_: u8 = 0;
    let mut v___x_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
    v___x_4783_ = 1;
    v___x_4784_ = l_Lean_instFromJsonModuleArtifacts_fromJson___closed__4;
    v___x_4785_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4784_, v___x_4783_);
    return v___x_4785_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6() -> *mut LeanObject {
    let mut v___x_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut LeanObject = core::ptr::null_mut();
    v___x_4786_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__5,
    );
    v___x_4787_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3,
    );
    v___x_4788_ = lean_string_append(v___x_4787_, v___x_4786_);
    return v___x_4788_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7() -> *mut LeanObject {
    let mut v___x_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    v___x_4789_ = l_Lean_instFromJsonImport_fromJson___closed__9;
    v___x_4790_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__6,
    );
    v___x_4791_ = lean_string_append(v___x_4790_, v___x_4789_);
    return v___x_4791_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9() -> *mut LeanObject {
    let mut v___x_4794_: u8 = 0;
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    v___x_4794_ = 1;
    v___x_4795_ = l_Lean_instFromJsonModuleArtifacts_fromJson___closed__8;
    v___x_4796_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4795_, v___x_4794_);
    return v___x_4796_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10() -> *mut LeanObject {
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut LeanObject = core::ptr::null_mut();
    v___x_4797_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__9,
    );
    v___x_4798_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3,
    );
    v___x_4799_ = lean_string_append(v___x_4798_, v___x_4797_);
    return v___x_4799_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11() -> *mut LeanObject {
    let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut LeanObject = core::ptr::null_mut();
    v___x_4800_ = l_Lean_instFromJsonImport_fromJson___closed__9;
    v___x_4801_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__10,
    );
    v___x_4802_ = lean_string_append(v___x_4801_, v___x_4800_);
    return v___x_4802_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13() -> *mut LeanObject {
    let mut v___x_4805_: u8 = 0;
    let mut v___x_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
    v___x_4805_ = 1;
    v___x_4806_ = l_Lean_instFromJsonModuleArtifacts_fromJson___closed__12;
    v___x_4807_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4806_, v___x_4805_);
    return v___x_4807_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14() -> *mut LeanObject {
    let mut v___x_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut LeanObject = core::ptr::null_mut();
    v___x_4808_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__13,
    );
    v___x_4809_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3,
    );
    v___x_4810_ = lean_string_append(v___x_4809_, v___x_4808_);
    return v___x_4810_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15() -> *mut LeanObject {
    let mut v___x_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    v___x_4811_ = l_Lean_instFromJsonImport_fromJson___closed__9;
    v___x_4812_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__14,
    );
    v___x_4813_ = lean_string_append(v___x_4812_, v___x_4811_);
    return v___x_4813_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17() -> *mut LeanObject {
    let mut v___x_4816_: u8 = 0;
    let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    v___x_4816_ = 1;
    v___x_4817_ = l_Lean_instFromJsonModuleArtifacts_fromJson___closed__16;
    v___x_4818_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4817_, v___x_4816_);
    return v___x_4818_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18() -> *mut LeanObject {
    let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
    v___x_4819_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__17,
    );
    v___x_4820_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3,
    );
    v___x_4821_ = lean_string_append(v___x_4820_, v___x_4819_);
    return v___x_4821_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19() -> *mut LeanObject {
    let mut v___x_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut LeanObject = core::ptr::null_mut();
    v___x_4822_ = l_Lean_instFromJsonImport_fromJson___closed__9;
    v___x_4823_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__18,
    );
    v___x_4824_ = lean_string_append(v___x_4823_, v___x_4822_);
    return v___x_4824_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21() -> *mut LeanObject {
    let mut v___x_4827_: u8 = 0;
    let mut v___x_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut LeanObject = core::ptr::null_mut();
    v___x_4827_ = 1;
    v___x_4828_ = l_Lean_instFromJsonModuleArtifacts_fromJson___closed__20;
    v___x_4829_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4828_, v___x_4827_);
    return v___x_4829_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22() -> *mut LeanObject {
    let mut v___x_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
    v___x_4830_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__21,
    );
    v___x_4831_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3,
    );
    v___x_4832_ = lean_string_append(v___x_4831_, v___x_4830_);
    return v___x_4832_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23() -> *mut LeanObject {
    let mut v___x_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut LeanObject = core::ptr::null_mut();
    v___x_4833_ = l_Lean_instFromJsonImport_fromJson___closed__9;
    v___x_4834_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__22,
    );
    v___x_4835_ = lean_string_append(v___x_4834_, v___x_4833_);
    return v___x_4835_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25() -> *mut LeanObject {
    let mut v___x_4838_: u8 = 0;
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
    v___x_4838_ = 1;
    v___x_4839_ = l_Lean_instFromJsonModuleArtifacts_fromJson___closed__24;
    v___x_4840_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4839_, v___x_4838_);
    return v___x_4840_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26() -> *mut LeanObject {
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
    v___x_4841_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__25,
    );
    v___x_4842_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3,
    );
    v___x_4843_ = lean_string_append(v___x_4842_, v___x_4841_);
    return v___x_4843_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27() -> *mut LeanObject {
    let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
    v___x_4844_ = l_Lean_instFromJsonImport_fromJson___closed__9;
    v___x_4845_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__26,
    );
    v___x_4846_ = lean_string_append(v___x_4845_, v___x_4844_);
    return v___x_4846_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29() -> *mut LeanObject {
    let mut v___x_4849_: u8 = 0;
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    v___x_4849_ = 1;
    v___x_4850_ = l_Lean_instFromJsonModuleArtifacts_fromJson___closed__28;
    v___x_4851_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4850_, v___x_4849_);
    return v___x_4851_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30() -> *mut LeanObject {
    let mut v___x_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    v___x_4852_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__29,
    );
    v___x_4853_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3,
    );
    v___x_4854_ = lean_string_append(v___x_4853_, v___x_4852_);
    return v___x_4854_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31() -> *mut LeanObject {
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    v___x_4855_ = l_Lean_instFromJsonImport_fromJson___closed__9;
    v___x_4856_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__30,
    );
    v___x_4857_ = lean_string_append(v___x_4856_, v___x_4855_);
    return v___x_4857_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33() -> *mut LeanObject {
    let mut v___x_4860_: u8 = 0;
    let mut v___x_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    v___x_4860_ = 1;
    v___x_4861_ = l_Lean_instFromJsonModuleArtifacts_fromJson___closed__32;
    v___x_4862_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4861_, v___x_4860_);
    return v___x_4862_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34() -> *mut LeanObject {
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    v___x_4863_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__33,
    );
    v___x_4864_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__3,
    );
    v___x_4865_ = lean_string_append(v___x_4864_, v___x_4863_);
    return v___x_4865_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35() -> *mut LeanObject {
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    v___x_4866_ = l_Lean_instFromJsonImport_fromJson___closed__9;
    v___x_4867_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34_once),
        _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__34,
    );
    v___x_4868_ = lean_string_append(v___x_4867_, v___x_4866_);
    return v___x_4868_;
}
pub unsafe fn l_Lean_instFromJsonModuleArtifacts_fromJson(
    mut v_json_4869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4875_: u8 = 0;
    let mut v___x_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4881_: u8 = 0;
    let mut v_a_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4885_: u8 = 0;
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4889_: u8 = 0;
    let mut v_a_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4896_: u8 = 0;
    let mut v___x_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4902_: u8 = 0;
    let mut v_a_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4906_: u8 = 0;
    let mut v___x_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4910_: u8 = 0;
    let mut v_a_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4917_: u8 = 0;
    let mut v___x_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4923_: u8 = 0;
    let mut v_a_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4927_: u8 = 0;
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4931_: u8 = 0;
    let mut v_a_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4938_: u8 = 0;
    let mut v___x_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4944_: u8 = 0;
    let mut v_a_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4948_: u8 = 0;
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4952_: u8 = 0;
    let mut v_a_4953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4959_: u8 = 0;
    let mut v___x_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4965_: u8 = 0;
    let mut v_a_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4969_: u8 = 0;
    let mut v___x_4971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4973_: u8 = 0;
    let mut v_a_4974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4980_: u8 = 0;
    let mut v___x_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4986_: u8 = 0;
    let mut v_a_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4990_: u8 = 0;
    let mut v___x_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4994_: u8 = 0;
    let mut v_a_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5001_: u8 = 0;
    let mut v___x_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5007_: u8 = 0;
    let mut v_a_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5011_: u8 = 0;
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5015_: u8 = 0;
    let mut v_a_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5022_: u8 = 0;
    let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5028_: u8 = 0;
    let mut v_a_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5032_: u8 = 0;
    let mut v___x_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5036_: u8 = 0;
    let mut v_a_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5040_: u8 = 0;
    let mut v___x_5041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5045_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4870_ = l_Lean_instToJsonModuleArtifacts_toJson___closed__0;
                lean_inc(v_json_4869_);
                v___x_4871_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_4869_, v___x_4870_);
                if lean_obj_tag(v___x_4871_) == 0 {
                    lean_dec(v_json_4869_);
                    v_a_4872_ = lean_ctor_get(v___x_4871_, 0);
                    v_isSharedCheck_4881_ = (!lean_is_exclusive(v___x_4871_)) as u8;
                    if v_isSharedCheck_4881_ == 0 {
                        v___x_4874_ = v___x_4871_;
                        v_isShared_4875_ = v_isSharedCheck_4881_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4872_);
                        lean_dec(v___x_4871_);
                        v___x_4874_ = lean_box(0);
                        v_isShared_4875_ = v_isSharedCheck_4881_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_4871_) == 0 {
                        lean_dec(v_json_4869_);
                        v_a_4882_ = lean_ctor_get(v___x_4871_, 0);
                        v_isSharedCheck_4889_ = (!lean_is_exclusive(v___x_4871_)) as u8;
                        if v_isSharedCheck_4889_ == 0 {
                            v___x_4884_ = v___x_4871_;
                            v_isShared_4885_ = v_isSharedCheck_4889_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4882_);
                            lean_dec(v___x_4871_);
                            v___x_4884_ = lean_box(0);
                            v_isShared_4885_ = v_isSharedCheck_4889_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4890_ = lean_ctor_get(v___x_4871_, 0);
                        lean_inc(v_a_4890_);
                        lean_dec_ref_known(v___x_4871_, 1);
                        v___x_4891_ = l_Lean_instToJsonModuleArtifacts_toJson___closed__1;
                        lean_inc(v_json_4869_);
                        v___x_4892_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_4869_, v___x_4891_);
                        if lean_obj_tag(v___x_4892_) == 0 {
                            lean_dec(v_a_4890_);
                            lean_dec(v_json_4869_);
                            v_a_4893_ = lean_ctor_get(v___x_4892_, 0);
                            v_isSharedCheck_4902_ = (!lean_is_exclusive(v___x_4892_)) as u8;
                            if v_isSharedCheck_4902_ == 0 {
                                v___x_4895_ = v___x_4892_;
                                v_isShared_4896_ = v_isSharedCheck_4902_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_4893_);
                                lean_dec(v___x_4892_);
                                v___x_4895_ = lean_box(0);
                                v_isShared_4896_ = v_isSharedCheck_4902_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_4892_) == 0 {
                                lean_dec(v_a_4890_);
                                lean_dec(v_json_4869_);
                                v_a_4903_ = lean_ctor_get(v___x_4892_, 0);
                                v_isSharedCheck_4910_ = (!lean_is_exclusive(v___x_4892_)) as u8;
                                if v_isSharedCheck_4910_ == 0 {
                                    v___x_4905_ = v___x_4892_;
                                    v_isShared_4906_ = v_isSharedCheck_4910_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_4903_);
                                    lean_dec(v___x_4892_);
                                    v___x_4905_ = lean_box(0);
                                    v_isShared_4906_ = v_isSharedCheck_4910_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_4911_ = lean_ctor_get(v___x_4892_, 0);
                                lean_inc(v_a_4911_);
                                lean_dec_ref_known(v___x_4892_, 1);
                                v___x_4912_ = l_Lean_instToJsonModuleArtifacts_toJson___closed__2;
                                lean_inc(v_json_4869_);
                                v___x_4913_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_4869_, v___x_4912_);
                                if lean_obj_tag(v___x_4913_) == 0 {
                                    lean_dec(v_a_4911_);
                                    lean_dec(v_a_4890_);
                                    lean_dec(v_json_4869_);
                                    v_a_4914_ = lean_ctor_get(v___x_4913_, 0);
                                    v_isSharedCheck_4923_ = (!lean_is_exclusive(v___x_4913_)) as u8;
                                    if v_isSharedCheck_4923_ == 0 {
                                        v___x_4916_ = v___x_4913_;
                                        v_isShared_4917_ = v_isSharedCheck_4923_;
                                        state = 9;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4914_);
                                        lean_dec(v___x_4913_);
                                        v___x_4916_ = lean_box(0);
                                        v_isShared_4917_ = v_isSharedCheck_4923_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if lean_obj_tag(v___x_4913_) == 0 {
                                        lean_dec(v_a_4911_);
                                        lean_dec(v_a_4890_);
                                        lean_dec(v_json_4869_);
                                        v_a_4924_ = lean_ctor_get(v___x_4913_, 0);
                                        v_isSharedCheck_4931_ =
                                            (!lean_is_exclusive(v___x_4913_)) as u8;
                                        if v_isSharedCheck_4931_ == 0 {
                                            v___x_4926_ = v___x_4913_;
                                            v_isShared_4927_ = v_isSharedCheck_4931_;
                                            state = 11;
                                            continue;
                                        } else {
                                            lean_inc(v_a_4924_);
                                            lean_dec(v___x_4913_);
                                            v___x_4926_ = lean_box(0);
                                            v_isShared_4927_ = v_isSharedCheck_4931_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_4932_ = lean_ctor_get(v___x_4913_, 0);
                                        lean_inc(v_a_4932_);
                                        lean_dec_ref_known(v___x_4913_, 1);
                                        v___x_4933_ =
                                            l_Lean_instToJsonModuleArtifacts_toJson___closed__3;
                                        lean_inc(v_json_4869_);
                                        v___x_4934_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_4869_, v___x_4933_);
                                        if lean_obj_tag(v___x_4934_) == 0 {
                                            lean_dec(v_a_4932_);
                                            lean_dec(v_a_4911_);
                                            lean_dec(v_a_4890_);
                                            lean_dec(v_json_4869_);
                                            v_a_4935_ = lean_ctor_get(v___x_4934_, 0);
                                            v_isSharedCheck_4944_ =
                                                (!lean_is_exclusive(v___x_4934_)) as u8;
                                            if v_isSharedCheck_4944_ == 0 {
                                                v___x_4937_ = v___x_4934_;
                                                v_isShared_4938_ = v_isSharedCheck_4944_;
                                                state = 13;
                                                continue;
                                            } else {
                                                lean_inc(v_a_4935_);
                                                lean_dec(v___x_4934_);
                                                v___x_4937_ = lean_box(0);
                                                v_isShared_4938_ = v_isSharedCheck_4944_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            if lean_obj_tag(v___x_4934_) == 0 {
                                                lean_dec(v_a_4932_);
                                                lean_dec(v_a_4911_);
                                                lean_dec(v_a_4890_);
                                                lean_dec(v_json_4869_);
                                                v_a_4945_ = lean_ctor_get(v___x_4934_, 0);
                                                v_isSharedCheck_4952_ =
                                                    (!lean_is_exclusive(v___x_4934_)) as u8;
                                                if v_isSharedCheck_4952_ == 0 {
                                                    v___x_4947_ = v___x_4934_;
                                                    v_isShared_4948_ = v_isSharedCheck_4952_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_4945_);
                                                    lean_dec(v___x_4934_);
                                                    v___x_4947_ = lean_box(0);
                                                    v_isShared_4948_ = v_isSharedCheck_4952_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_4953_ = lean_ctor_get(v___x_4934_, 0);
                                                lean_inc(v_a_4953_);
                                                lean_dec_ref_known(v___x_4934_, 1);
                                                v___x_4954_ = l_Lean_instToJsonModuleArtifacts_toJson___closed__4;
                                                lean_inc(v_json_4869_);
                                                v___x_4955_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_4869_, v___x_4954_);
                                                if lean_obj_tag(v___x_4955_) == 0 {
                                                    lean_dec(v_a_4953_);
                                                    lean_dec(v_a_4932_);
                                                    lean_dec(v_a_4911_);
                                                    lean_dec(v_a_4890_);
                                                    lean_dec(v_json_4869_);
                                                    v_a_4956_ = lean_ctor_get(v___x_4955_, 0);
                                                    v_isSharedCheck_4965_ =
                                                        (!lean_is_exclusive(v___x_4955_)) as u8;
                                                    if v_isSharedCheck_4965_ == 0 {
                                                        v___x_4958_ = v___x_4955_;
                                                        v_isShared_4959_ = v_isSharedCheck_4965_;
                                                        state = 17;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_4956_);
                                                        lean_dec(v___x_4955_);
                                                        v___x_4958_ = lean_box(0);
                                                        v_isShared_4959_ = v_isSharedCheck_4965_;
                                                        state = 17;
                                                        continue;
                                                    }
                                                } else {
                                                    if lean_obj_tag(v___x_4955_) == 0 {
                                                        lean_dec(v_a_4953_);
                                                        lean_dec(v_a_4932_);
                                                        lean_dec(v_a_4911_);
                                                        lean_dec(v_a_4890_);
                                                        lean_dec(v_json_4869_);
                                                        v_a_4966_ = lean_ctor_get(v___x_4955_, 0);
                                                        v_isSharedCheck_4973_ =
                                                            (!lean_is_exclusive(v___x_4955_)) as u8;
                                                        if v_isSharedCheck_4973_ == 0 {
                                                            v___x_4968_ = v___x_4955_;
                                                            v_isShared_4969_ =
                                                                v_isSharedCheck_4973_;
                                                            state = 19;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_4966_);
                                                            lean_dec(v___x_4955_);
                                                            v___x_4968_ = lean_box(0);
                                                            v_isShared_4969_ =
                                                                v_isSharedCheck_4973_;
                                                            state = 19;
                                                            continue;
                                                        }
                                                    } else {
                                                        v_a_4974_ = lean_ctor_get(v___x_4955_, 0);
                                                        lean_inc(v_a_4974_);
                                                        lean_dec_ref_known(v___x_4955_, 1);
                                                        v___x_4975_ = l_Lean_instToJsonModuleArtifacts_toJson___closed__5;
                                                        lean_inc(v_json_4869_);
                                                        v___x_4976_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_4869_, v___x_4975_);
                                                        if lean_obj_tag(v___x_4976_) == 0 {
                                                            lean_dec(v_a_4974_);
                                                            lean_dec(v_a_4953_);
                                                            lean_dec(v_a_4932_);
                                                            lean_dec(v_a_4911_);
                                                            lean_dec(v_a_4890_);
                                                            lean_dec(v_json_4869_);
                                                            v_a_4977_ =
                                                                lean_ctor_get(v___x_4976_, 0);
                                                            v_isSharedCheck_4986_ =
                                                                (!lean_is_exclusive(v___x_4976_))
                                                                    as u8;
                                                            if v_isSharedCheck_4986_ == 0 {
                                                                v___x_4979_ = v___x_4976_;
                                                                v_isShared_4980_ =
                                                                    v_isSharedCheck_4986_;
                                                                state = 21;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_4977_);
                                                                lean_dec(v___x_4976_);
                                                                v___x_4979_ = lean_box(0);
                                                                v_isShared_4980_ =
                                                                    v_isSharedCheck_4986_;
                                                                state = 21;
                                                                continue;
                                                            }
                                                        } else {
                                                            if lean_obj_tag(v___x_4976_) == 0 {
                                                                lean_dec(v_a_4974_);
                                                                lean_dec(v_a_4953_);
                                                                lean_dec(v_a_4932_);
                                                                lean_dec(v_a_4911_);
                                                                lean_dec(v_a_4890_);
                                                                lean_dec(v_json_4869_);
                                                                v_a_4987_ =
                                                                    lean_ctor_get(v___x_4976_, 0);
                                                                v_isSharedCheck_4994_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_4976_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_4994_ == 0 {
                                                                    v___x_4989_ = v___x_4976_;
                                                                    v_isShared_4990_ =
                                                                        v_isSharedCheck_4994_;
                                                                    state = 23;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_4987_);
                                                                    lean_dec(v___x_4976_);
                                                                    v___x_4989_ = lean_box(0);
                                                                    v_isShared_4990_ =
                                                                        v_isSharedCheck_4994_;
                                                                    state = 23;
                                                                    continue;
                                                                }
                                                            } else {
                                                                v_a_4995_ =
                                                                    lean_ctor_get(v___x_4976_, 0);
                                                                lean_inc(v_a_4995_);
                                                                lean_dec_ref_known(v___x_4976_, 1);
                                                                v___x_4996_ = l_Lean_instToJsonModuleArtifacts_toJson___closed__6;
                                                                lean_inc(v_json_4869_);
                                                                v___x_4997_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_4869_, v___x_4996_);
                                                                if lean_obj_tag(v___x_4997_) == 0 {
                                                                    lean_dec(v_a_4995_);
                                                                    lean_dec(v_a_4974_);
                                                                    lean_dec(v_a_4953_);
                                                                    lean_dec(v_a_4932_);
                                                                    lean_dec(v_a_4911_);
                                                                    lean_dec(v_a_4890_);
                                                                    lean_dec(v_json_4869_);
                                                                    v_a_4998_ = lean_ctor_get(
                                                                        v___x_4997_,
                                                                        0,
                                                                    );
                                                                    v_isSharedCheck_5007_ =
                                                                        (!lean_is_exclusive(
                                                                            v___x_4997_,
                                                                        ))
                                                                            as u8;
                                                                    if v_isSharedCheck_5007_ == 0 {
                                                                        v___x_5000_ = v___x_4997_;
                                                                        v_isShared_5001_ =
                                                                            v_isSharedCheck_5007_;
                                                                        state = 25;
                                                                        continue;
                                                                    } else {
                                                                        lean_inc(v_a_4998_);
                                                                        lean_dec(v___x_4997_);
                                                                        v___x_5000_ = lean_box(0);
                                                                        v_isShared_5001_ =
                                                                            v_isSharedCheck_5007_;
                                                                        state = 25;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    if lean_obj_tag(v___x_4997_)
                                                                        == 0
                                                                    {
                                                                        lean_dec(v_a_4995_);
                                                                        lean_dec(v_a_4974_);
                                                                        lean_dec(v_a_4953_);
                                                                        lean_dec(v_a_4932_);
                                                                        lean_dec(v_a_4911_);
                                                                        lean_dec(v_a_4890_);
                                                                        lean_dec(v_json_4869_);
                                                                        v_a_5008_ = lean_ctor_get(
                                                                            v___x_4997_,
                                                                            0,
                                                                        );
                                                                        v_isSharedCheck_5015_ =
                                                                            (!lean_is_exclusive(
                                                                                v___x_4997_,
                                                                            ))
                                                                                as u8;
                                                                        if v_isSharedCheck_5015_
                                                                            == 0
                                                                        {
                                                                            v___x_5010_ =
                                                                                v___x_4997_;
                                                                            v_isShared_5011_ = v_isSharedCheck_5015_;
                                                                            state = 27;
                                                                            continue;
                                                                        } else {
                                                                            lean_inc(v_a_5008_);
                                                                            lean_dec(v___x_4997_);
                                                                            v___x_5010_ =
                                                                                lean_box(0);
                                                                            v_isShared_5011_ = v_isSharedCheck_5015_;
                                                                            state = 27;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        v_a_5016_ = lean_ctor_get(
                                                                            v___x_4997_,
                                                                            0,
                                                                        );
                                                                        lean_inc(v_a_5016_);
                                                                        lean_dec_ref_known(
                                                                            v___x_4997_,
                                                                            1,
                                                                        );
                                                                        v___x_5017_ = l_Lean_instToJsonModuleArtifacts_toJson___closed__7;
                                                                        v___x_5018_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0(v_json_4869_, v___x_5017_);
                                                                        if lean_obj_tag(v___x_5018_)
                                                                            == 0
                                                                        {
                                                                            lean_dec(v_a_5016_);
                                                                            lean_dec(v_a_4995_);
                                                                            lean_dec(v_a_4974_);
                                                                            lean_dec(v_a_4953_);
                                                                            lean_dec(v_a_4932_);
                                                                            lean_dec(v_a_4911_);
                                                                            lean_dec(v_a_4890_);
                                                                            v_a_5019_ =
                                                                                lean_ctor_get(
                                                                                    v___x_5018_,
                                                                                    0,
                                                                                );
                                                                            v_isSharedCheck_5028_ =
                                                                                (!lean_is_exclusive(
                                                                                    v___x_5018_,
                                                                                ))
                                                                                    as u8;
                                                                            if v_isSharedCheck_5028_
                                                                                == 0
                                                                            {
                                                                                v___x_5021_ =
                                                                                    v___x_5018_;
                                                                                v_isShared_5022_ = v_isSharedCheck_5028_;
                                                                                state = 29;
                                                                                continue;
                                                                            } else {
                                                                                lean_inc(v_a_5019_);
                                                                                lean_dec(
                                                                                    v___x_5018_,
                                                                                );
                                                                                v___x_5021_ =
                                                                                    lean_box(0);
                                                                                v_isShared_5022_ = v_isSharedCheck_5028_;
                                                                                state = 29;
                                                                                continue;
                                                                            }
                                                                        } else {
                                                                            if lean_obj_tag(
                                                                                v___x_5018_,
                                                                            ) == 0
                                                                            {
                                                                                lean_dec(v_a_5016_);
                                                                                lean_dec(v_a_4995_);
                                                                                lean_dec(v_a_4974_);
                                                                                lean_dec(v_a_4953_);
                                                                                lean_dec(v_a_4932_);
                                                                                lean_dec(v_a_4911_);
                                                                                lean_dec(v_a_4890_);
                                                                                v_a_5029_ =
                                                                                    lean_ctor_get(
                                                                                        v___x_5018_,
                                                                                        0,
                                                                                    );
                                                                                v_isSharedCheck_5036_ = (!lean_is_exclusive(v___x_5018_)) as u8;
                                                                                if v_isSharedCheck_5036_ == 0 {
v___x_5031_ = v___x_5018_;
v_isShared_5032_ = v_isSharedCheck_5036_;
state = 31; continue;
} else {
lean_inc(v_a_5029_);
lean_dec(v___x_5018_);
v___x_5031_ = lean_box(0);
v_isShared_5032_ = v_isSharedCheck_5036_;
state = 31; continue;
}
                                                                            } else {
                                                                                v_a_5037_ =
                                                                                    lean_ctor_get(
                                                                                        v___x_5018_,
                                                                                        0,
                                                                                    );
                                                                                v_isSharedCheck_5045_ = (!lean_is_exclusive(v___x_5018_)) as u8;
                                                                                if v_isSharedCheck_5045_ == 0 {
v___x_5039_ = v___x_5018_;
v_isShared_5040_ = v_isSharedCheck_5045_;
state = 33; continue;
} else {
lean_inc(v_a_5037_);
lean_dec(v___x_5018_);
v___x_5039_ = lean_box(0);
v_isShared_5040_ = v_isSharedCheck_5045_;
state = 33; continue;
}
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4876_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7_once
                    ),
                    _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__7,
                );
                v___x_4877_ = lean_string_append(v___x_4876_, v_a_4872_);
                lean_dec(v_a_4872_);
                if v_isShared_4875_ == 0 {
                    lean_ctor_set(v___x_4874_, 0, v___x_4877_);
                    v___x_4879_ = v___x_4874_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4880_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4880_, 0, v___x_4877_);
                    v___x_4879_ = v_reuseFailAlloc_4880_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4879_;
            }
            3 => {
                if v_isShared_4885_ == 0 {
                    lean_ctor_set_tag(v___x_4884_, 0);
                    v___x_4887_ = v___x_4884_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4888_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4888_, 0, v_a_4882_);
                    v___x_4887_ = v_reuseFailAlloc_4888_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4887_;
            }
            5 => {
                v___x_4897_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11_once
                    ),
                    _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__11,
                );
                v___x_4898_ = lean_string_append(v___x_4897_, v_a_4893_);
                lean_dec(v_a_4893_);
                if v_isShared_4896_ == 0 {
                    lean_ctor_set(v___x_4895_, 0, v___x_4898_);
                    v___x_4900_ = v___x_4895_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4901_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4901_, 0, v___x_4898_);
                    v___x_4900_ = v_reuseFailAlloc_4901_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4900_;
            }
            7 => {
                if v_isShared_4906_ == 0 {
                    lean_ctor_set_tag(v___x_4905_, 0);
                    v___x_4908_ = v___x_4905_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4909_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4909_, 0, v_a_4903_);
                    v___x_4908_ = v_reuseFailAlloc_4909_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4908_;
            }
            9 => {
                v___x_4918_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15_once
                    ),
                    _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__15,
                );
                v___x_4919_ = lean_string_append(v___x_4918_, v_a_4914_);
                lean_dec(v_a_4914_);
                if v_isShared_4917_ == 0 {
                    lean_ctor_set(v___x_4916_, 0, v___x_4919_);
                    v___x_4921_ = v___x_4916_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4922_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4922_, 0, v___x_4919_);
                    v___x_4921_ = v_reuseFailAlloc_4922_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4921_;
            }
            11 => {
                if v_isShared_4927_ == 0 {
                    lean_ctor_set_tag(v___x_4926_, 0);
                    v___x_4929_ = v___x_4926_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4930_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4930_, 0, v_a_4924_);
                    v___x_4929_ = v_reuseFailAlloc_4930_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4929_;
            }
            13 => {
                v___x_4939_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19_once
                    ),
                    _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__19,
                );
                v___x_4940_ = lean_string_append(v___x_4939_, v_a_4935_);
                lean_dec(v_a_4935_);
                if v_isShared_4938_ == 0 {
                    lean_ctor_set(v___x_4937_, 0, v___x_4940_);
                    v___x_4942_ = v___x_4937_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4943_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4943_, 0, v___x_4940_);
                    v___x_4942_ = v_reuseFailAlloc_4943_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4942_;
            }
            15 => {
                if v_isShared_4948_ == 0 {
                    lean_ctor_set_tag(v___x_4947_, 0);
                    v___x_4950_ = v___x_4947_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4951_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4951_, 0, v_a_4945_);
                    v___x_4950_ = v_reuseFailAlloc_4951_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4950_;
            }
            17 => {
                v___x_4960_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23_once
                    ),
                    _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__23,
                );
                v___x_4961_ = lean_string_append(v___x_4960_, v_a_4956_);
                lean_dec(v_a_4956_);
                if v_isShared_4959_ == 0 {
                    lean_ctor_set(v___x_4958_, 0, v___x_4961_);
                    v___x_4963_ = v___x_4958_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4964_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4964_, 0, v___x_4961_);
                    v___x_4963_ = v_reuseFailAlloc_4964_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4963_;
            }
            19 => {
                if v_isShared_4969_ == 0 {
                    lean_ctor_set_tag(v___x_4968_, 0);
                    v___x_4971_ = v___x_4968_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4972_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4972_, 0, v_a_4966_);
                    v___x_4971_ = v_reuseFailAlloc_4972_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4971_;
            }
            21 => {
                v___x_4981_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27_once
                    ),
                    _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__27,
                );
                v___x_4982_ = lean_string_append(v___x_4981_, v_a_4977_);
                lean_dec(v_a_4977_);
                if v_isShared_4980_ == 0 {
                    lean_ctor_set(v___x_4979_, 0, v___x_4982_);
                    v___x_4984_ = v___x_4979_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4985_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4985_, 0, v___x_4982_);
                    v___x_4984_ = v_reuseFailAlloc_4985_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4984_;
            }
            23 => {
                if v_isShared_4990_ == 0 {
                    lean_ctor_set_tag(v___x_4989_, 0);
                    v___x_4992_ = v___x_4989_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4993_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4993_, 0, v_a_4987_);
                    v___x_4992_ = v_reuseFailAlloc_4993_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4992_;
            }
            25 => {
                v___x_5002_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31_once
                    ),
                    _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__31,
                );
                v___x_5003_ = lean_string_append(v___x_5002_, v_a_4998_);
                lean_dec(v_a_4998_);
                if v_isShared_5001_ == 0 {
                    lean_ctor_set(v___x_5000_, 0, v___x_5003_);
                    v___x_5005_ = v___x_5000_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5006_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5006_, 0, v___x_5003_);
                    v___x_5005_ = v_reuseFailAlloc_5006_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5005_;
            }
            27 => {
                if v_isShared_5011_ == 0 {
                    lean_ctor_set_tag(v___x_5010_, 0);
                    v___x_5013_ = v___x_5010_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5014_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5014_, 0, v_a_5008_);
                    v___x_5013_ = v_reuseFailAlloc_5014_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_5013_;
            }
            29 => {
                v___x_5023_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35_once
                    ),
                    _init_l_Lean_instFromJsonModuleArtifacts_fromJson___closed__35,
                );
                v___x_5024_ = lean_string_append(v___x_5023_, v_a_5019_);
                lean_dec(v_a_5019_);
                if v_isShared_5022_ == 0 {
                    lean_ctor_set(v___x_5021_, 0, v___x_5024_);
                    v___x_5026_ = v___x_5021_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5027_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5027_, 0, v___x_5024_);
                    v___x_5026_ = v_reuseFailAlloc_5027_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_5026_;
            }
            31 => {
                if v_isShared_5032_ == 0 {
                    lean_ctor_set_tag(v___x_5031_, 0);
                    v___x_5034_ = v___x_5031_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_5035_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_a_5029_);
                    v___x_5034_ = v_reuseFailAlloc_5035_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_5034_;
            }
            33 => {
                v___x_5041_ = lean_alloc_ctor(0, 8, (0) as u32);
                lean_ctor_set(v___x_5041_, 0, v_a_4890_);
                lean_ctor_set(v___x_5041_, 1, v_a_4911_);
                lean_ctor_set(v___x_5041_, 2, v_a_4932_);
                lean_ctor_set(v___x_5041_, 3, v_a_4953_);
                lean_ctor_set(v___x_5041_, 4, v_a_4974_);
                lean_ctor_set(v___x_5041_, 5, v_a_4995_);
                lean_ctor_set(v___x_5041_, 6, v_a_5016_);
                lean_ctor_set(v___x_5041_, 7, v_a_5037_);
                if v_isShared_5040_ == 0 {
                    lean_ctor_set(v___x_5039_, 0, v___x_5041_);
                    v___x_5043_ = v___x_5039_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_5044_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5044_, 0, v___x_5041_);
                    v___x_5043_ = v_reuseFailAlloc_5044_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_5043_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ModuleArtifacts_oleanParts(
    mut v_arts_5048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_olean_x3f_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_oleanServer_x3f_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_oleanPrivate_x3f_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fnames_5052_: *mut LeanObject = core::ptr::null_mut();
    v_olean_x3f_5049_ = lean_ctor_get(v_arts_5048_, 1);
    lean_inc(v_olean_x3f_5049_);
    v_oleanServer_x3f_5050_ = lean_ctor_get(v_arts_5048_, 2);
    lean_inc(v_oleanServer_x3f_5050_);
    v_oleanPrivate_x3f_5051_ = lean_ctor_get(v_arts_5048_, 3);
    lean_inc(v_oleanPrivate_x3f_5051_);
    lean_dec_ref(v_arts_5048_);
    v_fnames_5052_ = l_Lean_ImportArtifacts_oleanParts___closed__0;
    if lean_obj_tag(v_olean_x3f_5049_) == 1 {
        let mut v_val_5053_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fnames_5054_: *mut LeanObject = core::ptr::null_mut();
        v_val_5053_ = lean_ctor_get(v_olean_x3f_5049_, 0);
        lean_inc(v_val_5053_);
        lean_dec_ref_known(v_olean_x3f_5049_, 1);
        v_fnames_5054_ = lean_array_push(v_fnames_5052_, v_val_5053_);
        if lean_obj_tag(v_oleanServer_x3f_5050_) == 1 {
            let mut v_val_5055_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fnames_5056_: *mut LeanObject = core::ptr::null_mut();
            v_val_5055_ = lean_ctor_get(v_oleanServer_x3f_5050_, 0);
            lean_inc(v_val_5055_);
            lean_dec_ref_known(v_oleanServer_x3f_5050_, 1);
            v_fnames_5056_ = lean_array_push(v_fnames_5054_, v_val_5055_);
            if lean_obj_tag(v_oleanPrivate_x3f_5051_) == 1 {
                let mut v_val_5057_: *mut LeanObject = core::ptr::null_mut();
                let mut v_fnames_5058_: *mut LeanObject = core::ptr::null_mut();
                v_val_5057_ = lean_ctor_get(v_oleanPrivate_x3f_5051_, 0);
                lean_inc(v_val_5057_);
                lean_dec_ref_known(v_oleanPrivate_x3f_5051_, 1);
                v_fnames_5058_ = lean_array_push(v_fnames_5056_, v_val_5057_);
                return v_fnames_5058_;
            } else {
                lean_dec(v_oleanPrivate_x3f_5051_);
                return v_fnames_5056_;
            }
        } else {
            lean_dec(v_oleanPrivate_x3f_5051_);
            lean_dec(v_oleanServer_x3f_5050_);
            return v_fnames_5054_;
        }
    } else {
        lean_dec(v_oleanPrivate_x3f_5051_);
        lean_dec(v_oleanServer_x3f_5050_);
        lean_dec(v_olean_x3f_5049_);
        return v_fnames_5052_;
    }
}
pub unsafe fn l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0(
    mut v_x_5059_: *mut LeanObject,
    mut v_x_5060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5065_: u8 = 0;
    let mut v___x_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5073_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5059_) == 0 {
                    v___x_5061_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__1;
                    return v___x_5061_;
                } else {
                    v_val_5062_ = lean_ctor_get(v_x_5059_, 0);
                    v_isSharedCheck_5073_ = (!lean_is_exclusive(v_x_5059_)) as u8;
                    if v_isSharedCheck_5073_ == 0 {
                        v___x_5064_ = v_x_5059_;
                        v_isShared_5065_ = v_isSharedCheck_5073_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_5062_);
                        lean_dec(v_x_5059_);
                        v___x_5064_ = lean_box(0);
                        v_isShared_5065_ = v_isSharedCheck_5073_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5066_ =
                    l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__3;
                v___x_5067_ = l_String_quote(v_val_5062_);
                if v_isShared_5065_ == 0 {
                    lean_ctor_set_tag(v___x_5064_, 3);
                    lean_ctor_set(v___x_5064_, 0, v___x_5067_);
                    v___x_5069_ = v___x_5064_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5072_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5072_, 0, v___x_5067_);
                    v___x_5069_ = v_reuseFailAlloc_5072_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5070_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5070_, 0, v___x_5066_);
                lean_ctor_set(v___x_5070_, 1, v___x_5069_);
                v___x_5071_ = l_Repr_addAppParen(v___x_5070_, v_x_5060_);
                return v___x_5071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0___boxed(
    mut v_x_5074_: *mut LeanObject,
    mut v_x_5075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5076_: *mut LeanObject = core::ptr::null_mut();
    v_res_5076_ = l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0(v_x_5074_, v_x_5075_);
    lean_dec(v_x_5075_);
    return v_res_5076_;
}
pub unsafe fn _init_l_Lean_instReprPlugin_repr___redArg___closed__4() -> *mut LeanObject {
    let mut v___x_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut LeanObject = core::ptr::null_mut();
    v___x_5086_ = lean_unsigned_to_nat(8);
    v___x_5087_ = lean_nat_to_int(v___x_5086_);
    return v___x_5087_;
}
pub unsafe fn l_Lean_instReprPlugin_repr___redArg(
    mut v_x_5091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_path_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initFn_x3f_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5096_: u8 = 0;
    let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: u8 = 0;
    let mut v___x_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5131_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_path_5092_ = lean_ctor_get(v_x_5091_, 0);
                v_initFn_x3f_5093_ = lean_ctor_get(v_x_5091_, 1);
                v_isSharedCheck_5131_ = (!lean_is_exclusive(v_x_5091_)) as u8;
                if v_isSharedCheck_5131_ == 0 {
                    v___x_5095_ = v_x_5091_;
                    v_isShared_5096_ = v_isSharedCheck_5131_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_initFn_x3f_5093_);
                    lean_inc(v_path_5092_);
                    lean_dec(v_x_5091_);
                    v___x_5095_ = lean_box(0);
                    v_isShared_5096_ = v_isSharedCheck_5131_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5097_ = l_Lean_instReprImport_repr___redArg___closed__5;
                v___x_5098_ = l_Lean_instReprPlugin_repr___redArg___closed__3;
                v___x_5099_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instReprPlugin_repr___redArg___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_instReprPlugin_repr___redArg___closed__4_once),
                    _init_l_Lean_instReprPlugin_repr___redArg___closed__4,
                );
                v___x_5100_ = lean_unsigned_to_nat(0);
                v___x_5101_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0_spec__0_spec__1_spec__2___closed__1;
                v___x_5102_ = l_String_quote(v_path_5092_);
                v___x_5103_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_5103_, 0, v___x_5102_);
                if v_isShared_5096_ == 0 {
                    lean_ctor_set_tag(v___x_5095_, 5);
                    lean_ctor_set(v___x_5095_, 1, v___x_5103_);
                    lean_ctor_set(v___x_5095_, 0, v___x_5101_);
                    v___x_5105_ = v___x_5095_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5130_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5130_, 0, v___x_5101_);
                    lean_ctor_set(v_reuseFailAlloc_5130_, 1, v___x_5103_);
                    v___x_5105_ = v_reuseFailAlloc_5130_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5106_ = l_Repr_addAppParen(v___x_5105_, v___x_5100_);
                v___x_5107_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_5107_, 0, v___x_5099_);
                lean_ctor_set(v___x_5107_, 1, v___x_5106_);
                v___x_5108_ = 0;
                v___x_5109_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_5109_, 0, v___x_5107_);
                lean_ctor_set_uint8(
                    v___x_5109_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5108_,
                );
                v___x_5110_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5110_, 0, v___x_5098_);
                lean_ctor_set(v___x_5110_, 1, v___x_5109_);
                v___x_5111_ = l_Lean_instReprImport_repr___redArg___closed__9;
                v___x_5112_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5112_, 0, v___x_5110_);
                lean_ctor_set(v___x_5112_, 1, v___x_5111_);
                v___x_5113_ = lean_box(1);
                v___x_5114_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5114_, 0, v___x_5112_);
                lean_ctor_set(v___x_5114_, 1, v___x_5113_);
                v___x_5115_ = l_Lean_instReprPlugin_repr___redArg___closed__6;
                v___x_5116_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5116_, 0, v___x_5114_);
                lean_ctor_set(v___x_5116_, 1, v___x_5115_);
                v___x_5117_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5117_, 0, v___x_5116_);
                lean_ctor_set(v___x_5117_, 1, v___x_5097_);
                v___x_5118_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instReprModuleHeader_repr___redArg___closed__4),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprModuleHeader_repr___redArg___closed__4_once
                    ),
                    _init_l_Lean_instReprModuleHeader_repr___redArg___closed__4,
                );
                v___x_5119_ = l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0(
                    v_initFn_x3f_5093_,
                    v___x_5100_,
                );
                v___x_5120_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_5120_, 0, v___x_5118_);
                lean_ctor_set(v___x_5120_, 1, v___x_5119_);
                v___x_5121_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_5121_, 0, v___x_5120_);
                lean_ctor_set_uint8(
                    v___x_5121_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5108_,
                );
                v___x_5122_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5122_, 0, v___x_5117_);
                lean_ctor_set(v___x_5122_, 1, v___x_5121_);
                v___x_5123_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__20),
                    core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__20_once),
                    _init_l_Lean_instReprImport_repr___redArg___closed__20,
                );
                v___x_5124_ = l_Lean_instReprImport_repr___redArg___closed__21;
                v___x_5125_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5125_, 0, v___x_5124_);
                lean_ctor_set(v___x_5125_, 1, v___x_5122_);
                v___x_5126_ = l_Lean_instReprImport_repr___redArg___closed__22;
                v___x_5127_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5127_, 0, v___x_5125_);
                lean_ctor_set(v___x_5127_, 1, v___x_5126_);
                v___x_5128_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_5128_, 0, v___x_5123_);
                lean_ctor_set(v___x_5128_, 1, v___x_5127_);
                v___x_5129_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_5129_, 0, v___x_5128_);
                lean_ctor_set_uint8(
                    v___x_5129_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5108_,
                );
                return v___x_5129_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instReprPlugin_repr(
    mut v_x_5132_: *mut LeanObject,
    mut v_prec_5133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5134_: *mut LeanObject = core::ptr::null_mut();
    v___x_5134_ = l_Lean_instReprPlugin_repr___redArg(v_x_5132_);
    return v___x_5134_;
}
pub unsafe fn l_Lean_instReprPlugin_repr___boxed(
    mut v_x_5135_: *mut LeanObject,
    mut v_prec_5136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5137_: *mut LeanObject = core::ptr::null_mut();
    v_res_5137_ = l_Lean_instReprPlugin_repr(v_x_5135_, v_prec_5136_);
    lean_dec(v_prec_5136_);
    return v_res_5137_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_instToJsonPlugin_toJson_spec__0(
    mut v_k_5140_: *mut LeanObject,
    mut v_x_5141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5146_: u8 = 0;
    let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5153_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5141_) == 0 {
                    lean_dec_ref(v_k_5140_);
                    v___x_5142_ = lean_box(0);
                    return v___x_5142_;
                } else {
                    v_val_5143_ = lean_ctor_get(v_x_5141_, 0);
                    v_isSharedCheck_5153_ = (!lean_is_exclusive(v_x_5141_)) as u8;
                    if v_isSharedCheck_5153_ == 0 {
                        v___x_5145_ = v_x_5141_;
                        v_isShared_5146_ = v_isSharedCheck_5153_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_5143_);
                        lean_dec(v_x_5141_);
                        v___x_5145_ = lean_box(0);
                        v_isShared_5146_ = v_isSharedCheck_5153_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5146_ == 0 {
                    lean_ctor_set_tag(v___x_5145_, 3);
                    v___x_5148_ = v___x_5145_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5152_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5152_, 0, v_val_5143_);
                    v___x_5148_ = v_reuseFailAlloc_5152_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5149_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5149_, 0, v_k_5140_);
                lean_ctor_set(v___x_5149_, 1, v___x_5148_);
                v___x_5150_ = lean_box(0);
                v___x_5151_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5151_, 0, v___x_5149_);
                lean_ctor_set(v___x_5151_, 1, v___x_5150_);
                return v___x_5151_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instToJsonPlugin_toJson(mut v_x_5155_: *mut LeanObject) -> *mut LeanObject {
    let mut v_path_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initFn_x3f_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5160_: u8 = 0;
    let mut v___x_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5175_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_path_5156_ = lean_ctor_get(v_x_5155_, 0);
                v_initFn_x3f_5157_ = lean_ctor_get(v_x_5155_, 1);
                v_isSharedCheck_5175_ = (!lean_is_exclusive(v_x_5155_)) as u8;
                if v_isSharedCheck_5175_ == 0 {
                    v___x_5159_ = v_x_5155_;
                    v_isShared_5160_ = v_isSharedCheck_5175_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_initFn_x3f_5157_);
                    lean_inc(v_path_5156_);
                    lean_dec(v_x_5155_);
                    v___x_5159_ = lean_box(0);
                    v_isShared_5160_ = v_isSharedCheck_5175_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5161_ = l_Lean_instReprPlugin_repr___redArg___closed__0;
                v___x_5162_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_5162_, 0, v_path_5156_);
                if v_isShared_5160_ == 0 {
                    lean_ctor_set(v___x_5159_, 1, v___x_5162_);
                    lean_ctor_set(v___x_5159_, 0, v___x_5161_);
                    v___x_5164_ = v___x_5159_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5174_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5174_, 0, v___x_5161_);
                    lean_ctor_set(v_reuseFailAlloc_5174_, 1, v___x_5162_);
                    v___x_5164_ = v_reuseFailAlloc_5174_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5165_ = lean_box(0);
                v___x_5166_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5166_, 0, v___x_5164_);
                lean_ctor_set(v___x_5166_, 1, v___x_5165_);
                v___x_5167_ = l_Lean_instToJsonPlugin_toJson___closed__0;
                v___x_5168_ = l_Lean_Json_opt___at___00Lean_instToJsonPlugin_toJson_spec__0(
                    v___x_5167_,
                    v_initFn_x3f_5157_,
                );
                v___x_5169_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5169_, 0, v___x_5168_);
                lean_ctor_set(v___x_5169_, 1, v___x_5165_);
                v___x_5170_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5170_, 0, v___x_5166_);
                lean_ctor_set(v___x_5170_, 1, v___x_5169_);
                v___x_5171_ = l_Lean_instToJsonImport_toJson___closed__0;
                v___x_5172_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(v___x_5170_, v___x_5171_);
                v___x_5173_ = l_Lean_Json_mkObj(v___x_5172_);
                lean_dec(v___x_5172_);
                return v___x_5173_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Plugin_ofFilePath(mut v_path_5178_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: *mut LeanObject = core::ptr::null_mut();
    v___x_5179_ = lean_box(0);
    v___x_5180_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5180_, 0, v_path_5178_);
    lean_ctor_set(v___x_5180_, 1, v___x_5179_);
    return v___x_5180_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__0(
    mut v_j_5183_: *mut LeanObject,
    mut v_k_5184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5190_: u8 = 0;
    let mut v___x_5192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5194_: u8 = 0;
    let mut v_a_5195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5198_: u8 = 0;
    let mut v___x_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5202_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5185_ = l_Lean_Json_getObjValD(v_j_5183_, v_k_5184_);
                v___x_5186_ = l_Lean_Json_getStr_x3f(v___x_5185_);
                if lean_obj_tag(v___x_5186_) == 0 {
                    v_a_5187_ = lean_ctor_get(v___x_5186_, 0);
                    v_isSharedCheck_5194_ = (!lean_is_exclusive(v___x_5186_)) as u8;
                    if v_isSharedCheck_5194_ == 0 {
                        v___x_5189_ = v___x_5186_;
                        v_isShared_5190_ = v_isSharedCheck_5194_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5187_);
                        lean_dec(v___x_5186_);
                        v___x_5189_ = lean_box(0);
                        v_isShared_5190_ = v_isSharedCheck_5194_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5195_ = lean_ctor_get(v___x_5186_, 0);
                    v_isSharedCheck_5202_ = (!lean_is_exclusive(v___x_5186_)) as u8;
                    if v_isSharedCheck_5202_ == 0 {
                        v___x_5197_ = v___x_5186_;
                        v_isShared_5198_ = v_isSharedCheck_5202_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5195_);
                        lean_dec(v___x_5186_);
                        v___x_5197_ = lean_box(0);
                        v_isShared_5198_ = v_isSharedCheck_5202_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5190_ == 0 {
                    v___x_5192_ = v___x_5189_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5193_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5193_, 0, v_a_5187_);
                    v___x_5192_ = v_reuseFailAlloc_5193_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5192_;
            }
            3 => {
                if v_isShared_5198_ == 0 {
                    v___x_5200_ = v___x_5197_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5201_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5201_, 0, v_a_5195_);
                    v___x_5200_ = v_reuseFailAlloc_5201_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5200_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__0___boxed(
    mut v_j_5203_: *mut LeanObject,
    mut v_k_5204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5205_: *mut LeanObject = core::ptr::null_mut();
    v_res_5205_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__0(v_j_5203_, v_k_5204_);
    lean_dec_ref(v_k_5204_);
    return v_res_5205_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1_spec__1(
    mut v_x_5206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5212_: u8 = 0;
    let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5216_: u8 = 0;
    let mut v_a_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5220_: u8 = 0;
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5206_) == 0 {
                    v___x_5207_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleArtifacts_fromJson_spec__0_spec__0___closed__0;
                    return v___x_5207_;
                } else {
                    v___x_5208_ = l_Lean_Json_getStr_x3f(v_x_5206_);
                    if lean_obj_tag(v___x_5208_) == 0 {
                        v_a_5209_ = lean_ctor_get(v___x_5208_, 0);
                        v_isSharedCheck_5216_ = (!lean_is_exclusive(v___x_5208_)) as u8;
                        if v_isSharedCheck_5216_ == 0 {
                            v___x_5211_ = v___x_5208_;
                            v_isShared_5212_ = v_isSharedCheck_5216_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5209_);
                            lean_dec(v___x_5208_);
                            v___x_5211_ = lean_box(0);
                            v_isShared_5212_ = v_isSharedCheck_5216_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5217_ = lean_ctor_get(v___x_5208_, 0);
                        v_isSharedCheck_5225_ = (!lean_is_exclusive(v___x_5208_)) as u8;
                        if v_isSharedCheck_5225_ == 0 {
                            v___x_5219_ = v___x_5208_;
                            v_isShared_5220_ = v_isSharedCheck_5225_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5217_);
                            lean_dec(v___x_5208_);
                            v___x_5219_ = lean_box(0);
                            v_isShared_5220_ = v_isSharedCheck_5225_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5212_ == 0 {
                    v___x_5214_ = v___x_5211_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5215_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5215_, 0, v_a_5209_);
                    v___x_5214_ = v_reuseFailAlloc_5215_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5214_;
            }
            3 => {
                v___x_5221_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5221_, 0, v_a_5217_);
                if v_isShared_5220_ == 0 {
                    lean_ctor_set(v___x_5219_, 0, v___x_5221_);
                    v___x_5223_ = v___x_5219_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5224_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5224_, 0, v___x_5221_);
                    v___x_5223_ = v_reuseFailAlloc_5224_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5223_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1(
    mut v_j_5226_: *mut LeanObject,
    mut v_k_5227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut LeanObject = core::ptr::null_mut();
    v___x_5228_ = l_Lean_Json_getObjValD(v_j_5226_, v_k_5227_);
    v___x_5229_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1_spec__1(v___x_5228_);
    return v___x_5229_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1___boxed(
    mut v_j_5230_: *mut LeanObject,
    mut v_k_5231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5232_: *mut LeanObject = core::ptr::null_mut();
    v_res_5232_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1(v_j_5230_, v_k_5231_);
    lean_dec_ref(v_k_5231_);
    return v_res_5232_;
}
pub unsafe fn l_Lean_Plugin_fromJson_x3f(mut v_data_5236_: *mut LeanObject) -> *mut LeanObject {
    let mut v_s_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5240_: u8 = 0;
    let mut v___x_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5245_: u8 = 0;
    let mut v___x_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5251_: u8 = 0;
    let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5255_: u8 = 0;
    let mut v_a_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5262_: u8 = 0;
    let mut v___x_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5266_: u8 = 0;
    let mut v_a_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5270_: u8 = 0;
    let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5275_: u8 = 0;
    let mut v___x_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match lean_obj_tag(v_data_5236_) {
                    3 => {
                        v_s_5237_ = lean_ctor_get(v_data_5236_, 0);
                        v_isSharedCheck_5245_ = (!lean_is_exclusive(v_data_5236_)) as u8;
                        if v_isSharedCheck_5245_ == 0 {
                            v___x_5239_ = v_data_5236_;
                            v_isShared_5240_ = v_isSharedCheck_5245_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_s_5237_);
                            lean_dec(v_data_5236_);
                            v___x_5239_ = lean_box(0);
                            v_isShared_5240_ = v_isSharedCheck_5245_;
                            state = 1;
                            continue;
                        }
                    }
                    5 => {
                        v___x_5246_ = l_Lean_instReprPlugin_repr___redArg___closed__0;
                        lean_inc_ref(v_data_5236_);
                        v___x_5247_ =
                            l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__0(
                                v_data_5236_,
                                v___x_5246_,
                            );
                        if lean_obj_tag(v___x_5247_) == 0 {
                            lean_dec_ref_known(v_data_5236_, 1);
                            v_a_5248_ = lean_ctor_get(v___x_5247_, 0);
                            v_isSharedCheck_5255_ = (!lean_is_exclusive(v___x_5247_)) as u8;
                            if v_isSharedCheck_5255_ == 0 {
                                v___x_5250_ = v___x_5247_;
                                v_isShared_5251_ = v_isSharedCheck_5255_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_5248_);
                                lean_dec(v___x_5247_);
                                v___x_5250_ = lean_box(0);
                                v_isShared_5251_ = v_isSharedCheck_5255_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_a_5256_ = lean_ctor_get(v___x_5247_, 0);
                            lean_inc(v_a_5256_);
                            lean_dec_ref_known(v___x_5247_, 1);
                            v___x_5257_ = l_Lean_instToJsonPlugin_toJson___closed__0;
                            v___x_5258_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1(v_data_5236_, v___x_5257_);
                            if lean_obj_tag(v___x_5258_) == 0 {
                                lean_dec(v_a_5256_);
                                v_a_5259_ = lean_ctor_get(v___x_5258_, 0);
                                v_isSharedCheck_5266_ = (!lean_is_exclusive(v___x_5258_)) as u8;
                                if v_isSharedCheck_5266_ == 0 {
                                    v___x_5261_ = v___x_5258_;
                                    v_isShared_5262_ = v_isSharedCheck_5266_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_5259_);
                                    lean_dec(v___x_5258_);
                                    v___x_5261_ = lean_box(0);
                                    v_isShared_5262_ = v_isSharedCheck_5266_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v_a_5267_ = lean_ctor_get(v___x_5258_, 0);
                                v_isSharedCheck_5275_ = (!lean_is_exclusive(v___x_5258_)) as u8;
                                if v_isSharedCheck_5275_ == 0 {
                                    v___x_5269_ = v___x_5258_;
                                    v_isShared_5270_ = v_isSharedCheck_5275_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_5267_);
                                    lean_dec(v___x_5258_);
                                    v___x_5269_ = lean_box(0);
                                    v_isShared_5270_ = v_isSharedCheck_5275_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    }
                    _ => {
                        lean_dec(v_data_5236_);
                        v___x_5276_ = l_Lean_Plugin_fromJson_x3f___closed__1;
                        return v___x_5276_;
                    }
                }
            }
            1 => {
                v___x_5241_ = l_Lean_Plugin_ofFilePath(v_s_5237_);
                if v_isShared_5240_ == 0 {
                    lean_ctor_set_tag(v___x_5239_, 1);
                    lean_ctor_set(v___x_5239_, 0, v___x_5241_);
                    v___x_5243_ = v___x_5239_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5244_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5244_, 0, v___x_5241_);
                    v___x_5243_ = v_reuseFailAlloc_5244_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5243_;
            }
            3 => {
                if v_isShared_5251_ == 0 {
                    v___x_5253_ = v___x_5250_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5254_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5254_, 0, v_a_5248_);
                    v___x_5253_ = v_reuseFailAlloc_5254_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5253_;
            }
            5 => {
                if v_isShared_5262_ == 0 {
                    v___x_5264_ = v___x_5261_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5265_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5265_, 0, v_a_5259_);
                    v___x_5264_ = v_reuseFailAlloc_5265_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5264_;
            }
            7 => {
                v___x_5271_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5271_, 0, v_a_5256_);
                lean_ctor_set(v___x_5271_, 1, v_a_5267_);
                if v_isShared_5270_ == 0 {
                    lean_ctor_set(v___x_5269_, 0, v___x_5271_);
                    v___x_5273_ = v___x_5269_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5274_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5274_, 0, v___x_5271_);
                    v___x_5273_ = v_reuseFailAlloc_5274_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5273_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2_spec__3_spec__5(
    mut v_x_5279_: *mut LeanObject,
    mut v_x_5280_: *mut LeanObject,
    mut v_x_5281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5286_: u8 = 0;
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5292_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5281_) == 0 {
                    lean_dec(v_x_5279_);
                    return v_x_5280_;
                } else {
                    v_head_5282_ = lean_ctor_get(v_x_5281_, 0);
                    v_tail_5283_ = lean_ctor_get(v_x_5281_, 1);
                    v_isSharedCheck_5292_ = (!lean_is_exclusive(v_x_5281_)) as u8;
                    if v_isSharedCheck_5292_ == 0 {
                        v___x_5285_ = v_x_5281_;
                        v_isShared_5286_ = v_isSharedCheck_5292_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5283_);
                        lean_inc(v_head_5282_);
                        lean_dec(v_x_5281_);
                        v___x_5285_ = lean_box(0);
                        v_isShared_5286_ = v_isSharedCheck_5292_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_5279_);
                if v_isShared_5286_ == 0 {
                    lean_ctor_set_tag(v___x_5285_, 5);
                    lean_ctor_set(v___x_5285_, 1, v_x_5279_);
                    lean_ctor_set(v___x_5285_, 0, v_x_5280_);
                    v___x_5288_ = v___x_5285_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5291_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5291_, 0, v_x_5280_);
                    lean_ctor_set(v_reuseFailAlloc_5291_, 1, v_x_5279_);
                    v___x_5288_ = v_reuseFailAlloc_5291_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5289_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5289_, 0, v___x_5288_);
                lean_ctor_set(v___x_5289_, 1, v_head_5282_);
                v_x_5280_ = v___x_5289_;
                v_x_5281_ = v_tail_5283_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2_spec__3(
    mut v_x_5293_: *mut LeanObject,
    mut v_x_5294_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5293_) == 0 {
        let mut v___x_5295_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_5294_);
        v___x_5295_ = lean_box(0);
        return v___x_5295_;
    } else {
        let mut v_tail_5296_: *mut LeanObject = core::ptr::null_mut();
        v_tail_5296_ = lean_ctor_get(v_x_5293_, 1);
        if lean_obj_tag(v_tail_5296_) == 0 {
            let mut v_head_5297_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_5294_);
            v_head_5297_ = lean_ctor_get(v_x_5293_, 0);
            lean_inc(v_head_5297_);
            lean_dec_ref_known(v_x_5293_, 2);
            return v_head_5297_;
        } else {
            let mut v_head_5298_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5299_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_5296_);
            v_head_5298_ = lean_ctor_get(v_x_5293_, 0);
            lean_inc(v_head_5298_);
            lean_dec_ref_known(v_x_5293_, 2);
            v___x_5299_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2_spec__3_spec__5(v_x_5294_, v_head_5298_, v_tail_5296_);
            return v___x_5299_;
        }
    }
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
    v___x_5302_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__0;
    v___x_5303_ = lean_string_length(v___x_5302_);
    return v___x_5303_;
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    v___x_5304_ = lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2_once), _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__2);
    v___x_5305_ = lean_nat_to_int(v___x_5304_);
    return v___x_5305_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(
    mut v_x_5310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5315_: u8 = 0;
    let mut v___x_5316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: u8 = 0;
    let mut v___x_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5335_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_5311_ = lean_ctor_get(v_x_5310_, 0);
                v_snd_5312_ = lean_ctor_get(v_x_5310_, 1);
                v_isSharedCheck_5335_ = (!lean_is_exclusive(v_x_5310_)) as u8;
                if v_isSharedCheck_5335_ == 0 {
                    v___x_5314_ = v_x_5310_;
                    v_isShared_5315_ = v_isSharedCheck_5335_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_5312_);
                    lean_inc(v_fst_5311_);
                    lean_dec(v_x_5310_);
                    v___x_5314_ = lean_box(0);
                    v_isShared_5315_ = v_isSharedCheck_5335_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5316_ = lean_unsigned_to_nat(0);
                v___x_5317_ = l_Lean_Name_reprPrec(v_fst_5311_, v___x_5316_);
                v___x_5318_ = lean_box(0);
                if v_isShared_5315_ == 0 {
                    lean_ctor_set_tag(v___x_5314_, 1);
                    lean_ctor_set(v___x_5314_, 1, v___x_5318_);
                    lean_ctor_set(v___x_5314_, 0, v___x_5317_);
                    v___x_5320_ = v___x_5314_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5334_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5334_, 0, v___x_5317_);
                    lean_ctor_set(v_reuseFailAlloc_5334_, 1, v___x_5318_);
                    v___x_5320_ = v_reuseFailAlloc_5334_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5321_ = l_Lean_instReprImportArtifacts_repr___redArg(v_snd_5312_);
                v___x_5322_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5322_, 0, v___x_5321_);
                lean_ctor_set(v___x_5322_, 1, v___x_5320_);
                v___x_5323_ = l_List_reverse___redArg(v___x_5322_);
                v___x_5324_ =
                    l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1;
                v___x_5325_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2_spec__3(v___x_5323_, v___x_5324_);
                v___x_5326_ = lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3_once), _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__3);
                v___x_5327_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__4;
                v___x_5328_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5328_, 0, v___x_5327_);
                lean_ctor_set(v___x_5328_, 1, v___x_5325_);
                v___x_5329_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg___closed__5;
                v___x_5330_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5330_, 0, v___x_5328_);
                lean_ctor_set(v___x_5330_, 1, v___x_5329_);
                v___x_5331_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_5331_, 0, v___x_5326_);
                lean_ctor_set(v___x_5331_, 1, v___x_5330_);
                v___x_5332_ = 0;
                v___x_5333_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_5333_, 0, v___x_5331_);
                lean_ctor_set_uint8(
                    v___x_5333_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5332_,
                );
                return v___x_5333_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3_spec__5_spec__8(
    mut v_x_5336_: *mut LeanObject,
    mut v_x_5337_: *mut LeanObject,
    mut v_x_5338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5343_: u8 = 0;
    let mut v___x_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5338_) == 0 {
                    lean_dec(v_x_5336_);
                    return v_x_5337_;
                } else {
                    v_head_5339_ = lean_ctor_get(v_x_5338_, 0);
                    v_tail_5340_ = lean_ctor_get(v_x_5338_, 1);
                    v_isSharedCheck_5350_ = (!lean_is_exclusive(v_x_5338_)) as u8;
                    if v_isSharedCheck_5350_ == 0 {
                        v___x_5342_ = v_x_5338_;
                        v_isShared_5343_ = v_isSharedCheck_5350_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5340_);
                        lean_inc(v_head_5339_);
                        lean_dec(v_x_5338_);
                        v___x_5342_ = lean_box(0);
                        v_isShared_5343_ = v_isSharedCheck_5350_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_5336_);
                if v_isShared_5343_ == 0 {
                    lean_ctor_set_tag(v___x_5342_, 5);
                    lean_ctor_set(v___x_5342_, 1, v_x_5336_);
                    lean_ctor_set(v___x_5342_, 0, v_x_5337_);
                    v___x_5345_ = v___x_5342_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5349_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5349_, 0, v_x_5337_);
                    lean_ctor_set(v_reuseFailAlloc_5349_, 1, v_x_5336_);
                    v___x_5345_ = v_reuseFailAlloc_5349_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5346_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_head_5339_);
                v___x_5347_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5347_, 0, v___x_5345_);
                lean_ctor_set(v___x_5347_, 1, v___x_5346_);
                v_x_5337_ = v___x_5347_;
                v_x_5338_ = v_tail_5340_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3_spec__5(
    mut v_x_5351_: *mut LeanObject,
    mut v_x_5352_: *mut LeanObject,
    mut v_x_5353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5358_: u8 = 0;
    let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5365_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5353_) == 0 {
                    lean_dec(v_x_5351_);
                    return v_x_5352_;
                } else {
                    v_head_5354_ = lean_ctor_get(v_x_5353_, 0);
                    v_tail_5355_ = lean_ctor_get(v_x_5353_, 1);
                    v_isSharedCheck_5365_ = (!lean_is_exclusive(v_x_5353_)) as u8;
                    if v_isSharedCheck_5365_ == 0 {
                        v___x_5357_ = v_x_5353_;
                        v_isShared_5358_ = v_isSharedCheck_5365_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5355_);
                        lean_inc(v_head_5354_);
                        lean_dec(v_x_5353_);
                        v___x_5357_ = lean_box(0);
                        v_isShared_5358_ = v_isSharedCheck_5365_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_5351_);
                if v_isShared_5358_ == 0 {
                    lean_ctor_set_tag(v___x_5357_, 5);
                    lean_ctor_set(v___x_5357_, 1, v_x_5351_);
                    lean_ctor_set(v___x_5357_, 0, v_x_5352_);
                    v___x_5360_ = v___x_5357_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5364_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_x_5352_);
                    lean_ctor_set(v_reuseFailAlloc_5364_, 1, v_x_5351_);
                    v___x_5360_ = v_reuseFailAlloc_5364_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5361_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_head_5354_);
                v___x_5362_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5362_, 0, v___x_5360_);
                lean_ctor_set(v___x_5362_, 1, v___x_5361_);
                v___x_5363_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3_spec__5_spec__8(v_x_5351_, v___x_5362_, v_tail_5355_);
                return v___x_5363_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3(
    mut v_x_5366_: *mut LeanObject,
    mut v_x_5367_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5366_) == 0 {
        let mut v___x_5368_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_5367_);
        v___x_5368_ = lean_box(0);
        return v___x_5368_;
    } else {
        let mut v_tail_5369_: *mut LeanObject = core::ptr::null_mut();
        v_tail_5369_ = lean_ctor_get(v_x_5366_, 1);
        if lean_obj_tag(v_tail_5369_) == 0 {
            let mut v_head_5370_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_5367_);
            v_head_5370_ = lean_ctor_get(v_x_5366_, 0);
            lean_inc(v_head_5370_);
            lean_dec_ref_known(v_x_5366_, 2);
            v___x_5371_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_head_5370_);
            return v___x_5371_;
        } else {
            let mut v_head_5372_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5373_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5374_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_5369_);
            v_head_5372_ = lean_ctor_get(v_x_5366_, 0);
            lean_inc(v_head_5372_);
            lean_dec_ref_known(v_x_5366_, 2);
            v___x_5373_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_head_5372_);
            v___x_5374_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3_spec__5(v_x_5367_, v___x_5373_, v_tail_5369_);
            return v___x_5374_;
        }
    }
}
pub unsafe fn _init_l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut LeanObject = core::ptr::null_mut();
    v___x_5379_ = l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__2;
    v___x_5380_ = lean_string_length(v___x_5379_);
    return v___x_5380_;
}
pub unsafe fn _init_l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    v___x_5381_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3_once
        ),
        _init_l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__3,
    );
    v___x_5382_ = lean_nat_to_int(v___x_5381_);
    return v___x_5382_;
}
pub unsafe fn l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg(
    mut v_a_5385_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_5385_) == 0 {
        let mut v___x_5386_: *mut LeanObject = core::ptr::null_mut();
        v___x_5386_ =
            l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__1;
        return v___x_5386_;
    } else {
        let mut v___x_5387_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5388_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5389_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5390_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5391_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5392_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5393_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5395_: u8 = 0;
        let mut v___x_5396_: *mut LeanObject = core::ptr::null_mut();
        v___x_5387_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1;
        v___x_5388_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__3(v_a_5385_, v___x_5387_);
        v___x_5389_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4_once), _init_l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__4);
        v___x_5390_ =
            l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg___closed__5;
        v___x_5391_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_5391_, 0, v___x_5390_);
        lean_ctor_set(v___x_5391_, 1, v___x_5388_);
        v___x_5392_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6;
        v___x_5393_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_5393_, 0, v___x_5391_);
        lean_ctor_set(v___x_5393_, 1, v___x_5392_);
        v___x_5394_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_5394_, 0, v___x_5389_);
        lean_ctor_set(v___x_5394_, 1, v___x_5393_);
        v___x_5395_ = 0;
        v___x_5396_ = lean_alloc_ctor(6, 1, (1) as u32);
        lean_ctor_set(v___x_5396_, 0, v___x_5394_);
        lean_ctor_set_uint8(
            v___x_5396_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            v___x_5395_,
        );
        return v___x_5396_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1(
    mut v_init_5397_: *mut LeanObject,
    mut v_x_5398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5398_) == 0 {
                    v_k_5399_ = lean_ctor_get(v_x_5398_, 1);
                    v_v_5400_ = lean_ctor_get(v_x_5398_, 2);
                    v_l_5401_ = lean_ctor_get(v_x_5398_, 3);
                    v_r_5402_ = lean_ctor_get(v_x_5398_, 4);
                    v___x_5403_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1(v_init_5397_, v_r_5402_);
                    lean_inc(v_v_5400_);
                    lean_inc(v_k_5399_);
                    v___x_5404_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5404_, 0, v_k_5399_);
                    lean_ctor_set(v___x_5404_, 1, v_v_5400_);
                    v___x_5405_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_5405_, 0, v___x_5404_);
                    lean_ctor_set(v___x_5405_, 1, v___x_5403_);
                    v_init_5397_ = v___x_5405_;
                    v_x_5398_ = v_l_5401_;
                    state = 0;
                    continue;
                } else {
                    return v_init_5397_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1___boxed(
    mut v_init_5407_: *mut LeanObject,
    mut v_x_5408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5409_: *mut LeanObject = core::ptr::null_mut();
    v_res_5409_ =
        l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1(
            v_init_5407_,
            v_x_5408_,
        );
    lean_dec(v_x_5408_);
    return v_res_5409_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5_spec__8_spec__11(
    mut v_x_5410_: *mut LeanObject,
    mut v_x_5411_: *mut LeanObject,
    mut v_x_5412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5417_: u8 = 0;
    let mut v___x_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5424_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5412_) == 0 {
                    lean_dec(v_x_5410_);
                    return v_x_5411_;
                } else {
                    v_head_5413_ = lean_ctor_get(v_x_5412_, 0);
                    v_tail_5414_ = lean_ctor_get(v_x_5412_, 1);
                    v_isSharedCheck_5424_ = (!lean_is_exclusive(v_x_5412_)) as u8;
                    if v_isSharedCheck_5424_ == 0 {
                        v___x_5416_ = v_x_5412_;
                        v_isShared_5417_ = v_isSharedCheck_5424_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5414_);
                        lean_inc(v_head_5413_);
                        lean_dec(v_x_5412_);
                        v___x_5416_ = lean_box(0);
                        v_isShared_5417_ = v_isSharedCheck_5424_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_5410_);
                if v_isShared_5417_ == 0 {
                    lean_ctor_set_tag(v___x_5416_, 5);
                    lean_ctor_set(v___x_5416_, 1, v_x_5410_);
                    lean_ctor_set(v___x_5416_, 0, v_x_5411_);
                    v___x_5419_ = v___x_5416_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5423_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5423_, 0, v_x_5411_);
                    lean_ctor_set(v_reuseFailAlloc_5423_, 1, v_x_5410_);
                    v___x_5419_ = v_reuseFailAlloc_5423_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5420_ = l_Lean_instReprPlugin_repr___redArg(v_head_5413_);
                v___x_5421_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5421_, 0, v___x_5419_);
                lean_ctor_set(v___x_5421_, 1, v___x_5420_);
                v_x_5411_ = v___x_5421_;
                v_x_5412_ = v_tail_5414_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5_spec__8(
    mut v_x_5425_: *mut LeanObject,
    mut v_x_5426_: *mut LeanObject,
    mut v_x_5427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5432_: u8 = 0;
    let mut v___x_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5439_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5427_) == 0 {
                    lean_dec(v_x_5425_);
                    return v_x_5426_;
                } else {
                    v_head_5428_ = lean_ctor_get(v_x_5427_, 0);
                    v_tail_5429_ = lean_ctor_get(v_x_5427_, 1);
                    v_isSharedCheck_5439_ = (!lean_is_exclusive(v_x_5427_)) as u8;
                    if v_isSharedCheck_5439_ == 0 {
                        v___x_5431_ = v_x_5427_;
                        v_isShared_5432_ = v_isSharedCheck_5439_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5429_);
                        lean_inc(v_head_5428_);
                        lean_dec(v_x_5427_);
                        v___x_5431_ = lean_box(0);
                        v_isShared_5432_ = v_isSharedCheck_5439_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_5425_);
                if v_isShared_5432_ == 0 {
                    lean_ctor_set_tag(v___x_5431_, 5);
                    lean_ctor_set(v___x_5431_, 1, v_x_5425_);
                    lean_ctor_set(v___x_5431_, 0, v_x_5426_);
                    v___x_5434_ = v___x_5431_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5438_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5438_, 0, v_x_5426_);
                    lean_ctor_set(v_reuseFailAlloc_5438_, 1, v_x_5425_);
                    v___x_5434_ = v_reuseFailAlloc_5438_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5435_ = l_Lean_instReprPlugin_repr___redArg(v_head_5428_);
                v___x_5436_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5436_, 0, v___x_5434_);
                lean_ctor_set(v___x_5436_, 1, v___x_5435_);
                v___x_5437_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5_spec__8_spec__11(v_x_5425_, v___x_5436_, v_tail_5429_);
                return v___x_5437_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5(
    mut v_x_5440_: *mut LeanObject,
    mut v_x_5441_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5440_) == 0 {
        let mut v___x_5442_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_5441_);
        v___x_5442_ = lean_box(0);
        return v___x_5442_;
    } else {
        let mut v_tail_5443_: *mut LeanObject = core::ptr::null_mut();
        v_tail_5443_ = lean_ctor_get(v_x_5440_, 1);
        if lean_obj_tag(v_tail_5443_) == 0 {
            let mut v_head_5444_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_5441_);
            v_head_5444_ = lean_ctor_get(v_x_5440_, 0);
            lean_inc(v_head_5444_);
            lean_dec_ref_known(v_x_5440_, 2);
            v___x_5445_ = l_Lean_instReprPlugin_repr___redArg(v_head_5444_);
            return v___x_5445_;
        } else {
            let mut v_head_5446_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5447_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5448_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_5443_);
            v_head_5446_ = lean_ctor_get(v_x_5440_, 0);
            lean_inc(v_head_5446_);
            lean_dec_ref_known(v_x_5440_, 2);
            v___x_5447_ = l_Lean_instReprPlugin_repr___redArg(v_head_5446_);
            v___x_5448_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5_spec__8(v_x_5441_, v___x_5447_, v_tail_5443_);
            return v___x_5448_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3(
    mut v_xs_5449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: u8 = 0;
    v___x_5450_ = lean_array_get_size(v_xs_5449_);
    v___x_5451_ = lean_unsigned_to_nat(0);
    v___x_5452_ = lean_nat_dec_eq(v___x_5450_, v___x_5451_);
    if v___x_5452_ == 0 {
        let mut v___x_5453_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5455_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5456_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5457_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5458_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5459_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5460_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5461_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5462_: *mut LeanObject = core::ptr::null_mut();
        v___x_5453_ = lean_array_to_list(v_xs_5449_);
        v___x_5454_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__1;
        v___x_5455_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3_spec__5(v___x_5453_, v___x_5454_);
        v___x_5456_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4_once
            ),
            _init_l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__4,
        );
        v___x_5457_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__5;
        v___x_5458_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_5458_, 0, v___x_5457_);
        lean_ctor_set(v___x_5458_, 1, v___x_5455_);
        v___x_5459_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__6;
        v___x_5460_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_5460_, 0, v___x_5458_);
        lean_ctor_set(v___x_5460_, 1, v___x_5459_);
        v___x_5461_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_5461_, 0, v___x_5456_);
        lean_ctor_set(v___x_5461_, 1, v___x_5460_);
        v___x_5462_ = l_Std_Format_fill(v___x_5461_);
        return v___x_5462_;
    } else {
        let mut v___x_5463_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_5449_);
        v___x_5463_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0___closed__8;
        return v___x_5463_;
    }
}
pub unsafe fn l_Option_repr___at___00Lean_instReprModuleSetup_repr_spec__0(
    mut v_x_5464_: *mut LeanObject,
    mut v_x_5465_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5464_) == 0 {
        let mut v___x_5466_: *mut LeanObject = core::ptr::null_mut();
        v___x_5466_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__1;
        return v___x_5466_;
    } else {
        let mut v_val_5467_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5468_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5469_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5470_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
        v_val_5467_ = lean_ctor_get(v_x_5464_, 0);
        lean_inc(v_val_5467_);
        lean_dec_ref_known(v_x_5464_, 1);
        v___x_5468_ = l_Option_repr___at___00Lean_instReprModuleArtifacts_repr_spec__0___closed__3;
        v___x_5469_ = l_Array_repr___at___00Lean_instReprModuleHeader_repr_spec__0(v_val_5467_);
        v___x_5470_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_5470_, 0, v___x_5468_);
        lean_ctor_set(v___x_5470_, 1, v___x_5469_);
        v___x_5471_ = l_Repr_addAppParen(v___x_5470_, v_x_5465_);
        return v___x_5471_;
    }
}
pub unsafe fn l_Option_repr___at___00Lean_instReprModuleSetup_repr_spec__0___boxed(
    mut v_x_5472_: *mut LeanObject,
    mut v_x_5473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5474_: *mut LeanObject = core::ptr::null_mut();
    v_res_5474_ =
        l_Option_repr___at___00Lean_instReprModuleSetup_repr_spec__0(v_x_5472_, v_x_5473_);
    lean_dec(v_x_5473_);
    return v_res_5474_;
}
pub unsafe fn l_Lean_instReprModuleSetup_repr___redArg(
    mut v_x_5505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_package_x3f_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_5508_: u8 = 0;
    let mut v_imports_x3f_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_importArts_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: u8 = 0;
    let mut v___x_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut LeanObject = core::ptr::null_mut();
    v_name_5506_ = lean_ctor_get(v_x_5505_, 0);
    lean_inc(v_name_5506_);
    v_package_x3f_5507_ = lean_ctor_get(v_x_5505_, 1);
    lean_inc(v_package_x3f_5507_);
    v_isModule_5508_ = lean_ctor_get_uint8(
        v_x_5505_,
        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
    );
    v_imports_x3f_5509_ = lean_ctor_get(v_x_5505_, 2);
    lean_inc(v_imports_x3f_5509_);
    v_importArts_5510_ = lean_ctor_get(v_x_5505_, 3);
    lean_inc(v_importArts_5510_);
    v_dynlibs_5511_ = lean_ctor_get(v_x_5505_, 4);
    lean_inc_ref(v_dynlibs_5511_);
    v_plugins_5512_ = lean_ctor_get(v_x_5505_, 5);
    lean_inc_ref(v_plugins_5512_);
    v_options_5513_ = lean_ctor_get(v_x_5505_, 6);
    lean_inc(v_options_5513_);
    lean_dec_ref(v_x_5505_);
    v___x_5514_ = l_Lean_instReprImport_repr___redArg___closed__5;
    v___x_5515_ = l_Lean_instReprModuleSetup_repr___redArg___closed__3;
    v___x_5516_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprPlugin_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instReprPlugin_repr___redArg___closed__4_once),
        _init_l_Lean_instReprPlugin_repr___redArg___closed__4,
    );
    v___x_5517_ = lean_unsigned_to_nat(0);
    v___x_5518_ = l_Lean_Name_reprPrec(v_name_5506_, v___x_5517_);
    v___x_5519_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_5519_, 0, v___x_5516_);
    lean_ctor_set(v___x_5519_, 1, v___x_5518_);
    v___x_5520_ = 0;
    v___x_5521_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_5521_, 0, v___x_5519_);
    lean_ctor_set_uint8(
        v___x_5521_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5520_,
    );
    v___x_5522_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5522_, 0, v___x_5515_);
    lean_ctor_set(v___x_5522_, 1, v___x_5521_);
    v___x_5523_ = l_Lean_instReprImport_repr___redArg___closed__9;
    v___x_5524_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5524_, 0, v___x_5522_);
    lean_ctor_set(v___x_5524_, 1, v___x_5523_);
    v___x_5525_ = lean_box(1);
    v___x_5526_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5526_, 0, v___x_5524_);
    lean_ctor_set(v___x_5526_, 1, v___x_5525_);
    v___x_5527_ = l_Lean_instReprModuleSetup_repr___redArg___closed__5;
    v___x_5528_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5528_, 0, v___x_5526_);
    lean_ctor_set(v___x_5528_, 1, v___x_5527_);
    v___x_5529_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5529_, 0, v___x_5528_);
    lean_ctor_set(v___x_5529_, 1, v___x_5514_);
    v___x_5530_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprModuleHeader_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_instReprModuleHeader_repr___redArg___closed__7_once),
        _init_l_Lean_instReprModuleHeader_repr___redArg___closed__7,
    );
    v___x_5531_ =
        l_Option_repr___at___00Lean_instReprPlugin_repr_spec__0(v_package_x3f_5507_, v___x_5517_);
    v___x_5532_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_5532_, 0, v___x_5530_);
    lean_ctor_set(v___x_5532_, 1, v___x_5531_);
    v___x_5533_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_5533_, 0, v___x_5532_);
    lean_ctor_set_uint8(
        v___x_5533_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5520_,
    );
    v___x_5534_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5534_, 0, v___x_5529_);
    lean_ctor_set(v___x_5534_, 1, v___x_5533_);
    v___x_5535_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5535_, 0, v___x_5534_);
    lean_ctor_set(v___x_5535_, 1, v___x_5523_);
    v___x_5536_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5536_, 0, v___x_5535_);
    lean_ctor_set(v___x_5536_, 1, v___x_5525_);
    v___x_5537_ = l_Lean_instReprModuleHeader_repr___redArg___closed__6;
    v___x_5538_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5538_, 0, v___x_5536_);
    lean_ctor_set(v___x_5538_, 1, v___x_5537_);
    v___x_5539_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5539_, 0, v___x_5538_);
    lean_ctor_set(v___x_5539_, 1, v___x_5514_);
    v___x_5540_ = l_Bool_repr___redArg(v_isModule_5508_);
    v___x_5541_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_5541_, 0, v___x_5530_);
    lean_ctor_set(v___x_5541_, 1, v___x_5540_);
    v___x_5542_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_5542_, 0, v___x_5541_);
    lean_ctor_set_uint8(
        v___x_5542_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5520_,
    );
    v___x_5543_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5543_, 0, v___x_5539_);
    lean_ctor_set(v___x_5543_, 1, v___x_5542_);
    v___x_5544_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5544_, 0, v___x_5543_);
    lean_ctor_set(v___x_5544_, 1, v___x_5523_);
    v___x_5545_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5545_, 0, v___x_5544_);
    lean_ctor_set(v___x_5545_, 1, v___x_5525_);
    v___x_5546_ = l_Lean_instReprModuleSetup_repr___redArg___closed__7;
    v___x_5547_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5547_, 0, v___x_5545_);
    lean_ctor_set(v___x_5547_, 1, v___x_5546_);
    v___x_5548_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5548_, 0, v___x_5547_);
    lean_ctor_set(v___x_5548_, 1, v___x_5514_);
    v___x_5549_ = l_Option_repr___at___00Lean_instReprModuleSetup_repr_spec__0(
        v_imports_x3f_5509_,
        v___x_5517_,
    );
    v___x_5550_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_5550_, 0, v___x_5530_);
    lean_ctor_set(v___x_5550_, 1, v___x_5549_);
    v___x_5551_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_5551_, 0, v___x_5550_);
    lean_ctor_set_uint8(
        v___x_5551_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5520_,
    );
    v___x_5552_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5552_, 0, v___x_5548_);
    lean_ctor_set(v___x_5552_, 1, v___x_5551_);
    v___x_5553_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5553_, 0, v___x_5552_);
    lean_ctor_set(v___x_5553_, 1, v___x_5523_);
    v___x_5554_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5554_, 0, v___x_5553_);
    lean_ctor_set(v___x_5554_, 1, v___x_5525_);
    v___x_5555_ = l_Lean_instReprModuleSetup_repr___redArg___closed__9;
    v___x_5556_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5556_, 0, v___x_5554_);
    lean_ctor_set(v___x_5556_, 1, v___x_5555_);
    v___x_5557_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5557_, 0, v___x_5556_);
    lean_ctor_set(v___x_5557_, 1, v___x_5514_);
    v___x_5558_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__15_once),
        _init_l_Lean_instReprImport_repr___redArg___closed__15,
    );
    v___x_5559_ = l_Lean_instReprModuleSetup_repr___redArg___closed__11;
    v___x_5560_ = lean_box(0);
    v___x_5561_ =
        l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_instReprModuleSetup_repr_spec__1(
            v___x_5560_,
            v_importArts_5510_,
        );
    lean_dec(v_importArts_5510_);
    v___x_5562_ = l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg(v___x_5561_);
    v___x_5563_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5563_, 0, v___x_5559_);
    lean_ctor_set(v___x_5563_, 1, v___x_5562_);
    v___x_5564_ = l_Repr_addAppParen(v___x_5563_, v___x_5517_);
    v___x_5565_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_5565_, 0, v___x_5558_);
    lean_ctor_set(v___x_5565_, 1, v___x_5564_);
    v___x_5566_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_5566_, 0, v___x_5565_);
    lean_ctor_set_uint8(
        v___x_5566_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5520_,
    );
    v___x_5567_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5567_, 0, v___x_5557_);
    lean_ctor_set(v___x_5567_, 1, v___x_5566_);
    v___x_5568_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5568_, 0, v___x_5567_);
    lean_ctor_set(v___x_5568_, 1, v___x_5523_);
    v___x_5569_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5569_, 0, v___x_5568_);
    lean_ctor_set(v___x_5569_, 1, v___x_5525_);
    v___x_5570_ = l_Lean_instReprModuleSetup_repr___redArg___closed__13;
    v___x_5571_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5571_, 0, v___x_5569_);
    lean_ctor_set(v___x_5571_, 1, v___x_5570_);
    v___x_5572_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5572_, 0, v___x_5571_);
    lean_ctor_set(v___x_5572_, 1, v___x_5514_);
    v___x_5573_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprModuleHeader_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instReprModuleHeader_repr___redArg___closed__4_once),
        _init_l_Lean_instReprModuleHeader_repr___redArg___closed__4,
    );
    v___x_5574_ = l_Array_repr___at___00Lean_instReprImportArtifacts_repr_spec__0(v_dynlibs_5511_);
    v___x_5575_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_5575_, 0, v___x_5573_);
    lean_ctor_set(v___x_5575_, 1, v___x_5574_);
    v___x_5576_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_5576_, 0, v___x_5575_);
    lean_ctor_set_uint8(
        v___x_5576_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5520_,
    );
    v___x_5577_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5577_, 0, v___x_5572_);
    lean_ctor_set(v___x_5577_, 1, v___x_5576_);
    v___x_5578_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5578_, 0, v___x_5577_);
    lean_ctor_set(v___x_5578_, 1, v___x_5523_);
    v___x_5579_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5579_, 0, v___x_5578_);
    lean_ctor_set(v___x_5579_, 1, v___x_5525_);
    v___x_5580_ = l_Lean_instReprModuleSetup_repr___redArg___closed__15;
    v___x_5581_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5581_, 0, v___x_5579_);
    lean_ctor_set(v___x_5581_, 1, v___x_5580_);
    v___x_5582_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5582_, 0, v___x_5581_);
    lean_ctor_set(v___x_5582_, 1, v___x_5514_);
    v___x_5583_ = l_Array_repr___at___00Lean_instReprModuleSetup_repr_spec__3(v_plugins_5512_);
    v___x_5584_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_5584_, 0, v___x_5573_);
    lean_ctor_set(v___x_5584_, 1, v___x_5583_);
    v___x_5585_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_5585_, 0, v___x_5584_);
    lean_ctor_set_uint8(
        v___x_5585_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5520_,
    );
    v___x_5586_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5586_, 0, v___x_5582_);
    lean_ctor_set(v___x_5586_, 1, v___x_5585_);
    v___x_5587_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5587_, 0, v___x_5586_);
    lean_ctor_set(v___x_5587_, 1, v___x_5523_);
    v___x_5588_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5588_, 0, v___x_5587_);
    lean_ctor_set(v___x_5588_, 1, v___x_5525_);
    v___x_5589_ = l_Lean_instReprModuleSetup_repr___redArg___closed__17;
    v___x_5590_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5590_, 0, v___x_5588_);
    lean_ctor_set(v___x_5590_, 1, v___x_5589_);
    v___x_5591_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5591_, 0, v___x_5590_);
    lean_ctor_set(v___x_5591_, 1, v___x_5514_);
    v___x_5592_ = l_Lean_instReprLeanOptions_repr___redArg(v_options_5513_);
    lean_dec(v_options_5513_);
    v___x_5593_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_5593_, 0, v___x_5573_);
    lean_ctor_set(v___x_5593_, 1, v___x_5592_);
    v___x_5594_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_5594_, 0, v___x_5593_);
    lean_ctor_set_uint8(
        v___x_5594_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5520_,
    );
    v___x_5595_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5595_, 0, v___x_5591_);
    lean_ctor_set(v___x_5595_, 1, v___x_5594_);
    v___x_5596_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__20),
        core::ptr::addr_of_mut!(l_Lean_instReprImport_repr___redArg___closed__20_once),
        _init_l_Lean_instReprImport_repr___redArg___closed__20,
    );
    v___x_5597_ = l_Lean_instReprImport_repr___redArg___closed__21;
    v___x_5598_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5598_, 0, v___x_5597_);
    lean_ctor_set(v___x_5598_, 1, v___x_5595_);
    v___x_5599_ = l_Lean_instReprImport_repr___redArg___closed__22;
    v___x_5600_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5600_, 0, v___x_5598_);
    lean_ctor_set(v___x_5600_, 1, v___x_5599_);
    v___x_5601_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_5601_, 0, v___x_5596_);
    lean_ctor_set(v___x_5601_, 1, v___x_5600_);
    v___x_5602_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_5602_, 0, v___x_5601_);
    lean_ctor_set_uint8(
        v___x_5602_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5520_,
    );
    return v___x_5602_;
}
pub unsafe fn l_Lean_instReprModuleSetup_repr(
    mut v_x_5603_: *mut LeanObject,
    mut v_prec_5604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5605_: *mut LeanObject = core::ptr::null_mut();
    v___x_5605_ = l_Lean_instReprModuleSetup_repr___redArg(v_x_5603_);
    return v___x_5605_;
}
pub unsafe fn l_Lean_instReprModuleSetup_repr___boxed(
    mut v_x_5606_: *mut LeanObject,
    mut v_prec_5607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5608_: *mut LeanObject = core::ptr::null_mut();
    v_res_5608_ = l_Lean_instReprModuleSetup_repr(v_x_5606_, v_prec_5607_);
    lean_dec(v_prec_5607_);
    return v_res_5608_;
}
pub unsafe fn l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2(
    mut v_a_5609_: *mut LeanObject,
    mut v_n_5610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5611_: *mut LeanObject = core::ptr::null_mut();
    v___x_5611_ = l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___redArg(v_a_5609_);
    return v___x_5611_;
}
pub unsafe fn l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2___boxed(
    mut v_a_5612_: *mut LeanObject,
    mut v_n_5613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5614_: *mut LeanObject = core::ptr::null_mut();
    v_res_5614_ = l_List_repr___at___00Lean_instReprModuleSetup_repr_spec__2(v_a_5612_, v_n_5613_);
    lean_dec(v_n_5613_);
    return v_res_5614_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2(
    mut v_x_5615_: *mut LeanObject,
    mut v_x_5616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5617_: *mut LeanObject = core::ptr::null_mut();
    v___x_5617_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___redArg(v_x_5615_);
    return v___x_5617_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2___boxed(
    mut v_x_5618_: *mut LeanObject,
    mut v_x_5619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5620_: *mut LeanObject = core::ptr::null_mut();
    v_res_5620_ =
        l_Prod_repr___at___00List_repr___at___00Lean_instReprModuleSetup_repr_spec__2_spec__2(
            v_x_5618_, v_x_5619_,
        );
    lean_dec(v_x_5619_);
    return v_res_5620_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__6(
    mut v_sz_5631_: usize,
    mut v_i_5632_: usize,
    mut v_bs_5633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5634_: u8 = 0;
    let mut v_v_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: usize = 0;
    let mut v___x_5640_: usize = 0;
    let mut v___x_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5634_ = lean_usize_dec_lt(v_i_5632_, v_sz_5631_);
                if v___x_5634_ == 0 {
                    return v_bs_5633_;
                } else {
                    v_v_5635_ = lean_array_uget(v_bs_5633_, v_i_5632_);
                    v___x_5636_ = lean_unsigned_to_nat(0);
                    v_bs_x27_5637_ = lean_array_uset(v_bs_5633_, v_i_5632_, v___x_5636_);
                    v___x_5638_ = l_Lean_instToJsonPlugin_toJson(v_v_5635_);
                    v___x_5639_ = 1usize;
                    v___x_5640_ = lean_usize_add(v_i_5632_, v___x_5639_);
                    v___x_5641_ = lean_array_uset(v_bs_x27_5637_, v_i_5632_, v___x_5638_);
                    v_i_5632_ = v___x_5640_;
                    v_bs_5633_ = v___x_5641_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__6___boxed(
    mut v_sz_5643_: *mut LeanObject,
    mut v_i_5644_: *mut LeanObject,
    mut v_bs_5645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5646_: usize = 0;
    let mut v_i_boxed_5647_: usize = 0;
    let mut v_res_5648_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5646_ = lean_unbox_usize(v_sz_5643_);
    lean_dec(v_sz_5643_);
    v_i_boxed_5647_ = lean_unbox_usize(v_i_5644_);
    lean_dec(v_i_5644_);
    v_res_5648_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__6(v_sz_boxed_5646_, v_i_boxed_5647_, v_bs_5645_);
    return v_res_5648_;
}
pub unsafe fn l_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3(
    mut v_a_5649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_5650_: usize = 0;
    let mut v___x_5651_: usize = 0;
    let mut v___x_5652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut LeanObject = core::ptr::null_mut();
    v_sz_5650_ = lean_array_size(v_a_5649_);
    v___x_5651_ = 0usize;
    v___x_5652_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3_spec__6(v_sz_5650_, v___x_5651_, v_a_5649_);
    v___x_5653_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_5653_, 0, v___x_5652_);
    return v___x_5653_;
}
pub unsafe fn l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2___redArg(
    mut v_msg_5654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut LeanObject = core::ptr::null_mut();
    v___x_5655_ = lean_box(1);
    v___x_5656_ = lean_panic_fn_borrowed(v___x_5655_, v_msg_5654_);
    return v___x_5656_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut LeanObject = core::ptr::null_mut();
    v___x_5660_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__2;
    v___x_5661_ = lean_unsigned_to_nat(35);
    v___x_5662_ = lean_unsigned_to_nat(182);
    v___x_5663_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__1;
    v___x_5664_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__0;
    v___x_5665_ = l_mkPanicMessageWithDecl(
        v___x_5664_,
        v___x_5663_,
        v___x_5662_,
        v___x_5661_,
        v___x_5660_,
    );
    return v___x_5665_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut LeanObject = core::ptr::null_mut();
    v___x_5666_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__2;
    v___x_5667_ = lean_unsigned_to_nat(21);
    v___x_5668_ = lean_unsigned_to_nat(183);
    v___x_5669_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__1;
    v___x_5670_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__0;
    v___x_5671_ = l_mkPanicMessageWithDecl(
        v___x_5670_,
        v___x_5669_,
        v___x_5668_,
        v___x_5667_,
        v___x_5666_,
    );
    return v___x_5671_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut LeanObject = core::ptr::null_mut();
    v___x_5674_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__6;
    v___x_5675_ = lean_unsigned_to_nat(35);
    v___x_5676_ = lean_unsigned_to_nat(276);
    v___x_5677_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__5;
    v___x_5678_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__0;
    v___x_5679_ = l_mkPanicMessageWithDecl(
        v___x_5678_,
        v___x_5677_,
        v___x_5676_,
        v___x_5675_,
        v___x_5674_,
    );
    return v___x_5679_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__8()
-> *mut LeanObject {
    let mut v___x_5680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut LeanObject = core::ptr::null_mut();
    v___x_5680_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__6;
    v___x_5681_ = lean_unsigned_to_nat(21);
    v___x_5682_ = lean_unsigned_to_nat(277);
    v___x_5683_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__5;
    v___x_5684_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__0;
    v___x_5685_ = l_mkPanicMessageWithDecl(
        v___x_5684_,
        v___x_5683_,
        v___x_5682_,
        v___x_5681_,
        v___x_5680_,
    );
    return v___x_5685_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg(
    mut v_k_5686_: *mut LeanObject,
    mut v_v_5687_: *mut LeanObject,
    mut v_t_5688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_5689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_5692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5696_: u8 = 0;
    let mut v___x_5697_: u8 = 0;
    let mut v___x_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: u8 = 0;
    let mut v___x_5708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5716_: u8 = 0;
    let mut v_size_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_5721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: u8 = 0;
    let mut v___x_5727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5728_: u8 = 0;
    let mut v___x_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5755_: u8 = 0;
    let mut v_unused_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5770_: u8 = 0;
    let mut v___x_5772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5774_: u8 = 0;
    let mut v_unused_5775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5785_: u8 = 0;
    let mut v_unused_5786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_5797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5804_: u8 = 0;
    let mut v_size_5805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5815_: u8 = 0;
    let mut v_unused_5816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5822_: u8 = 0;
    let mut v___x_5823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5831_: u8 = 0;
    let mut v_unused_5832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5840_: u8 = 0;
    let mut v_k_5841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5845_: u8 = 0;
    let mut v___x_5846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5857_: u8 = 0;
    let mut v_unused_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5861_: u8 = 0;
    let mut v_unused_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_5881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: u8 = 0;
    let mut v___x_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5894_: u8 = 0;
    let mut v_size_5895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: u8 = 0;
    let mut v___x_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5906_: u8 = 0;
    let mut v___x_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5932_: u8 = 0;
    let mut v_unused_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5946_: u8 = 0;
    let mut v___x_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5950_: u8 = 0;
    let mut v_unused_5951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5961_: u8 = 0;
    let mut v_unused_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5980_: u8 = 0;
    let mut v_size_5981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5991_: u8 = 0;
    let mut v_unused_5992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5998_: u8 = 0;
    let mut v_k_5999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6003_: u8 = 0;
    let mut v___x_6004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6015_: u8 = 0;
    let mut v_unused_6016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6019_: u8 = 0;
    let mut v_unused_6020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6028_: u8 = 0;
    let mut v___x_6029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6037_: u8 = 0;
    let mut v_unused_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6049_: u8 = 0;
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_5688_) == 0 {
                    v_size_5689_ = lean_ctor_get(v_t_5688_, 0);
                    v_k_5690_ = lean_ctor_get(v_t_5688_, 1);
                    v_v_5691_ = lean_ctor_get(v_t_5688_, 2);
                    v_l_5692_ = lean_ctor_get(v_t_5688_, 3);
                    v_r_5693_ = lean_ctor_get(v_t_5688_, 4);
                    v_isSharedCheck_6049_ = (!lean_is_exclusive(v_t_5688_)) as u8;
                    if v_isSharedCheck_6049_ == 0 {
                        v___x_5695_ = v_t_5688_;
                        v_isShared_5696_ = v_isSharedCheck_6049_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_5693_);
                        lean_inc(v_l_5692_);
                        lean_inc(v_v_5691_);
                        lean_inc(v_k_5690_);
                        lean_inc(v_size_5689_);
                        lean_dec(v_t_5688_);
                        v___x_5695_ = lean_box(0);
                        v_isShared_5696_ = v_isSharedCheck_6049_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_6050_ = lean_unsigned_to_nat(1);
                    v___x_6051_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_6051_, 0, v___x_6050_);
                    lean_ctor_set(v___x_6051_, 1, v_k_5686_);
                    lean_ctor_set(v___x_6051_, 2, v_v_5687_);
                    lean_ctor_set(v___x_6051_, 3, v_t_5688_);
                    lean_ctor_set(v___x_6051_, 4, v_t_5688_);
                    return v___x_6051_;
                }
            }
            1 => {
                v___x_5697_ = lean_string_compare(v_k_5686_, v_k_5690_);
                match v___x_5697_ {
                    0 => {
                        lean_dec(v_size_5689_);
                        v___x_5698_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg(v_k_5686_, v_v_5687_, v_l_5692_);
                        if lean_obj_tag(v_r_5693_) == 0 {
                            if lean_obj_tag(v___x_5698_) == 0 {
                                v_size_5699_ = lean_ctor_get(v_r_5693_, 0);
                                v_size_5700_ = lean_ctor_get(v___x_5698_, 0);
                                lean_inc(v_size_5700_);
                                v_k_5701_ = lean_ctor_get(v___x_5698_, 1);
                                lean_inc(v_k_5701_);
                                v_v_5702_ = lean_ctor_get(v___x_5698_, 2);
                                lean_inc(v_v_5702_);
                                v_l_5703_ = lean_ctor_get(v___x_5698_, 3);
                                lean_inc(v_l_5703_);
                                v_r_5704_ = lean_ctor_get(v___x_5698_, 4);
                                lean_inc(v_r_5704_);
                                v___x_5705_ = lean_unsigned_to_nat(3);
                                v___x_5706_ = lean_nat_mul(v___x_5705_, v_size_5699_);
                                v___x_5707_ = lean_nat_dec_lt(v___x_5706_, v_size_5700_);
                                lean_dec(v___x_5706_);
                                if v___x_5707_ == 0 {
                                    lean_dec(v_r_5704_);
                                    lean_dec(v_l_5703_);
                                    lean_dec(v_v_5702_);
                                    lean_dec(v_k_5701_);
                                    v___x_5708_ = lean_unsigned_to_nat(1);
                                    v___x_5709_ = lean_nat_add(v___x_5708_, v_size_5700_);
                                    lean_dec(v_size_5700_);
                                    v___x_5710_ = lean_nat_add(v___x_5709_, v_size_5699_);
                                    lean_dec(v___x_5709_);
                                    if v_isShared_5696_ == 0 {
                                        lean_ctor_set(v___x_5695_, 3, v___x_5698_);
                                        lean_ctor_set(v___x_5695_, 0, v___x_5710_);
                                        v___x_5712_ = v___x_5695_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_5713_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_5713_, 0, v___x_5710_);
                                        lean_ctor_set(v_reuseFailAlloc_5713_, 1, v_k_5690_);
                                        lean_ctor_set(v_reuseFailAlloc_5713_, 2, v_v_5691_);
                                        lean_ctor_set(v_reuseFailAlloc_5713_, 3, v___x_5698_);
                                        lean_ctor_set(v_reuseFailAlloc_5713_, 4, v_r_5693_);
                                        v___x_5712_ = v_reuseFailAlloc_5713_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v_isSharedCheck_5785_ = (!lean_is_exclusive(v___x_5698_)) as u8;
                                    if v_isSharedCheck_5785_ == 0 {
                                        v_unused_5786_ = lean_ctor_get(v___x_5698_, 4);
                                        lean_dec(v_unused_5786_);
                                        v_unused_5787_ = lean_ctor_get(v___x_5698_, 3);
                                        lean_dec(v_unused_5787_);
                                        v_unused_5788_ = lean_ctor_get(v___x_5698_, 2);
                                        lean_dec(v_unused_5788_);
                                        v_unused_5789_ = lean_ctor_get(v___x_5698_, 1);
                                        lean_dec(v_unused_5789_);
                                        v_unused_5790_ = lean_ctor_get(v___x_5698_, 0);
                                        lean_dec(v_unused_5790_);
                                        v___x_5715_ = v___x_5698_;
                                        v_isShared_5716_ = v_isSharedCheck_5785_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_dec(v___x_5698_);
                                        v___x_5715_ = lean_box(0);
                                        v_isShared_5716_ = v_isSharedCheck_5785_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_5791_ = lean_ctor_get(v_r_5693_, 0);
                                v___x_5792_ = lean_unsigned_to_nat(1);
                                v___x_5793_ = lean_nat_add(v___x_5792_, v_size_5791_);
                                if v_isShared_5696_ == 0 {
                                    lean_ctor_set(v___x_5695_, 3, v___x_5698_);
                                    lean_ctor_set(v___x_5695_, 0, v___x_5793_);
                                    v___x_5795_ = v___x_5695_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_5796_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_5796_, 0, v___x_5793_);
                                    lean_ctor_set(v_reuseFailAlloc_5796_, 1, v_k_5690_);
                                    lean_ctor_set(v_reuseFailAlloc_5796_, 2, v_v_5691_);
                                    lean_ctor_set(v_reuseFailAlloc_5796_, 3, v___x_5698_);
                                    lean_ctor_set(v_reuseFailAlloc_5796_, 4, v_r_5693_);
                                    v___x_5795_ = v_reuseFailAlloc_5796_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if lean_obj_tag(v___x_5698_) == 0 {
                                v_l_5797_ = lean_ctor_get(v___x_5698_, 3);
                                lean_inc(v_l_5797_);
                                if lean_obj_tag(v_l_5797_) == 0 {
                                    v_r_5798_ = lean_ctor_get(v___x_5698_, 4);
                                    lean_inc(v_r_5798_);
                                    if lean_obj_tag(v_r_5798_) == 0 {
                                        v_size_5799_ = lean_ctor_get(v___x_5698_, 0);
                                        v_k_5800_ = lean_ctor_get(v___x_5698_, 1);
                                        v_v_5801_ = lean_ctor_get(v___x_5698_, 2);
                                        v_isSharedCheck_5815_ =
                                            (!lean_is_exclusive(v___x_5698_)) as u8;
                                        if v_isSharedCheck_5815_ == 0 {
                                            v_unused_5816_ = lean_ctor_get(v___x_5698_, 4);
                                            lean_dec(v_unused_5816_);
                                            v_unused_5817_ = lean_ctor_get(v___x_5698_, 3);
                                            lean_dec(v_unused_5817_);
                                            v___x_5803_ = v___x_5698_;
                                            v_isShared_5804_ = v_isSharedCheck_5815_;
                                            state = 14;
                                            continue;
                                        } else {
                                            lean_inc(v_v_5801_);
                                            lean_inc(v_k_5800_);
                                            lean_inc(v_size_5799_);
                                            lean_dec(v___x_5698_);
                                            v___x_5803_ = lean_box(0);
                                            v_isShared_5804_ = v_isSharedCheck_5815_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_5818_ = lean_ctor_get(v___x_5698_, 1);
                                        v_v_5819_ = lean_ctor_get(v___x_5698_, 2);
                                        v_isSharedCheck_5831_ =
                                            (!lean_is_exclusive(v___x_5698_)) as u8;
                                        if v_isSharedCheck_5831_ == 0 {
                                            v_unused_5832_ = lean_ctor_get(v___x_5698_, 4);
                                            lean_dec(v_unused_5832_);
                                            v_unused_5833_ = lean_ctor_get(v___x_5698_, 3);
                                            lean_dec(v_unused_5833_);
                                            v_unused_5834_ = lean_ctor_get(v___x_5698_, 0);
                                            lean_dec(v_unused_5834_);
                                            v___x_5821_ = v___x_5698_;
                                            v_isShared_5822_ = v_isSharedCheck_5831_;
                                            state = 17;
                                            continue;
                                        } else {
                                            lean_inc(v_v_5819_);
                                            lean_inc(v_k_5818_);
                                            lean_dec(v___x_5698_);
                                            v___x_5821_ = lean_box(0);
                                            v_isShared_5822_ = v_isSharedCheck_5831_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_5835_ = lean_ctor_get(v___x_5698_, 4);
                                    lean_inc(v_r_5835_);
                                    if lean_obj_tag(v_r_5835_) == 0 {
                                        v_k_5836_ = lean_ctor_get(v___x_5698_, 1);
                                        v_v_5837_ = lean_ctor_get(v___x_5698_, 2);
                                        v_isSharedCheck_5861_ =
                                            (!lean_is_exclusive(v___x_5698_)) as u8;
                                        if v_isSharedCheck_5861_ == 0 {
                                            v_unused_5862_ = lean_ctor_get(v___x_5698_, 4);
                                            lean_dec(v_unused_5862_);
                                            v_unused_5863_ = lean_ctor_get(v___x_5698_, 3);
                                            lean_dec(v_unused_5863_);
                                            v_unused_5864_ = lean_ctor_get(v___x_5698_, 0);
                                            lean_dec(v_unused_5864_);
                                            v___x_5839_ = v___x_5698_;
                                            v_isShared_5840_ = v_isSharedCheck_5861_;
                                            state = 20;
                                            continue;
                                        } else {
                                            lean_inc(v_v_5837_);
                                            lean_inc(v_k_5836_);
                                            lean_dec(v___x_5698_);
                                            v___x_5839_ = lean_box(0);
                                            v_isShared_5840_ = v_isSharedCheck_5861_;
                                            state = 20;
                                            continue;
                                        }
                                    } else {
                                        v___x_5865_ = lean_unsigned_to_nat(2);
                                        if v_isShared_5696_ == 0 {
                                            lean_ctor_set(v___x_5695_, 4, v_r_5835_);
                                            lean_ctor_set(v___x_5695_, 3, v___x_5698_);
                                            lean_ctor_set(v___x_5695_, 0, v___x_5865_);
                                            v___x_5867_ = v___x_5695_;
                                            state = 25;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_5868_ =
                                                lean_alloc_ctor(0, 5, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_5868_, 0, v___x_5865_);
                                            lean_ctor_set(v_reuseFailAlloc_5868_, 1, v_k_5690_);
                                            lean_ctor_set(v_reuseFailAlloc_5868_, 2, v_v_5691_);
                                            lean_ctor_set(v_reuseFailAlloc_5868_, 3, v___x_5698_);
                                            lean_ctor_set(v_reuseFailAlloc_5868_, 4, v_r_5835_);
                                            v___x_5867_ = v_reuseFailAlloc_5868_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_5869_ = lean_unsigned_to_nat(1);
                                if v_isShared_5696_ == 0 {
                                    lean_ctor_set(v___x_5695_, 4, v___x_5698_);
                                    lean_ctor_set(v___x_5695_, 3, v___x_5698_);
                                    lean_ctor_set(v___x_5695_, 0, v___x_5869_);
                                    v___x_5871_ = v___x_5695_;
                                    state = 26;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_5872_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_5872_, 0, v___x_5869_);
                                    lean_ctor_set(v_reuseFailAlloc_5872_, 1, v_k_5690_);
                                    lean_ctor_set(v_reuseFailAlloc_5872_, 2, v_v_5691_);
                                    lean_ctor_set(v_reuseFailAlloc_5872_, 3, v___x_5698_);
                                    lean_ctor_set(v_reuseFailAlloc_5872_, 4, v___x_5698_);
                                    v___x_5871_ = v_reuseFailAlloc_5872_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    }
                    1 => {
                        lean_dec(v_v_5691_);
                        lean_dec(v_k_5690_);
                        if v_isShared_5696_ == 0 {
                            lean_ctor_set(v___x_5695_, 2, v_v_5687_);
                            lean_ctor_set(v___x_5695_, 1, v_k_5686_);
                            v___x_5874_ = v___x_5695_;
                            state = 27;
                            continue;
                        } else {
                            v_reuseFailAlloc_5875_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5875_, 0, v_size_5689_);
                            lean_ctor_set(v_reuseFailAlloc_5875_, 1, v_k_5686_);
                            lean_ctor_set(v_reuseFailAlloc_5875_, 2, v_v_5687_);
                            lean_ctor_set(v_reuseFailAlloc_5875_, 3, v_l_5692_);
                            lean_ctor_set(v_reuseFailAlloc_5875_, 4, v_r_5693_);
                            v___x_5874_ = v_reuseFailAlloc_5875_;
                            state = 27;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec(v_size_5689_);
                        v___x_5876_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg(v_k_5686_, v_v_5687_, v_r_5693_);
                        if lean_obj_tag(v_l_5692_) == 0 {
                            if lean_obj_tag(v___x_5876_) == 0 {
                                v_size_5877_ = lean_ctor_get(v_l_5692_, 0);
                                v_size_5878_ = lean_ctor_get(v___x_5876_, 0);
                                lean_inc(v_size_5878_);
                                v_k_5879_ = lean_ctor_get(v___x_5876_, 1);
                                lean_inc(v_k_5879_);
                                v_v_5880_ = lean_ctor_get(v___x_5876_, 2);
                                lean_inc(v_v_5880_);
                                v_l_5881_ = lean_ctor_get(v___x_5876_, 3);
                                lean_inc(v_l_5881_);
                                v_r_5882_ = lean_ctor_get(v___x_5876_, 4);
                                lean_inc(v_r_5882_);
                                v___x_5883_ = lean_unsigned_to_nat(3);
                                v___x_5884_ = lean_nat_mul(v___x_5883_, v_size_5877_);
                                v___x_5885_ = lean_nat_dec_lt(v___x_5884_, v_size_5878_);
                                lean_dec(v___x_5884_);
                                if v___x_5885_ == 0 {
                                    lean_dec(v_r_5882_);
                                    lean_dec(v_l_5881_);
                                    lean_dec(v_v_5880_);
                                    lean_dec(v_k_5879_);
                                    v___x_5886_ = lean_unsigned_to_nat(1);
                                    v___x_5887_ = lean_nat_add(v___x_5886_, v_size_5877_);
                                    v___x_5888_ = lean_nat_add(v___x_5887_, v_size_5878_);
                                    lean_dec(v_size_5878_);
                                    lean_dec(v___x_5887_);
                                    if v_isShared_5696_ == 0 {
                                        lean_ctor_set(v___x_5695_, 4, v___x_5876_);
                                        lean_ctor_set(v___x_5695_, 0, v___x_5888_);
                                        v___x_5890_ = v___x_5695_;
                                        state = 28;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_5891_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_5891_, 0, v___x_5888_);
                                        lean_ctor_set(v_reuseFailAlloc_5891_, 1, v_k_5690_);
                                        lean_ctor_set(v_reuseFailAlloc_5891_, 2, v_v_5691_);
                                        lean_ctor_set(v_reuseFailAlloc_5891_, 3, v_l_5692_);
                                        lean_ctor_set(v_reuseFailAlloc_5891_, 4, v___x_5876_);
                                        v___x_5890_ = v_reuseFailAlloc_5891_;
                                        state = 28;
                                        continue;
                                    }
                                } else {
                                    v_isSharedCheck_5961_ = (!lean_is_exclusive(v___x_5876_)) as u8;
                                    if v_isSharedCheck_5961_ == 0 {
                                        v_unused_5962_ = lean_ctor_get(v___x_5876_, 4);
                                        lean_dec(v_unused_5962_);
                                        v_unused_5963_ = lean_ctor_get(v___x_5876_, 3);
                                        lean_dec(v_unused_5963_);
                                        v_unused_5964_ = lean_ctor_get(v___x_5876_, 2);
                                        lean_dec(v_unused_5964_);
                                        v_unused_5965_ = lean_ctor_get(v___x_5876_, 1);
                                        lean_dec(v_unused_5965_);
                                        v_unused_5966_ = lean_ctor_get(v___x_5876_, 0);
                                        lean_dec(v_unused_5966_);
                                        v___x_5893_ = v___x_5876_;
                                        v_isShared_5894_ = v_isSharedCheck_5961_;
                                        state = 29;
                                        continue;
                                    } else {
                                        lean_dec(v___x_5876_);
                                        v___x_5893_ = lean_box(0);
                                        v_isShared_5894_ = v_isSharedCheck_5961_;
                                        state = 29;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_5967_ = lean_ctor_get(v_l_5692_, 0);
                                v___x_5968_ = lean_unsigned_to_nat(1);
                                v___x_5969_ = lean_nat_add(v___x_5968_, v_size_5967_);
                                if v_isShared_5696_ == 0 {
                                    lean_ctor_set(v___x_5695_, 4, v___x_5876_);
                                    lean_ctor_set(v___x_5695_, 0, v___x_5969_);
                                    v___x_5971_ = v___x_5695_;
                                    state = 39;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_5972_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_5972_, 0, v___x_5969_);
                                    lean_ctor_set(v_reuseFailAlloc_5972_, 1, v_k_5690_);
                                    lean_ctor_set(v_reuseFailAlloc_5972_, 2, v_v_5691_);
                                    lean_ctor_set(v_reuseFailAlloc_5972_, 3, v_l_5692_);
                                    lean_ctor_set(v_reuseFailAlloc_5972_, 4, v___x_5876_);
                                    v___x_5971_ = v_reuseFailAlloc_5972_;
                                    state = 39;
                                    continue;
                                }
                            }
                        } else {
                            if lean_obj_tag(v___x_5876_) == 0 {
                                v_l_5973_ = lean_ctor_get(v___x_5876_, 3);
                                lean_inc(v_l_5973_);
                                if lean_obj_tag(v_l_5973_) == 0 {
                                    v_r_5974_ = lean_ctor_get(v___x_5876_, 4);
                                    lean_inc(v_r_5974_);
                                    if lean_obj_tag(v_r_5974_) == 0 {
                                        v_size_5975_ = lean_ctor_get(v___x_5876_, 0);
                                        v_k_5976_ = lean_ctor_get(v___x_5876_, 1);
                                        v_v_5977_ = lean_ctor_get(v___x_5876_, 2);
                                        v_isSharedCheck_5991_ =
                                            (!lean_is_exclusive(v___x_5876_)) as u8;
                                        if v_isSharedCheck_5991_ == 0 {
                                            v_unused_5992_ = lean_ctor_get(v___x_5876_, 4);
                                            lean_dec(v_unused_5992_);
                                            v_unused_5993_ = lean_ctor_get(v___x_5876_, 3);
                                            lean_dec(v_unused_5993_);
                                            v___x_5979_ = v___x_5876_;
                                            v_isShared_5980_ = v_isSharedCheck_5991_;
                                            state = 40;
                                            continue;
                                        } else {
                                            lean_inc(v_v_5977_);
                                            lean_inc(v_k_5976_);
                                            lean_inc(v_size_5975_);
                                            lean_dec(v___x_5876_);
                                            v___x_5979_ = lean_box(0);
                                            v_isShared_5980_ = v_isSharedCheck_5991_;
                                            state = 40;
                                            continue;
                                        }
                                    } else {
                                        v_k_5994_ = lean_ctor_get(v___x_5876_, 1);
                                        v_v_5995_ = lean_ctor_get(v___x_5876_, 2);
                                        v_isSharedCheck_6019_ =
                                            (!lean_is_exclusive(v___x_5876_)) as u8;
                                        if v_isSharedCheck_6019_ == 0 {
                                            v_unused_6020_ = lean_ctor_get(v___x_5876_, 4);
                                            lean_dec(v_unused_6020_);
                                            v_unused_6021_ = lean_ctor_get(v___x_5876_, 3);
                                            lean_dec(v_unused_6021_);
                                            v_unused_6022_ = lean_ctor_get(v___x_5876_, 0);
                                            lean_dec(v_unused_6022_);
                                            v___x_5997_ = v___x_5876_;
                                            v_isShared_5998_ = v_isSharedCheck_6019_;
                                            state = 43;
                                            continue;
                                        } else {
                                            lean_inc(v_v_5995_);
                                            lean_inc(v_k_5994_);
                                            lean_dec(v___x_5876_);
                                            v___x_5997_ = lean_box(0);
                                            v_isShared_5998_ = v_isSharedCheck_6019_;
                                            state = 43;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_6023_ = lean_ctor_get(v___x_5876_, 4);
                                    lean_inc(v_r_6023_);
                                    if lean_obj_tag(v_r_6023_) == 0 {
                                        v_k_6024_ = lean_ctor_get(v___x_5876_, 1);
                                        v_v_6025_ = lean_ctor_get(v___x_5876_, 2);
                                        v_isSharedCheck_6037_ =
                                            (!lean_is_exclusive(v___x_5876_)) as u8;
                                        if v_isSharedCheck_6037_ == 0 {
                                            v_unused_6038_ = lean_ctor_get(v___x_5876_, 4);
                                            lean_dec(v_unused_6038_);
                                            v_unused_6039_ = lean_ctor_get(v___x_5876_, 3);
                                            lean_dec(v_unused_6039_);
                                            v_unused_6040_ = lean_ctor_get(v___x_5876_, 0);
                                            lean_dec(v_unused_6040_);
                                            v___x_6027_ = v___x_5876_;
                                            v_isShared_6028_ = v_isSharedCheck_6037_;
                                            state = 48;
                                            continue;
                                        } else {
                                            lean_inc(v_v_6025_);
                                            lean_inc(v_k_6024_);
                                            lean_dec(v___x_5876_);
                                            v___x_6027_ = lean_box(0);
                                            v_isShared_6028_ = v_isSharedCheck_6037_;
                                            state = 48;
                                            continue;
                                        }
                                    } else {
                                        v___x_6041_ = lean_unsigned_to_nat(2);
                                        if v_isShared_5696_ == 0 {
                                            lean_ctor_set(v___x_5695_, 4, v___x_5876_);
                                            lean_ctor_set(v___x_5695_, 3, v_r_6023_);
                                            lean_ctor_set(v___x_5695_, 0, v___x_6041_);
                                            v___x_6043_ = v___x_5695_;
                                            state = 51;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_6044_ =
                                                lean_alloc_ctor(0, 5, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_6044_, 0, v___x_6041_);
                                            lean_ctor_set(v_reuseFailAlloc_6044_, 1, v_k_5690_);
                                            lean_ctor_set(v_reuseFailAlloc_6044_, 2, v_v_5691_);
                                            lean_ctor_set(v_reuseFailAlloc_6044_, 3, v_r_6023_);
                                            lean_ctor_set(v_reuseFailAlloc_6044_, 4, v___x_5876_);
                                            v___x_6043_ = v_reuseFailAlloc_6044_;
                                            state = 51;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_6045_ = lean_unsigned_to_nat(1);
                                if v_isShared_5696_ == 0 {
                                    lean_ctor_set(v___x_5695_, 4, v___x_5876_);
                                    lean_ctor_set(v___x_5695_, 3, v___x_5876_);
                                    lean_ctor_set(v___x_5695_, 0, v___x_6045_);
                                    v___x_6047_ = v___x_5695_;
                                    state = 52;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6048_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_6048_, 0, v___x_6045_);
                                    lean_ctor_set(v_reuseFailAlloc_6048_, 1, v_k_5690_);
                                    lean_ctor_set(v_reuseFailAlloc_6048_, 2, v_v_5691_);
                                    lean_ctor_set(v_reuseFailAlloc_6048_, 3, v___x_5876_);
                                    lean_ctor_set(v_reuseFailAlloc_6048_, 4, v___x_5876_);
                                    v___x_6047_ = v_reuseFailAlloc_6048_;
                                    state = 52;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_5712_;
            }
            3 => {
                if lean_obj_tag(v_l_5703_) == 0 {
                    if lean_obj_tag(v_r_5704_) == 0 {
                        v_size_5717_ = lean_ctor_get(v_l_5703_, 0);
                        v_size_5718_ = lean_ctor_get(v_r_5704_, 0);
                        v_k_5719_ = lean_ctor_get(v_r_5704_, 1);
                        v_v_5720_ = lean_ctor_get(v_r_5704_, 2);
                        v_l_5721_ = lean_ctor_get(v_r_5704_, 3);
                        v_r_5722_ = lean_ctor_get(v_r_5704_, 4);
                        v___x_5723_ = lean_unsigned_to_nat(2);
                        v___x_5724_ = lean_nat_mul(v___x_5723_, v_size_5717_);
                        v___x_5725_ = lean_nat_dec_lt(v_size_5718_, v___x_5724_);
                        lean_dec(v___x_5724_);
                        if v___x_5725_ == 0 {
                            lean_inc(v_r_5722_);
                            lean_inc(v_l_5721_);
                            lean_inc(v_v_5720_);
                            lean_inc(v_k_5719_);
                            v_isSharedCheck_5755_ = (!lean_is_exclusive(v_r_5704_)) as u8;
                            if v_isSharedCheck_5755_ == 0 {
                                v_unused_5756_ = lean_ctor_get(v_r_5704_, 4);
                                lean_dec(v_unused_5756_);
                                v_unused_5757_ = lean_ctor_get(v_r_5704_, 3);
                                lean_dec(v_unused_5757_);
                                v_unused_5758_ = lean_ctor_get(v_r_5704_, 2);
                                lean_dec(v_unused_5758_);
                                v_unused_5759_ = lean_ctor_get(v_r_5704_, 1);
                                lean_dec(v_unused_5759_);
                                v_unused_5760_ = lean_ctor_get(v_r_5704_, 0);
                                lean_dec(v_unused_5760_);
                                v___x_5727_ = v_r_5704_;
                                v_isShared_5728_ = v_isSharedCheck_5755_;
                                state = 4;
                                continue;
                            } else {
                                lean_dec(v_r_5704_);
                                v___x_5727_ = lean_box(0);
                                v_isShared_5728_ = v_isSharedCheck_5755_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_5695_);
                            v___x_5761_ = lean_unsigned_to_nat(1);
                            v___x_5762_ = lean_nat_add(v___x_5761_, v_size_5700_);
                            lean_dec(v_size_5700_);
                            v___x_5763_ = lean_nat_add(v___x_5762_, v_size_5699_);
                            lean_dec(v___x_5762_);
                            v___x_5764_ = lean_nat_add(v___x_5761_, v_size_5699_);
                            v___x_5765_ = lean_nat_add(v___x_5764_, v_size_5718_);
                            lean_dec(v___x_5764_);
                            lean_inc_ref(v_r_5693_);
                            if v_isShared_5716_ == 0 {
                                lean_ctor_set(v___x_5715_, 4, v_r_5693_);
                                lean_ctor_set(v___x_5715_, 3, v_r_5704_);
                                lean_ctor_set(v___x_5715_, 2, v_v_5691_);
                                lean_ctor_set(v___x_5715_, 1, v_k_5690_);
                                lean_ctor_set(v___x_5715_, 0, v___x_5765_);
                                v___x_5767_ = v___x_5715_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_5780_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_5780_, 0, v___x_5765_);
                                lean_ctor_set(v_reuseFailAlloc_5780_, 1, v_k_5690_);
                                lean_ctor_set(v_reuseFailAlloc_5780_, 2, v_v_5691_);
                                lean_ctor_set(v_reuseFailAlloc_5780_, 3, v_r_5704_);
                                lean_ctor_set(v_reuseFailAlloc_5780_, 4, v_r_5693_);
                                v___x_5767_ = v_reuseFailAlloc_5780_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_l_5703_, 5);
                        lean_del_object(v___x_5715_);
                        lean_dec(v_v_5702_);
                        lean_dec(v_k_5701_);
                        lean_dec(v_size_5700_);
                        lean_dec_ref_known(v_r_5693_, 5);
                        lean_del_object(v___x_5695_);
                        lean_dec(v_v_5691_);
                        lean_dec(v_k_5690_);
                        v___x_5781_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__3_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__3);
                        v___x_5782_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2___redArg(v___x_5781_);
                        return v___x_5782_;
                    }
                } else {
                    lean_del_object(v___x_5715_);
                    lean_dec(v_r_5704_);
                    lean_dec(v_v_5702_);
                    lean_dec(v_k_5701_);
                    lean_dec(v_size_5700_);
                    lean_dec_ref_known(v_r_5693_, 5);
                    lean_del_object(v___x_5695_);
                    lean_dec(v_v_5691_);
                    lean_dec(v_k_5690_);
                    v___x_5783_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__4), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__4_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__4);
                    v___x_5784_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2___redArg(v___x_5783_);
                    return v___x_5784_;
                }
            }
            4 => {
                v___x_5729_ = lean_unsigned_to_nat(1);
                v___x_5730_ = lean_nat_add(v___x_5729_, v_size_5700_);
                lean_dec(v_size_5700_);
                v___x_5731_ = lean_nat_add(v___x_5730_, v_size_5699_);
                lean_dec(v___x_5730_);
                v___x_5743_ = lean_nat_add(v___x_5729_, v_size_5717_);
                if lean_obj_tag(v_l_5721_) == 0 {
                    v_size_5753_ = lean_ctor_get(v_l_5721_, 0);
                    lean_inc(v_size_5753_);
                    v___y_5745_ = v_size_5753_;
                    state = 8;
                    continue;
                } else {
                    v___x_5754_ = lean_unsigned_to_nat(0);
                    v___y_5745_ = v___x_5754_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_5736_ = lean_nat_add(v___y_5733_, v___y_5735_);
                lean_dec(v___y_5735_);
                lean_dec(v___y_5733_);
                if v_isShared_5728_ == 0 {
                    lean_ctor_set(v___x_5727_, 4, v_r_5693_);
                    lean_ctor_set(v___x_5727_, 3, v_r_5722_);
                    lean_ctor_set(v___x_5727_, 2, v_v_5691_);
                    lean_ctor_set(v___x_5727_, 1, v_k_5690_);
                    lean_ctor_set(v___x_5727_, 0, v___x_5736_);
                    v___x_5738_ = v___x_5727_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5742_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5742_, 0, v___x_5736_);
                    lean_ctor_set(v_reuseFailAlloc_5742_, 1, v_k_5690_);
                    lean_ctor_set(v_reuseFailAlloc_5742_, 2, v_v_5691_);
                    lean_ctor_set(v_reuseFailAlloc_5742_, 3, v_r_5722_);
                    lean_ctor_set(v_reuseFailAlloc_5742_, 4, v_r_5693_);
                    v___x_5738_ = v_reuseFailAlloc_5742_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_5716_ == 0 {
                    lean_ctor_set(v___x_5715_, 4, v___x_5738_);
                    lean_ctor_set(v___x_5715_, 3, v___y_5734_);
                    lean_ctor_set(v___x_5715_, 2, v_v_5720_);
                    lean_ctor_set(v___x_5715_, 1, v_k_5719_);
                    lean_ctor_set(v___x_5715_, 0, v___x_5731_);
                    v___x_5740_ = v___x_5715_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5741_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5741_, 0, v___x_5731_);
                    lean_ctor_set(v_reuseFailAlloc_5741_, 1, v_k_5719_);
                    lean_ctor_set(v_reuseFailAlloc_5741_, 2, v_v_5720_);
                    lean_ctor_set(v_reuseFailAlloc_5741_, 3, v___y_5734_);
                    lean_ctor_set(v_reuseFailAlloc_5741_, 4, v___x_5738_);
                    v___x_5740_ = v_reuseFailAlloc_5741_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5740_;
            }
            8 => {
                v___x_5746_ = lean_nat_add(v___x_5743_, v___y_5745_);
                lean_dec(v___y_5745_);
                lean_dec(v___x_5743_);
                if v_isShared_5696_ == 0 {
                    lean_ctor_set(v___x_5695_, 4, v_l_5721_);
                    lean_ctor_set(v___x_5695_, 3, v_l_5703_);
                    lean_ctor_set(v___x_5695_, 2, v_v_5702_);
                    lean_ctor_set(v___x_5695_, 1, v_k_5701_);
                    lean_ctor_set(v___x_5695_, 0, v___x_5746_);
                    v___x_5748_ = v___x_5695_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5752_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5752_, 0, v___x_5746_);
                    lean_ctor_set(v_reuseFailAlloc_5752_, 1, v_k_5701_);
                    lean_ctor_set(v_reuseFailAlloc_5752_, 2, v_v_5702_);
                    lean_ctor_set(v_reuseFailAlloc_5752_, 3, v_l_5703_);
                    lean_ctor_set(v_reuseFailAlloc_5752_, 4, v_l_5721_);
                    v___x_5748_ = v_reuseFailAlloc_5752_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_5749_ = lean_nat_add(v___x_5729_, v_size_5699_);
                if lean_obj_tag(v_r_5722_) == 0 {
                    v_size_5750_ = lean_ctor_get(v_r_5722_, 0);
                    lean_inc(v_size_5750_);
                    v___y_5733_ = v___x_5749_;
                    v___y_5734_ = v___x_5748_;
                    v___y_5735_ = v_size_5750_;
                    state = 5;
                    continue;
                } else {
                    v___x_5751_ = lean_unsigned_to_nat(0);
                    v___y_5733_ = v___x_5749_;
                    v___y_5734_ = v___x_5748_;
                    v___y_5735_ = v___x_5751_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_5774_ = (!lean_is_exclusive(v_r_5693_)) as u8;
                if v_isSharedCheck_5774_ == 0 {
                    v_unused_5775_ = lean_ctor_get(v_r_5693_, 4);
                    lean_dec(v_unused_5775_);
                    v_unused_5776_ = lean_ctor_get(v_r_5693_, 3);
                    lean_dec(v_unused_5776_);
                    v_unused_5777_ = lean_ctor_get(v_r_5693_, 2);
                    lean_dec(v_unused_5777_);
                    v_unused_5778_ = lean_ctor_get(v_r_5693_, 1);
                    lean_dec(v_unused_5778_);
                    v_unused_5779_ = lean_ctor_get(v_r_5693_, 0);
                    lean_dec(v_unused_5779_);
                    v___x_5769_ = v_r_5693_;
                    v_isShared_5770_ = v_isSharedCheck_5774_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_r_5693_);
                    v___x_5769_ = lean_box(0);
                    v_isShared_5770_ = v_isSharedCheck_5774_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_5770_ == 0 {
                    lean_ctor_set(v___x_5769_, 4, v___x_5767_);
                    lean_ctor_set(v___x_5769_, 3, v_l_5703_);
                    lean_ctor_set(v___x_5769_, 2, v_v_5702_);
                    lean_ctor_set(v___x_5769_, 1, v_k_5701_);
                    lean_ctor_set(v___x_5769_, 0, v___x_5763_);
                    v___x_5772_ = v___x_5769_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5773_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5773_, 0, v___x_5763_);
                    lean_ctor_set(v_reuseFailAlloc_5773_, 1, v_k_5701_);
                    lean_ctor_set(v_reuseFailAlloc_5773_, 2, v_v_5702_);
                    lean_ctor_set(v_reuseFailAlloc_5773_, 3, v_l_5703_);
                    lean_ctor_set(v_reuseFailAlloc_5773_, 4, v___x_5767_);
                    v___x_5772_ = v_reuseFailAlloc_5773_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5772_;
            }
            13 => {
                return v___x_5795_;
            }
            14 => {
                v_size_5805_ = lean_ctor_get(v_r_5798_, 0);
                v___x_5806_ = lean_unsigned_to_nat(1);
                v___x_5807_ = lean_nat_add(v___x_5806_, v_size_5799_);
                lean_dec(v_size_5799_);
                v___x_5808_ = lean_nat_add(v___x_5806_, v_size_5805_);
                if v_isShared_5804_ == 0 {
                    lean_ctor_set(v___x_5803_, 4, v_r_5693_);
                    lean_ctor_set(v___x_5803_, 3, v_r_5798_);
                    lean_ctor_set(v___x_5803_, 2, v_v_5691_);
                    lean_ctor_set(v___x_5803_, 1, v_k_5690_);
                    lean_ctor_set(v___x_5803_, 0, v___x_5808_);
                    v___x_5810_ = v___x_5803_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5814_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5814_, 0, v___x_5808_);
                    lean_ctor_set(v_reuseFailAlloc_5814_, 1, v_k_5690_);
                    lean_ctor_set(v_reuseFailAlloc_5814_, 2, v_v_5691_);
                    lean_ctor_set(v_reuseFailAlloc_5814_, 3, v_r_5798_);
                    lean_ctor_set(v_reuseFailAlloc_5814_, 4, v_r_5693_);
                    v___x_5810_ = v_reuseFailAlloc_5814_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_5696_ == 0 {
                    lean_ctor_set(v___x_5695_, 4, v___x_5810_);
                    lean_ctor_set(v___x_5695_, 3, v_l_5797_);
                    lean_ctor_set(v___x_5695_, 2, v_v_5801_);
                    lean_ctor_set(v___x_5695_, 1, v_k_5800_);
                    lean_ctor_set(v___x_5695_, 0, v___x_5807_);
                    v___x_5812_ = v___x_5695_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5813_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5813_, 0, v___x_5807_);
                    lean_ctor_set(v_reuseFailAlloc_5813_, 1, v_k_5800_);
                    lean_ctor_set(v_reuseFailAlloc_5813_, 2, v_v_5801_);
                    lean_ctor_set(v_reuseFailAlloc_5813_, 3, v_l_5797_);
                    lean_ctor_set(v_reuseFailAlloc_5813_, 4, v___x_5810_);
                    v___x_5812_ = v_reuseFailAlloc_5813_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5812_;
            }
            17 => {
                v___x_5823_ = lean_unsigned_to_nat(3);
                v___x_5824_ = lean_unsigned_to_nat(1);
                if v_isShared_5822_ == 0 {
                    lean_ctor_set(v___x_5821_, 3, v_r_5798_);
                    lean_ctor_set(v___x_5821_, 2, v_v_5691_);
                    lean_ctor_set(v___x_5821_, 1, v_k_5690_);
                    lean_ctor_set(v___x_5821_, 0, v___x_5824_);
                    v___x_5826_ = v___x_5821_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5830_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5830_, 0, v___x_5824_);
                    lean_ctor_set(v_reuseFailAlloc_5830_, 1, v_k_5690_);
                    lean_ctor_set(v_reuseFailAlloc_5830_, 2, v_v_5691_);
                    lean_ctor_set(v_reuseFailAlloc_5830_, 3, v_r_5798_);
                    lean_ctor_set(v_reuseFailAlloc_5830_, 4, v_r_5798_);
                    v___x_5826_ = v_reuseFailAlloc_5830_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_5696_ == 0 {
                    lean_ctor_set(v___x_5695_, 4, v___x_5826_);
                    lean_ctor_set(v___x_5695_, 3, v_l_5797_);
                    lean_ctor_set(v___x_5695_, 2, v_v_5819_);
                    lean_ctor_set(v___x_5695_, 1, v_k_5818_);
                    lean_ctor_set(v___x_5695_, 0, v___x_5823_);
                    v___x_5828_ = v___x_5695_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5829_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5829_, 0, v___x_5823_);
                    lean_ctor_set(v_reuseFailAlloc_5829_, 1, v_k_5818_);
                    lean_ctor_set(v_reuseFailAlloc_5829_, 2, v_v_5819_);
                    lean_ctor_set(v_reuseFailAlloc_5829_, 3, v_l_5797_);
                    lean_ctor_set(v_reuseFailAlloc_5829_, 4, v___x_5826_);
                    v___x_5828_ = v_reuseFailAlloc_5829_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_5828_;
            }
            20 => {
                v_k_5841_ = lean_ctor_get(v_r_5835_, 1);
                v_v_5842_ = lean_ctor_get(v_r_5835_, 2);
                v_isSharedCheck_5857_ = (!lean_is_exclusive(v_r_5835_)) as u8;
                if v_isSharedCheck_5857_ == 0 {
                    v_unused_5858_ = lean_ctor_get(v_r_5835_, 4);
                    lean_dec(v_unused_5858_);
                    v_unused_5859_ = lean_ctor_get(v_r_5835_, 3);
                    lean_dec(v_unused_5859_);
                    v_unused_5860_ = lean_ctor_get(v_r_5835_, 0);
                    lean_dec(v_unused_5860_);
                    v___x_5844_ = v_r_5835_;
                    v_isShared_5845_ = v_isSharedCheck_5857_;
                    state = 21;
                    continue;
                } else {
                    lean_inc(v_v_5842_);
                    lean_inc(v_k_5841_);
                    lean_dec(v_r_5835_);
                    v___x_5844_ = lean_box(0);
                    v_isShared_5845_ = v_isSharedCheck_5857_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_5846_ = lean_unsigned_to_nat(3);
                v___x_5847_ = lean_unsigned_to_nat(1);
                if v_isShared_5845_ == 0 {
                    lean_ctor_set(v___x_5844_, 4, v_l_5797_);
                    lean_ctor_set(v___x_5844_, 3, v_l_5797_);
                    lean_ctor_set(v___x_5844_, 2, v_v_5837_);
                    lean_ctor_set(v___x_5844_, 1, v_k_5836_);
                    lean_ctor_set(v___x_5844_, 0, v___x_5847_);
                    v___x_5849_ = v___x_5844_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5856_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5856_, 0, v___x_5847_);
                    lean_ctor_set(v_reuseFailAlloc_5856_, 1, v_k_5836_);
                    lean_ctor_set(v_reuseFailAlloc_5856_, 2, v_v_5837_);
                    lean_ctor_set(v_reuseFailAlloc_5856_, 3, v_l_5797_);
                    lean_ctor_set(v_reuseFailAlloc_5856_, 4, v_l_5797_);
                    v___x_5849_ = v_reuseFailAlloc_5856_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_5840_ == 0 {
                    lean_ctor_set(v___x_5839_, 4, v_l_5797_);
                    lean_ctor_set(v___x_5839_, 2, v_v_5691_);
                    lean_ctor_set(v___x_5839_, 1, v_k_5690_);
                    lean_ctor_set(v___x_5839_, 0, v___x_5847_);
                    v___x_5851_ = v___x_5839_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_5855_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5855_, 0, v___x_5847_);
                    lean_ctor_set(v_reuseFailAlloc_5855_, 1, v_k_5690_);
                    lean_ctor_set(v_reuseFailAlloc_5855_, 2, v_v_5691_);
                    lean_ctor_set(v_reuseFailAlloc_5855_, 3, v_l_5797_);
                    lean_ctor_set(v_reuseFailAlloc_5855_, 4, v_l_5797_);
                    v___x_5851_ = v_reuseFailAlloc_5855_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_5696_ == 0 {
                    lean_ctor_set(v___x_5695_, 4, v___x_5851_);
                    lean_ctor_set(v___x_5695_, 3, v___x_5849_);
                    lean_ctor_set(v___x_5695_, 2, v_v_5842_);
                    lean_ctor_set(v___x_5695_, 1, v_k_5841_);
                    lean_ctor_set(v___x_5695_, 0, v___x_5846_);
                    v___x_5853_ = v___x_5695_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5854_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5854_, 0, v___x_5846_);
                    lean_ctor_set(v_reuseFailAlloc_5854_, 1, v_k_5841_);
                    lean_ctor_set(v_reuseFailAlloc_5854_, 2, v_v_5842_);
                    lean_ctor_set(v_reuseFailAlloc_5854_, 3, v___x_5849_);
                    lean_ctor_set(v_reuseFailAlloc_5854_, 4, v___x_5851_);
                    v___x_5853_ = v_reuseFailAlloc_5854_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5853_;
            }
            25 => {
                return v___x_5867_;
            }
            26 => {
                return v___x_5871_;
            }
            27 => {
                return v___x_5874_;
            }
            28 => {
                return v___x_5890_;
            }
            29 => {
                if lean_obj_tag(v_l_5881_) == 0 {
                    if lean_obj_tag(v_r_5882_) == 0 {
                        v_size_5895_ = lean_ctor_get(v_l_5881_, 0);
                        v_k_5896_ = lean_ctor_get(v_l_5881_, 1);
                        v_v_5897_ = lean_ctor_get(v_l_5881_, 2);
                        v_l_5898_ = lean_ctor_get(v_l_5881_, 3);
                        v_r_5899_ = lean_ctor_get(v_l_5881_, 4);
                        v_size_5900_ = lean_ctor_get(v_r_5882_, 0);
                        v___x_5901_ = lean_unsigned_to_nat(2);
                        v___x_5902_ = lean_nat_mul(v___x_5901_, v_size_5900_);
                        v___x_5903_ = lean_nat_dec_lt(v_size_5895_, v___x_5902_);
                        lean_dec(v___x_5902_);
                        if v___x_5903_ == 0 {
                            lean_inc(v_r_5899_);
                            lean_inc(v_l_5898_);
                            lean_inc(v_v_5897_);
                            lean_inc(v_k_5896_);
                            v_isSharedCheck_5932_ = (!lean_is_exclusive(v_l_5881_)) as u8;
                            if v_isSharedCheck_5932_ == 0 {
                                v_unused_5933_ = lean_ctor_get(v_l_5881_, 4);
                                lean_dec(v_unused_5933_);
                                v_unused_5934_ = lean_ctor_get(v_l_5881_, 3);
                                lean_dec(v_unused_5934_);
                                v_unused_5935_ = lean_ctor_get(v_l_5881_, 2);
                                lean_dec(v_unused_5935_);
                                v_unused_5936_ = lean_ctor_get(v_l_5881_, 1);
                                lean_dec(v_unused_5936_);
                                v_unused_5937_ = lean_ctor_get(v_l_5881_, 0);
                                lean_dec(v_unused_5937_);
                                v___x_5905_ = v_l_5881_;
                                v_isShared_5906_ = v_isSharedCheck_5932_;
                                state = 30;
                                continue;
                            } else {
                                lean_dec(v_l_5881_);
                                v___x_5905_ = lean_box(0);
                                v_isShared_5906_ = v_isSharedCheck_5932_;
                                state = 30;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_5695_);
                            v___x_5938_ = lean_unsigned_to_nat(1);
                            v___x_5939_ = lean_nat_add(v___x_5938_, v_size_5877_);
                            v___x_5940_ = lean_nat_add(v___x_5939_, v_size_5878_);
                            lean_dec(v_size_5878_);
                            v___x_5941_ = lean_nat_add(v___x_5939_, v_size_5895_);
                            lean_dec(v___x_5939_);
                            lean_inc_ref(v_l_5692_);
                            if v_isShared_5894_ == 0 {
                                lean_ctor_set(v___x_5893_, 4, v_l_5881_);
                                lean_ctor_set(v___x_5893_, 3, v_l_5692_);
                                lean_ctor_set(v___x_5893_, 2, v_v_5691_);
                                lean_ctor_set(v___x_5893_, 1, v_k_5690_);
                                lean_ctor_set(v___x_5893_, 0, v___x_5941_);
                                v___x_5943_ = v___x_5893_;
                                state = 36;
                                continue;
                            } else {
                                v_reuseFailAlloc_5956_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_5956_, 0, v___x_5941_);
                                lean_ctor_set(v_reuseFailAlloc_5956_, 1, v_k_5690_);
                                lean_ctor_set(v_reuseFailAlloc_5956_, 2, v_v_5691_);
                                lean_ctor_set(v_reuseFailAlloc_5956_, 3, v_l_5692_);
                                lean_ctor_set(v_reuseFailAlloc_5956_, 4, v_l_5881_);
                                v___x_5943_ = v_reuseFailAlloc_5956_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_l_5881_, 5);
                        lean_del_object(v___x_5893_);
                        lean_dec(v_v_5880_);
                        lean_dec(v_k_5879_);
                        lean_dec(v_size_5878_);
                        lean_dec_ref_known(v_l_5692_, 5);
                        lean_del_object(v___x_5695_);
                        lean_dec(v_v_5691_);
                        lean_dec(v_k_5690_);
                        v___x_5957_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__7);
                        v___x_5958_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2___redArg(v___x_5957_);
                        return v___x_5958_;
                    }
                } else {
                    lean_del_object(v___x_5893_);
                    lean_dec(v_r_5882_);
                    lean_dec(v_v_5880_);
                    lean_dec(v_k_5879_);
                    lean_dec(v_size_5878_);
                    lean_dec_ref_known(v_l_5692_, 5);
                    lean_del_object(v___x_5695_);
                    lean_dec(v_v_5691_);
                    lean_dec(v_k_5690_);
                    v___x_5959_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__8), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__8_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg___closed__8);
                    v___x_5960_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2___redArg(v___x_5959_);
                    return v___x_5960_;
                }
            }
            30 => {
                v___x_5907_ = lean_unsigned_to_nat(1);
                v___x_5908_ = lean_nat_add(v___x_5907_, v_size_5877_);
                v___x_5909_ = lean_nat_add(v___x_5908_, v_size_5878_);
                lean_dec(v_size_5878_);
                if lean_obj_tag(v_l_5898_) == 0 {
                    v_size_5930_ = lean_ctor_get(v_l_5898_, 0);
                    lean_inc(v_size_5930_);
                    v___y_5922_ = v_size_5930_;
                    state = 34;
                    continue;
                } else {
                    v___x_5931_ = lean_unsigned_to_nat(0);
                    v___y_5922_ = v___x_5931_;
                    state = 34;
                    continue;
                }
            }
            31 => {
                v___x_5914_ = lean_nat_add(v___y_5911_, v___y_5913_);
                lean_dec(v___y_5913_);
                lean_dec(v___y_5911_);
                if v_isShared_5906_ == 0 {
                    lean_ctor_set(v___x_5905_, 4, v_r_5882_);
                    lean_ctor_set(v___x_5905_, 3, v_r_5899_);
                    lean_ctor_set(v___x_5905_, 2, v_v_5880_);
                    lean_ctor_set(v___x_5905_, 1, v_k_5879_);
                    lean_ctor_set(v___x_5905_, 0, v___x_5914_);
                    v___x_5916_ = v___x_5905_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_5920_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5920_, 0, v___x_5914_);
                    lean_ctor_set(v_reuseFailAlloc_5920_, 1, v_k_5879_);
                    lean_ctor_set(v_reuseFailAlloc_5920_, 2, v_v_5880_);
                    lean_ctor_set(v_reuseFailAlloc_5920_, 3, v_r_5899_);
                    lean_ctor_set(v_reuseFailAlloc_5920_, 4, v_r_5882_);
                    v___x_5916_ = v_reuseFailAlloc_5920_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_5894_ == 0 {
                    lean_ctor_set(v___x_5893_, 4, v___x_5916_);
                    lean_ctor_set(v___x_5893_, 3, v___y_5912_);
                    lean_ctor_set(v___x_5893_, 2, v_v_5897_);
                    lean_ctor_set(v___x_5893_, 1, v_k_5896_);
                    lean_ctor_set(v___x_5893_, 0, v___x_5909_);
                    v___x_5918_ = v___x_5893_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_5919_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5919_, 0, v___x_5909_);
                    lean_ctor_set(v_reuseFailAlloc_5919_, 1, v_k_5896_);
                    lean_ctor_set(v_reuseFailAlloc_5919_, 2, v_v_5897_);
                    lean_ctor_set(v_reuseFailAlloc_5919_, 3, v___y_5912_);
                    lean_ctor_set(v_reuseFailAlloc_5919_, 4, v___x_5916_);
                    v___x_5918_ = v_reuseFailAlloc_5919_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_5918_;
            }
            34 => {
                v___x_5923_ = lean_nat_add(v___x_5908_, v___y_5922_);
                lean_dec(v___y_5922_);
                lean_dec(v___x_5908_);
                if v_isShared_5696_ == 0 {
                    lean_ctor_set(v___x_5695_, 4, v_l_5898_);
                    lean_ctor_set(v___x_5695_, 0, v___x_5923_);
                    v___x_5925_ = v___x_5695_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_5929_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5929_, 0, v___x_5923_);
                    lean_ctor_set(v_reuseFailAlloc_5929_, 1, v_k_5690_);
                    lean_ctor_set(v_reuseFailAlloc_5929_, 2, v_v_5691_);
                    lean_ctor_set(v_reuseFailAlloc_5929_, 3, v_l_5692_);
                    lean_ctor_set(v_reuseFailAlloc_5929_, 4, v_l_5898_);
                    v___x_5925_ = v_reuseFailAlloc_5929_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_5926_ = lean_nat_add(v___x_5907_, v_size_5900_);
                if lean_obj_tag(v_r_5899_) == 0 {
                    v_size_5927_ = lean_ctor_get(v_r_5899_, 0);
                    lean_inc(v_size_5927_);
                    v___y_5911_ = v___x_5926_;
                    v___y_5912_ = v___x_5925_;
                    v___y_5913_ = v_size_5927_;
                    state = 31;
                    continue;
                } else {
                    v___x_5928_ = lean_unsigned_to_nat(0);
                    v___y_5911_ = v___x_5926_;
                    v___y_5912_ = v___x_5925_;
                    v___y_5913_ = v___x_5928_;
                    state = 31;
                    continue;
                }
            }
            36 => {
                v_isSharedCheck_5950_ = (!lean_is_exclusive(v_l_5692_)) as u8;
                if v_isSharedCheck_5950_ == 0 {
                    v_unused_5951_ = lean_ctor_get(v_l_5692_, 4);
                    lean_dec(v_unused_5951_);
                    v_unused_5952_ = lean_ctor_get(v_l_5692_, 3);
                    lean_dec(v_unused_5952_);
                    v_unused_5953_ = lean_ctor_get(v_l_5692_, 2);
                    lean_dec(v_unused_5953_);
                    v_unused_5954_ = lean_ctor_get(v_l_5692_, 1);
                    lean_dec(v_unused_5954_);
                    v_unused_5955_ = lean_ctor_get(v_l_5692_, 0);
                    lean_dec(v_unused_5955_);
                    v___x_5945_ = v_l_5692_;
                    v_isShared_5946_ = v_isSharedCheck_5950_;
                    state = 37;
                    continue;
                } else {
                    lean_dec(v_l_5692_);
                    v___x_5945_ = lean_box(0);
                    v_isShared_5946_ = v_isSharedCheck_5950_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_5946_ == 0 {
                    lean_ctor_set(v___x_5945_, 4, v_r_5882_);
                    lean_ctor_set(v___x_5945_, 3, v___x_5943_);
                    lean_ctor_set(v___x_5945_, 2, v_v_5880_);
                    lean_ctor_set(v___x_5945_, 1, v_k_5879_);
                    lean_ctor_set(v___x_5945_, 0, v___x_5940_);
                    v___x_5948_ = v___x_5945_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_5949_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5949_, 0, v___x_5940_);
                    lean_ctor_set(v_reuseFailAlloc_5949_, 1, v_k_5879_);
                    lean_ctor_set(v_reuseFailAlloc_5949_, 2, v_v_5880_);
                    lean_ctor_set(v_reuseFailAlloc_5949_, 3, v___x_5943_);
                    lean_ctor_set(v_reuseFailAlloc_5949_, 4, v_r_5882_);
                    v___x_5948_ = v_reuseFailAlloc_5949_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_5948_;
            }
            39 => {
                return v___x_5971_;
            }
            40 => {
                v_size_5981_ = lean_ctor_get(v_l_5973_, 0);
                v___x_5982_ = lean_unsigned_to_nat(1);
                v___x_5983_ = lean_nat_add(v___x_5982_, v_size_5975_);
                lean_dec(v_size_5975_);
                v___x_5984_ = lean_nat_add(v___x_5982_, v_size_5981_);
                if v_isShared_5980_ == 0 {
                    lean_ctor_set(v___x_5979_, 4, v_l_5973_);
                    lean_ctor_set(v___x_5979_, 3, v_l_5692_);
                    lean_ctor_set(v___x_5979_, 2, v_v_5691_);
                    lean_ctor_set(v___x_5979_, 1, v_k_5690_);
                    lean_ctor_set(v___x_5979_, 0, v___x_5984_);
                    v___x_5986_ = v___x_5979_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_5990_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5990_, 0, v___x_5984_);
                    lean_ctor_set(v_reuseFailAlloc_5990_, 1, v_k_5690_);
                    lean_ctor_set(v_reuseFailAlloc_5990_, 2, v_v_5691_);
                    lean_ctor_set(v_reuseFailAlloc_5990_, 3, v_l_5692_);
                    lean_ctor_set(v_reuseFailAlloc_5990_, 4, v_l_5973_);
                    v___x_5986_ = v_reuseFailAlloc_5990_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                if v_isShared_5696_ == 0 {
                    lean_ctor_set(v___x_5695_, 4, v_r_5974_);
                    lean_ctor_set(v___x_5695_, 3, v___x_5986_);
                    lean_ctor_set(v___x_5695_, 2, v_v_5977_);
                    lean_ctor_set(v___x_5695_, 1, v_k_5976_);
                    lean_ctor_set(v___x_5695_, 0, v___x_5983_);
                    v___x_5988_ = v___x_5695_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_5989_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5989_, 0, v___x_5983_);
                    lean_ctor_set(v_reuseFailAlloc_5989_, 1, v_k_5976_);
                    lean_ctor_set(v_reuseFailAlloc_5989_, 2, v_v_5977_);
                    lean_ctor_set(v_reuseFailAlloc_5989_, 3, v___x_5986_);
                    lean_ctor_set(v_reuseFailAlloc_5989_, 4, v_r_5974_);
                    v___x_5988_ = v_reuseFailAlloc_5989_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_5988_;
            }
            43 => {
                v_k_5999_ = lean_ctor_get(v_l_5973_, 1);
                v_v_6000_ = lean_ctor_get(v_l_5973_, 2);
                v_isSharedCheck_6015_ = (!lean_is_exclusive(v_l_5973_)) as u8;
                if v_isSharedCheck_6015_ == 0 {
                    v_unused_6016_ = lean_ctor_get(v_l_5973_, 4);
                    lean_dec(v_unused_6016_);
                    v_unused_6017_ = lean_ctor_get(v_l_5973_, 3);
                    lean_dec(v_unused_6017_);
                    v_unused_6018_ = lean_ctor_get(v_l_5973_, 0);
                    lean_dec(v_unused_6018_);
                    v___x_6002_ = v_l_5973_;
                    v_isShared_6003_ = v_isSharedCheck_6015_;
                    state = 44;
                    continue;
                } else {
                    lean_inc(v_v_6000_);
                    lean_inc(v_k_5999_);
                    lean_dec(v_l_5973_);
                    v___x_6002_ = lean_box(0);
                    v_isShared_6003_ = v_isSharedCheck_6015_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                v___x_6004_ = lean_unsigned_to_nat(3);
                v___x_6005_ = lean_unsigned_to_nat(1);
                if v_isShared_6003_ == 0 {
                    lean_ctor_set(v___x_6002_, 4, v_r_5974_);
                    lean_ctor_set(v___x_6002_, 3, v_r_5974_);
                    lean_ctor_set(v___x_6002_, 2, v_v_5691_);
                    lean_ctor_set(v___x_6002_, 1, v_k_5690_);
                    lean_ctor_set(v___x_6002_, 0, v___x_6005_);
                    v___x_6007_ = v___x_6002_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_6014_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6014_, 0, v___x_6005_);
                    lean_ctor_set(v_reuseFailAlloc_6014_, 1, v_k_5690_);
                    lean_ctor_set(v_reuseFailAlloc_6014_, 2, v_v_5691_);
                    lean_ctor_set(v_reuseFailAlloc_6014_, 3, v_r_5974_);
                    lean_ctor_set(v_reuseFailAlloc_6014_, 4, v_r_5974_);
                    v___x_6007_ = v_reuseFailAlloc_6014_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_5998_ == 0 {
                    lean_ctor_set(v___x_5997_, 3, v_r_5974_);
                    lean_ctor_set(v___x_5997_, 0, v___x_6005_);
                    v___x_6009_ = v___x_5997_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_6013_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6013_, 0, v___x_6005_);
                    lean_ctor_set(v_reuseFailAlloc_6013_, 1, v_k_5994_);
                    lean_ctor_set(v_reuseFailAlloc_6013_, 2, v_v_5995_);
                    lean_ctor_set(v_reuseFailAlloc_6013_, 3, v_r_5974_);
                    lean_ctor_set(v_reuseFailAlloc_6013_, 4, v_r_5974_);
                    v___x_6009_ = v_reuseFailAlloc_6013_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                if v_isShared_5696_ == 0 {
                    lean_ctor_set(v___x_5695_, 4, v___x_6009_);
                    lean_ctor_set(v___x_5695_, 3, v___x_6007_);
                    lean_ctor_set(v___x_5695_, 2, v_v_6000_);
                    lean_ctor_set(v___x_5695_, 1, v_k_5999_);
                    lean_ctor_set(v___x_5695_, 0, v___x_6004_);
                    v___x_6011_ = v___x_5695_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_6012_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6012_, 0, v___x_6004_);
                    lean_ctor_set(v_reuseFailAlloc_6012_, 1, v_k_5999_);
                    lean_ctor_set(v_reuseFailAlloc_6012_, 2, v_v_6000_);
                    lean_ctor_set(v_reuseFailAlloc_6012_, 3, v___x_6007_);
                    lean_ctor_set(v_reuseFailAlloc_6012_, 4, v___x_6009_);
                    v___x_6011_ = v_reuseFailAlloc_6012_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_6011_;
            }
            48 => {
                v___x_6029_ = lean_unsigned_to_nat(3);
                v___x_6030_ = lean_unsigned_to_nat(1);
                if v_isShared_6028_ == 0 {
                    lean_ctor_set(v___x_6027_, 4, v_l_5973_);
                    lean_ctor_set(v___x_6027_, 2, v_v_5691_);
                    lean_ctor_set(v___x_6027_, 1, v_k_5690_);
                    lean_ctor_set(v___x_6027_, 0, v___x_6030_);
                    v___x_6032_ = v___x_6027_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_6036_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6036_, 0, v___x_6030_);
                    lean_ctor_set(v_reuseFailAlloc_6036_, 1, v_k_5690_);
                    lean_ctor_set(v_reuseFailAlloc_6036_, 2, v_v_5691_);
                    lean_ctor_set(v_reuseFailAlloc_6036_, 3, v_l_5973_);
                    lean_ctor_set(v_reuseFailAlloc_6036_, 4, v_l_5973_);
                    v___x_6032_ = v_reuseFailAlloc_6036_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                if v_isShared_5696_ == 0 {
                    lean_ctor_set(v___x_5695_, 4, v_r_6023_);
                    lean_ctor_set(v___x_5695_, 3, v___x_6032_);
                    lean_ctor_set(v___x_5695_, 2, v_v_6025_);
                    lean_ctor_set(v___x_5695_, 1, v_k_6024_);
                    lean_ctor_set(v___x_5695_, 0, v___x_6029_);
                    v___x_6034_ = v___x_5695_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_6035_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6035_, 0, v___x_6029_);
                    lean_ctor_set(v_reuseFailAlloc_6035_, 1, v_k_6024_);
                    lean_ctor_set(v_reuseFailAlloc_6035_, 2, v_v_6025_);
                    lean_ctor_set(v_reuseFailAlloc_6035_, 3, v___x_6032_);
                    lean_ctor_set(v_reuseFailAlloc_6035_, 4, v_r_6023_);
                    v___x_6034_ = v_reuseFailAlloc_6035_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_6034_;
            }
            51 => {
                return v___x_6043_;
            }
            52 => {
                return v___x_6047_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__4(
    mut v_sz_6052_: usize,
    mut v_i_6053_: usize,
    mut v_bs_6054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6055_: u8 = 0;
    let mut v_v_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: usize = 0;
    let mut v___x_6061_: usize = 0;
    let mut v___x_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6055_ = lean_usize_dec_lt(v_i_6053_, v_sz_6052_);
                if v___x_6055_ == 0 {
                    return v_bs_6054_;
                } else {
                    v_v_6056_ = lean_array_uget(v_bs_6054_, v_i_6053_);
                    v___x_6057_ = lean_unsigned_to_nat(0);
                    v_bs_x27_6058_ = lean_array_uset(v_bs_6054_, v_i_6053_, v___x_6057_);
                    v___x_6059_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_6059_, 0, v_v_6056_);
                    v___x_6060_ = 1usize;
                    v___x_6061_ = lean_usize_add(v_i_6053_, v___x_6060_);
                    v___x_6062_ = lean_array_uset(v_bs_x27_6058_, v_i_6053_, v___x_6059_);
                    v_i_6053_ = v___x_6061_;
                    v_bs_6054_ = v___x_6062_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__4___boxed(
    mut v_sz_6064_: *mut LeanObject,
    mut v_i_6065_: *mut LeanObject,
    mut v_bs_6066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6067_: usize = 0;
    let mut v_i_boxed_6068_: usize = 0;
    let mut v_res_6069_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6067_ = lean_unbox_usize(v_sz_6064_);
    lean_dec(v_sz_6064_);
    v_i_boxed_6068_ = lean_unbox_usize(v_i_6065_);
    lean_dec(v_i_6065_);
    v_res_6069_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__4(v_sz_boxed_6067_, v_i_boxed_6068_, v_bs_6066_);
    return v_res_6069_;
}
pub unsafe fn l_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2(
    mut v_a_6070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_6071_: usize = 0;
    let mut v___x_6072_: usize = 0;
    let mut v___x_6073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6074_: *mut LeanObject = core::ptr::null_mut();
    v_sz_6071_ = lean_array_size(v_a_6070_);
    v___x_6072_ = 0usize;
    v___x_6073_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2_spec__4(v_sz_6071_, v___x_6072_, v_a_6070_);
    v___x_6074_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_6074_, 0, v___x_6073_);
    return v___x_6074_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4(
    mut v_init_6075_: *mut LeanObject,
    mut v_x_6076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_6077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: u8 = 0;
    let mut v___x_6083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6076_) == 0 {
                    v_k_6077_ = lean_ctor_get(v_x_6076_, 1);
                    lean_inc(v_k_6077_);
                    v_v_6078_ = lean_ctor_get(v_x_6076_, 2);
                    lean_inc(v_v_6078_);
                    v_l_6079_ = lean_ctor_get(v_x_6076_, 3);
                    lean_inc(v_l_6079_);
                    v_r_6080_ = lean_ctor_get(v_x_6076_, 4);
                    lean_inc(v_r_6080_);
                    lean_dec_ref_known(v_x_6076_, 5);
                    v___x_6081_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4(v_init_6075_, v_l_6079_);
                    v___x_6082_ = 1;
                    v___x_6083_ = l_Lean_Name_toString(v_k_6077_, v___x_6082_);
                    v___x_6084_ = l_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2(
                        v_v_6078_,
                    );
                    v___x_6085_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg(v___x_6083_, v___x_6084_, v___x_6081_);
                    v_init_6075_ = v___x_6085_;
                    v_x_6076_ = v_r_6080_;
                    state = 0;
                    continue;
                } else {
                    return v_init_6075_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1(
    mut v_m_6087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut LeanObject = core::ptr::null_mut();
    v___x_6088_ = lean_box(1);
    v___x_6089_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4(v___x_6088_, v_m_6087_);
    v___x_6090_ = lean_alloc_ctor(5, 1, (0) as u32);
    lean_ctor_set(v___x_6090_, 0, v___x_6089_);
    return v___x_6090_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_instToJsonModuleSetup_toJson_spec__0(
    mut v_k_6091_: *mut LeanObject,
    mut v_x_6092_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6092_) == 0 {
        let mut v___x_6093_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_k_6091_);
        v___x_6093_ = lean_box(0);
        return v___x_6093_;
    } else {
        let mut v_val_6094_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6095_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6096_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6097_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6098_: *mut LeanObject = core::ptr::null_mut();
        v_val_6094_ = lean_ctor_get(v_x_6092_, 0);
        lean_inc(v_val_6094_);
        lean_dec_ref_known(v_x_6092_, 1);
        v___x_6095_ =
            l_Array_toJson___at___00Lean_instToJsonModuleHeader_toJson_spec__0(v_val_6094_);
        v___x_6096_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_6096_, 0, v_k_6091_);
        lean_ctor_set(v___x_6096_, 1, v___x_6095_);
        v___x_6097_ = lean_box(0);
        v___x_6098_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_6098_, 0, v___x_6096_);
        lean_ctor_set(v___x_6098_, 1, v___x_6097_);
        return v___x_6098_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__8_spec__11(
    mut v_init_6099_: *mut LeanObject,
    mut v_x_6100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: u8 = 0;
    let mut v___x_6107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_6112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6115_: u8 = 0;
    let mut v___x_6117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6119_: u8 = 0;
    let mut v_b_6120_: u8 = 0;
    let mut v___x_6122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6123_: u8 = 0;
    let mut v___x_6125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6127_: u8 = 0;
    let mut v_n_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6131_: u8 = 0;
    let mut v___x_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6136_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6100_) == 0 {
                    v_k_6101_ = lean_ctor_get(v_x_6100_, 1);
                    lean_inc(v_k_6101_);
                    v_v_6102_ = lean_ctor_get(v_x_6100_, 2);
                    lean_inc(v_v_6102_);
                    v_l_6103_ = lean_ctor_get(v_x_6100_, 3);
                    lean_inc(v_l_6103_);
                    v_r_6104_ = lean_ctor_get(v_x_6100_, 4);
                    lean_inc(v_r_6104_);
                    lean_dec_ref_known(v_x_6100_, 5);
                    v___x_6105_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__8_spec__11(v_init_6099_, v_l_6103_);
                    v___x_6106_ = 1;
                    v___x_6107_ = l_Lean_Name_toString(v_k_6101_, v___x_6106_);
                    match lean_obj_tag(v_v_6102_) {
                        0 => {
                            v_s_6112_ = lean_ctor_get(v_v_6102_, 0);
                            v_isSharedCheck_6119_ = (!lean_is_exclusive(v_v_6102_)) as u8;
                            if v_isSharedCheck_6119_ == 0 {
                                v___x_6114_ = v_v_6102_;
                                v_isShared_6115_ = v_isSharedCheck_6119_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_s_6112_);
                                lean_dec(v_v_6102_);
                                v___x_6114_ = lean_box(0);
                                v_isShared_6115_ = v_isSharedCheck_6119_;
                                state = 2;
                                continue;
                            }
                        }
                        1 => {
                            v_b_6120_ = lean_ctor_get_uint8(v_v_6102_, 0 as u32);
                            v_isSharedCheck_6127_ = (!lean_is_exclusive(v_v_6102_)) as u8;
                            if v_isSharedCheck_6127_ == 0 {
                                v___x_6122_ = v_v_6102_;
                                v_isShared_6123_ = v_isSharedCheck_6127_;
                                state = 4;
                                continue;
                            } else {
                                lean_dec(v_v_6102_);
                                v___x_6122_ = lean_box(0);
                                v_isShared_6123_ = v_isSharedCheck_6127_;
                                state = 4;
                                continue;
                            }
                        }
                        _ => {
                            v_n_6128_ = lean_ctor_get(v_v_6102_, 0);
                            v_isSharedCheck_6136_ = (!lean_is_exclusive(v_v_6102_)) as u8;
                            if v_isSharedCheck_6136_ == 0 {
                                v___x_6130_ = v_v_6102_;
                                v_isShared_6131_ = v_isSharedCheck_6136_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_n_6128_);
                                lean_dec(v_v_6102_);
                                v___x_6130_ = lean_box(0);
                                v_isShared_6131_ = v_isSharedCheck_6136_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    return v_init_6099_;
                }
            }
            1 => {
                v___x_6110_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg(v___x_6107_, v___y_6109_, v___x_6105_);
                v_init_6099_ = v___x_6110_;
                v_x_6100_ = v_r_6104_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_6115_ == 0 {
                    lean_ctor_set_tag(v___x_6114_, 3);
                    v___x_6117_ = v___x_6114_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6118_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6118_, 0, v_s_6112_);
                    v___x_6117_ = v_reuseFailAlloc_6118_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_6109_ = v___x_6117_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_6123_ == 0 {
                    v___x_6125_ = v___x_6122_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6126_ = lean_alloc_ctor(1, 0, (1) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6126_, 0 as u32, v_b_6120_);
                    v___x_6125_ = v_reuseFailAlloc_6126_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_6109_ = v___x_6125_;
                state = 1;
                continue;
            }
            6 => {
                v___x_6132_ = l_Lean_JsonNumber_fromNat(v_n_6128_);
                if v_isShared_6131_ == 0 {
                    lean_ctor_set(v___x_6130_, 0, v___x_6132_);
                    v___x_6134_ = v___x_6130_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6135_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6135_, 0, v___x_6132_);
                    v___x_6134_ = v_reuseFailAlloc_6135_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_6109_ = v___x_6134_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4(
    mut v_m_6137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut LeanObject = core::ptr::null_mut();
    v___x_6138_ = lean_box(1);
    v___x_6139_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__8_spec__11(v___x_6138_, v_m_6137_);
    v___x_6140_ = lean_alloc_ctor(5, 1, (0) as u32);
    lean_ctor_set(v___x_6140_, 0, v___x_6139_);
    return v___x_6140_;
}
pub unsafe fn l_Lean_instToJsonModuleSetup_toJson(
    mut v_x_6142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_6143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_package_x3f_6144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_6145_: u8 = 0;
    let mut v_imports_x3f_6146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_importArts_6147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_6148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_6149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_6150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: u8 = 0;
    let mut v___x_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: *mut LeanObject = core::ptr::null_mut();
    v_name_6143_ = lean_ctor_get(v_x_6142_, 0);
    lean_inc(v_name_6143_);
    v_package_x3f_6144_ = lean_ctor_get(v_x_6142_, 1);
    lean_inc(v_package_x3f_6144_);
    v_isModule_6145_ = lean_ctor_get_uint8(
        v_x_6142_,
        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
    );
    v_imports_x3f_6146_ = lean_ctor_get(v_x_6142_, 2);
    lean_inc(v_imports_x3f_6146_);
    v_importArts_6147_ = lean_ctor_get(v_x_6142_, 3);
    lean_inc(v_importArts_6147_);
    v_dynlibs_6148_ = lean_ctor_get(v_x_6142_, 4);
    lean_inc_ref(v_dynlibs_6148_);
    v_plugins_6149_ = lean_ctor_get(v_x_6142_, 5);
    lean_inc_ref(v_plugins_6149_);
    v_options_6150_ = lean_ctor_get(v_x_6142_, 6);
    lean_inc(v_options_6150_);
    lean_dec_ref(v_x_6142_);
    v___x_6151_ = l_Lean_instReprModuleSetup_repr___redArg___closed__0;
    v___x_6152_ = 1;
    v___x_6153_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_name_6143_,
        v___x_6152_,
    );
    v___x_6154_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_6154_, 0, v___x_6153_);
    v___x_6155_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6155_, 0, v___x_6151_);
    lean_ctor_set(v___x_6155_, 1, v___x_6154_);
    v___x_6156_ = lean_box(0);
    v___x_6157_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6157_, 0, v___x_6155_);
    lean_ctor_set(v___x_6157_, 1, v___x_6156_);
    v___x_6158_ = l_Lean_instToJsonModuleSetup_toJson___closed__0;
    v___x_6159_ = l_Lean_Json_opt___at___00Lean_instToJsonPlugin_toJson_spec__0(
        v___x_6158_,
        v_package_x3f_6144_,
    );
    v___x_6160_ = l_Lean_instReprModuleHeader_repr___redArg___closed__5;
    v___x_6161_ = lean_alloc_ctor(1, 0, (1) as u32);
    lean_ctor_set_uint8(v___x_6161_, 0 as u32, v_isModule_6145_);
    v___x_6162_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6162_, 0, v___x_6160_);
    lean_ctor_set(v___x_6162_, 1, v___x_6161_);
    v___x_6163_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6163_, 0, v___x_6162_);
    lean_ctor_set(v___x_6163_, 1, v___x_6156_);
    v___x_6164_ = l_Lean_instReprModuleHeader_repr___redArg___closed__0;
    v___x_6165_ = l_Lean_Json_opt___at___00Lean_instToJsonModuleSetup_toJson_spec__0(
        v___x_6164_,
        v_imports_x3f_6146_,
    );
    v___x_6166_ = l_Lean_instReprModuleSetup_repr___redArg___closed__8;
    v___x_6167_ = l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1(
        v_importArts_6147_,
    );
    v___x_6168_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6168_, 0, v___x_6166_);
    lean_ctor_set(v___x_6168_, 1, v___x_6167_);
    v___x_6169_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6169_, 0, v___x_6168_);
    lean_ctor_set(v___x_6169_, 1, v___x_6156_);
    v___x_6170_ = l_Lean_instReprModuleSetup_repr___redArg___closed__12;
    v___x_6171_ =
        l_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__2(v_dynlibs_6148_);
    v___x_6172_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6172_, 0, v___x_6170_);
    lean_ctor_set(v___x_6172_, 1, v___x_6171_);
    v___x_6173_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6173_, 0, v___x_6172_);
    lean_ctor_set(v___x_6173_, 1, v___x_6156_);
    v___x_6174_ = l_Lean_instReprModuleSetup_repr___redArg___closed__14;
    v___x_6175_ =
        l_Array_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__3(v_plugins_6149_);
    v___x_6176_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6176_, 0, v___x_6174_);
    lean_ctor_set(v___x_6176_, 1, v___x_6175_);
    v___x_6177_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6177_, 0, v___x_6176_);
    lean_ctor_set(v___x_6177_, 1, v___x_6156_);
    v___x_6178_ = l_Lean_instReprModuleSetup_repr___redArg___closed__16;
    v___x_6179_ =
        l_Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4(v_options_6150_);
    v___x_6180_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6180_, 0, v___x_6178_);
    lean_ctor_set(v___x_6180_, 1, v___x_6179_);
    v___x_6181_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6181_, 0, v___x_6180_);
    lean_ctor_set(v___x_6181_, 1, v___x_6156_);
    v___x_6182_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6182_, 0, v___x_6181_);
    lean_ctor_set(v___x_6182_, 1, v___x_6156_);
    v___x_6183_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6183_, 0, v___x_6177_);
    lean_ctor_set(v___x_6183_, 1, v___x_6182_);
    v___x_6184_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6184_, 0, v___x_6173_);
    lean_ctor_set(v___x_6184_, 1, v___x_6183_);
    v___x_6185_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6185_, 0, v___x_6169_);
    lean_ctor_set(v___x_6185_, 1, v___x_6184_);
    v___x_6186_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6186_, 0, v___x_6165_);
    lean_ctor_set(v___x_6186_, 1, v___x_6185_);
    v___x_6187_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6187_, 0, v___x_6163_);
    lean_ctor_set(v___x_6187_, 1, v___x_6186_);
    v___x_6188_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6188_, 0, v___x_6159_);
    lean_ctor_set(v___x_6188_, 1, v___x_6187_);
    v___x_6189_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6189_, 0, v___x_6157_);
    lean_ctor_set(v___x_6189_, 1, v___x_6188_);
    v___x_6190_ = l_Lean_instToJsonImport_toJson___closed__0;
    v___x_6191_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonImport_toJson_spec__0(v___x_6189_, v___x_6190_);
    v___x_6192_ = l_Lean_Json_mkObj(v___x_6191_);
    lean_dec(v___x_6191_);
    return v___x_6192_;
}
pub unsafe fn l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2(
    mut v_00_u03b2_6193_: *mut LeanObject,
    mut v_msg_6194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6195_: *mut LeanObject = core::ptr::null_mut();
    v___x_6195_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1_spec__2___redArg(v_msg_6194_);
    return v___x_6195_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1(
    mut v_00_u03b2_6196_: *mut LeanObject,
    mut v_k_6197_: *mut LeanObject,
    mut v_v_6198_: *mut LeanObject,
    mut v_t_6199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6200_: *mut LeanObject = core::ptr::null_mut();
    v___x_6200_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__1___redArg(v_k_6197_, v_v_6198_, v_t_6199_);
    return v___x_6200_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2(
    mut v_init_6201_: *mut LeanObject,
    mut v_t_6202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6203_: *mut LeanObject = core::ptr::null_mut();
    v___x_6203_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__1_spec__2_spec__4(v_init_6201_, v_t_6202_);
    return v___x_6203_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__8(
    mut v_init_6204_: *mut LeanObject,
    mut v_t_6205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6206_: *mut LeanObject = core::ptr::null_mut();
    v___x_6206_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lean_instToJsonModuleSetup_toJson_spec__4_spec__8_spec__11(v_init_6204_, v_t_6205_);
    return v___x_6206_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__3()
-> *mut LeanObject {
    let mut v_natZero_6213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_6214_: *mut LeanObject = core::ptr::null_mut();
    v_natZero_6213_ = lean_unsigned_to_nat(0);
    v_intZero_6214_ = lean_nat_to_int(v_natZero_6213_);
    return v_intZero_6214_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12(
    mut v_init_6216_: *mut LeanObject,
    mut v_x_6217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6230_: u8 = 0;
    let mut v_a_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: u8 = 0;
    let mut v_n_6238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6243_: u8 = 0;
    let mut v_s_6244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6247_: u8 = 0;
    let mut v___x_6249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6251_: u8 = 0;
    let mut v_b_6252_: u8 = 0;
    let mut v___x_6254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6255_: u8 = 0;
    let mut v___x_6257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6259_: u8 = 0;
    let mut v_n_6260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6263_: u8 = 0;
    let mut v_mantissa_6264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exponent_6265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natZero_6266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_6267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_6268_: u8 = 0;
    let mut v___x_6269_: u8 = 0;
    let mut v_a_6270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6274_: u8 = 0;
    let mut v___x_6275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_6282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6285_: u8 = 0;
    let mut v___x_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6289_: u8 = 0;
    let mut v_b_6290_: u8 = 0;
    let mut v___x_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6293_: u8 = 0;
    let mut v___x_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6297_: u8 = 0;
    let mut v_n_6298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6301_: u8 = 0;
    let mut v_mantissa_6302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exponent_6303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natZero_6304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_6305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_6306_: u8 = 0;
    let mut v___x_6307_: u8 = 0;
    let mut v_a_6308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6312_: u8 = 0;
    let mut v_isSharedCheck_6313_: u8 = 0;
    let mut v___x_6314_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6217_) == 0 {
                    v_k_6222_ = lean_ctor_get(v_x_6217_, 1);
                    lean_inc(v_k_6222_);
                    v_v_6223_ = lean_ctor_get(v_x_6217_, 2);
                    lean_inc(v_v_6223_);
                    v_l_6224_ = lean_ctor_get(v_x_6217_, 3);
                    lean_inc(v_l_6224_);
                    v_r_6225_ = lean_ctor_get(v_x_6217_, 4);
                    lean_inc(v_r_6225_);
                    lean_dec_ref_known(v_x_6217_, 5);
                    v___x_6226_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12(v_init_6216_, v_l_6224_);
                    if lean_obj_tag(v___x_6226_) == 0 {
                        lean_dec(v_r_6225_);
                        lean_dec(v_v_6223_);
                        lean_dec(v_k_6222_);
                        return v___x_6226_;
                    } else {
                        v_a_6227_ = lean_ctor_get(v___x_6226_, 0);
                        v_isSharedCheck_6313_ = (!lean_is_exclusive(v___x_6226_)) as u8;
                        if v_isSharedCheck_6313_ == 0 {
                            v___x_6229_ = v___x_6226_;
                            v_isShared_6230_ = v_isSharedCheck_6313_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6227_);
                            lean_dec(v___x_6226_);
                            v___x_6229_ = lean_box(0);
                            v_isShared_6230_ = v_isSharedCheck_6313_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v___x_6314_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6314_, 0, v_init_6216_);
                    return v___x_6314_;
                }
            }
            1 => {
                v___x_6219_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__1;
                return v___x_6219_;
            }
            2 => {
                v___x_6221_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__1;
                return v___x_6221_;
            }
            3 => {
                v___x_6236_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__2;
                v___x_6237_ = lean_string_dec_eq(v_k_6222_, v___x_6236_);
                if v___x_6237_ == 0 {
                    lean_inc(v_k_6222_);
                    v_n_6238_ = l_String_toName(v_k_6222_);
                    v___x_6243_ = l_Lean_Name_isAnonymous(v_n_6238_);
                    if v___x_6243_ == 0 {
                        lean_del_object(v___x_6229_);
                        lean_dec(v_k_6222_);
                        match lean_obj_tag(v_v_6223_) {
                            3 => {
                                v_s_6244_ = lean_ctor_get(v_v_6223_, 0);
                                v_isSharedCheck_6251_ = (!lean_is_exclusive(v_v_6223_)) as u8;
                                if v_isSharedCheck_6251_ == 0 {
                                    v___x_6246_ = v_v_6223_;
                                    v_isShared_6247_ = v_isSharedCheck_6251_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_s_6244_);
                                    lean_dec(v_v_6223_);
                                    v___x_6246_ = lean_box(0);
                                    v_isShared_6247_ = v_isSharedCheck_6251_;
                                    state = 6;
                                    continue;
                                }
                            }
                            1 => {
                                v_b_6252_ = lean_ctor_get_uint8(v_v_6223_, 0 as u32);
                                v_isSharedCheck_6259_ = (!lean_is_exclusive(v_v_6223_)) as u8;
                                if v_isSharedCheck_6259_ == 0 {
                                    v___x_6254_ = v_v_6223_;
                                    v_isShared_6255_ = v_isSharedCheck_6259_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_dec(v_v_6223_);
                                    v___x_6254_ = lean_box(0);
                                    v_isShared_6255_ = v_isSharedCheck_6259_;
                                    state = 8;
                                    continue;
                                }
                            }
                            2 => {
                                v_n_6260_ = lean_ctor_get(v_v_6223_, 0);
                                v_isSharedCheck_6274_ = (!lean_is_exclusive(v_v_6223_)) as u8;
                                if v_isSharedCheck_6274_ == 0 {
                                    v___x_6262_ = v_v_6223_;
                                    v_isShared_6263_ = v_isSharedCheck_6274_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_inc(v_n_6260_);
                                    lean_dec(v_v_6223_);
                                    v___x_6262_ = lean_box(0);
                                    v_isShared_6263_ = v_isSharedCheck_6274_;
                                    state = 10;
                                    continue;
                                }
                            }
                            _ => {
                                lean_dec(v_n_6238_);
                                lean_dec(v_a_6227_);
                                lean_dec(v_r_6225_);
                                lean_dec(v_v_6223_);
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_n_6238_);
                        lean_dec(v_a_6227_);
                        lean_dec(v_r_6225_);
                        lean_dec(v_v_6223_);
                        v___x_6275_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__4;
                        v___x_6276_ = lean_string_append(v___x_6275_, v_k_6222_);
                        lean_dec(v_k_6222_);
                        v___x_6277_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1;
                        v___x_6278_ = lean_string_append(v___x_6276_, v___x_6277_);
                        if v_isShared_6230_ == 0 {
                            lean_ctor_set_tag(v___x_6229_, 0);
                            lean_ctor_set(v___x_6229_, 0, v___x_6278_);
                            v___x_6280_ = v___x_6229_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_6281_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6281_, 0, v___x_6278_);
                            v___x_6280_ = v_reuseFailAlloc_6281_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_6229_);
                    lean_dec(v_k_6222_);
                    match lean_obj_tag(v_v_6223_) {
                        3 => {
                            v_s_6282_ = lean_ctor_get(v_v_6223_, 0);
                            v_isSharedCheck_6289_ = (!lean_is_exclusive(v_v_6223_)) as u8;
                            if v_isSharedCheck_6289_ == 0 {
                                v___x_6284_ = v_v_6223_;
                                v_isShared_6285_ = v_isSharedCheck_6289_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_s_6282_);
                                lean_dec(v_v_6223_);
                                v___x_6284_ = lean_box(0);
                                v_isShared_6285_ = v_isSharedCheck_6289_;
                                state = 13;
                                continue;
                            }
                        }
                        1 => {
                            v_b_6290_ = lean_ctor_get_uint8(v_v_6223_, 0 as u32);
                            v_isSharedCheck_6297_ = (!lean_is_exclusive(v_v_6223_)) as u8;
                            if v_isSharedCheck_6297_ == 0 {
                                v___x_6292_ = v_v_6223_;
                                v_isShared_6293_ = v_isSharedCheck_6297_;
                                state = 15;
                                continue;
                            } else {
                                lean_dec(v_v_6223_);
                                v___x_6292_ = lean_box(0);
                                v_isShared_6293_ = v_isSharedCheck_6297_;
                                state = 15;
                                continue;
                            }
                        }
                        2 => {
                            v_n_6298_ = lean_ctor_get(v_v_6223_, 0);
                            v_isSharedCheck_6312_ = (!lean_is_exclusive(v_v_6223_)) as u8;
                            if v_isSharedCheck_6312_ == 0 {
                                v___x_6300_ = v_v_6223_;
                                v_isShared_6301_ = v_isSharedCheck_6312_;
                                state = 17;
                                continue;
                            } else {
                                lean_inc(v_n_6298_);
                                lean_dec(v_v_6223_);
                                v___x_6300_ = lean_box(0);
                                v_isShared_6301_ = v_isSharedCheck_6312_;
                                state = 17;
                                continue;
                            }
                        }
                        _ => {
                            lean_dec(v_a_6227_);
                            lean_dec(v_r_6225_);
                            lean_dec(v_v_6223_);
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v___x_6233_ = lean_box(0);
                v___x_6234_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_6233_, v_a_6232_, v_a_6227_);
                v_init_6216_ = v___x_6234_;
                v_x_6217_ = v_r_6225_;
                state = 0;
                continue;
            }
            5 => {
                v___x_6241_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_6238_, v_a_6240_, v_a_6227_);
                v_init_6216_ = v___x_6241_;
                v_x_6217_ = v_r_6225_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_6247_ == 0 {
                    lean_ctor_set_tag(v___x_6246_, 0);
                    v___x_6249_ = v___x_6246_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6250_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6250_, 0, v_s_6244_);
                    v___x_6249_ = v_reuseFailAlloc_6250_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_a_6240_ = v___x_6249_;
                state = 5;
                continue;
            }
            8 => {
                if v_isShared_6255_ == 0 {
                    v___x_6257_ = v___x_6254_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6258_ = lean_alloc_ctor(1, 0, (1) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6258_, 0 as u32, v_b_6252_);
                    v___x_6257_ = v_reuseFailAlloc_6258_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_a_6240_ = v___x_6257_;
                state = 5;
                continue;
            }
            10 => {
                v_mantissa_6264_ = lean_ctor_get(v_n_6260_, 0);
                lean_inc(v_mantissa_6264_);
                v_exponent_6265_ = lean_ctor_get(v_n_6260_, 1);
                lean_inc(v_exponent_6265_);
                lean_dec_ref(v_n_6260_);
                v_natZero_6266_ = lean_unsigned_to_nat(0);
                v_intZero_6267_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__3), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__3_once), _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__3);
                v_isNeg_6268_ = lean_int_dec_lt(v_mantissa_6264_, v_intZero_6267_);
                if v_isNeg_6268_ == 0 {
                    v___x_6269_ = lean_nat_dec_eq(v_exponent_6265_, v_natZero_6266_);
                    lean_dec(v_exponent_6265_);
                    if v___x_6269_ == 0 {
                        lean_dec(v_mantissa_6264_);
                        lean_del_object(v___x_6262_);
                        lean_dec(v_n_6238_);
                        lean_dec(v_a_6227_);
                        lean_dec(v_r_6225_);
                        state = 2;
                        continue;
                    } else {
                        v_a_6270_ = lean_nat_abs(v_mantissa_6264_);
                        lean_dec(v_mantissa_6264_);
                        if v_isShared_6263_ == 0 {
                            lean_ctor_set(v___x_6262_, 0, v_a_6270_);
                            v___x_6272_ = v___x_6262_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_6273_ = lean_alloc_ctor(2, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6273_, 0, v_a_6270_);
                            v___x_6272_ = v_reuseFailAlloc_6273_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_exponent_6265_);
                    lean_dec(v_mantissa_6264_);
                    lean_del_object(v___x_6262_);
                    lean_dec(v_n_6238_);
                    lean_dec(v_a_6227_);
                    lean_dec(v_r_6225_);
                    state = 2;
                    continue;
                }
            }
            11 => {
                v_a_6240_ = v___x_6272_;
                state = 5;
                continue;
            }
            12 => {
                return v___x_6280_;
            }
            13 => {
                if v_isShared_6285_ == 0 {
                    lean_ctor_set_tag(v___x_6284_, 0);
                    v___x_6287_ = v___x_6284_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6288_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6288_, 0, v_s_6282_);
                    v___x_6287_ = v_reuseFailAlloc_6288_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v_a_6232_ = v___x_6287_;
                state = 4;
                continue;
            }
            15 => {
                if v_isShared_6293_ == 0 {
                    v___x_6295_ = v___x_6292_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6296_ = lean_alloc_ctor(1, 0, (1) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6296_, 0 as u32, v_b_6290_);
                    v___x_6295_ = v_reuseFailAlloc_6296_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v_a_6232_ = v___x_6295_;
                state = 4;
                continue;
            }
            17 => {
                v_mantissa_6302_ = lean_ctor_get(v_n_6298_, 0);
                lean_inc(v_mantissa_6302_);
                v_exponent_6303_ = lean_ctor_get(v_n_6298_, 1);
                lean_inc(v_exponent_6303_);
                lean_dec_ref(v_n_6298_);
                v_natZero_6304_ = lean_unsigned_to_nat(0);
                v_intZero_6305_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__3), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__3_once), _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__3);
                v_isNeg_6306_ = lean_int_dec_lt(v_mantissa_6302_, v_intZero_6305_);
                if v_isNeg_6306_ == 0 {
                    v___x_6307_ = lean_nat_dec_eq(v_exponent_6303_, v_natZero_6304_);
                    lean_dec(v_exponent_6303_);
                    if v___x_6307_ == 0 {
                        lean_dec(v_mantissa_6302_);
                        lean_del_object(v___x_6300_);
                        lean_dec(v_a_6227_);
                        lean_dec(v_r_6225_);
                        state = 1;
                        continue;
                    } else {
                        v_a_6308_ = lean_nat_abs(v_mantissa_6302_);
                        lean_dec(v_mantissa_6302_);
                        if v_isShared_6301_ == 0 {
                            lean_ctor_set(v___x_6300_, 0, v_a_6308_);
                            v___x_6310_ = v___x_6300_;
                            state = 18;
                            continue;
                        } else {
                            v_reuseFailAlloc_6311_ = lean_alloc_ctor(2, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6311_, 0, v_a_6308_);
                            v___x_6310_ = v_reuseFailAlloc_6311_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_exponent_6303_);
                    lean_dec(v_mantissa_6302_);
                    lean_del_object(v___x_6300_);
                    lean_dec(v_a_6227_);
                    lean_dec(v_r_6225_);
                    state = 1;
                    continue;
                }
            }
            18 => {
                v_a_6232_ = v___x_6310_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8(
    mut v_x_6316_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6316_) == 5 {
        let mut v_kvPairs_6317_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6318_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6319_: *mut LeanObject = core::ptr::null_mut();
        v_kvPairs_6317_ = lean_ctor_get(v_x_6316_, 0);
        lean_inc(v_kvPairs_6317_);
        lean_dec_ref_known(v_x_6316_, 1);
        v___x_6318_ = lean_box(1);
        v___x_6319_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12(v___x_6318_, v_kvPairs_6317_);
        return v___x_6319_;
    } else {
        let mut v___x_6320_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6321_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6322_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6323_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6324_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6325_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6326_: *mut LeanObject = core::ptr::null_mut();
        v___x_6320_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8___closed__0;
        v___x_6321_ = lean_unsigned_to_nat(80);
        v___x_6322_ = l_Lean_Json_pretty(v_x_6316_, v___x_6321_);
        v___x_6323_ = lean_string_append(v___x_6320_, v___x_6322_);
        lean_dec_ref(v___x_6322_);
        v___x_6324_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1;
        v___x_6325_ = lean_string_append(v___x_6323_, v___x_6324_);
        v___x_6326_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_6326_, 0, v___x_6325_);
        return v___x_6326_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4(
    mut v_j_6327_: *mut LeanObject,
    mut v_k_6328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6334_: u8 = 0;
    let mut v___x_6336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6338_: u8 = 0;
    let mut v_a_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6342_: u8 = 0;
    let mut v___x_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6346_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6329_ = l_Lean_Json_getObjValD(v_j_6327_, v_k_6328_);
                v___x_6330_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8(v___x_6329_);
                if lean_obj_tag(v___x_6330_) == 0 {
                    v_a_6331_ = lean_ctor_get(v___x_6330_, 0);
                    v_isSharedCheck_6338_ = (!lean_is_exclusive(v___x_6330_)) as u8;
                    if v_isSharedCheck_6338_ == 0 {
                        v___x_6333_ = v___x_6330_;
                        v_isShared_6334_ = v_isSharedCheck_6338_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6331_);
                        lean_dec(v___x_6330_);
                        v___x_6333_ = lean_box(0);
                        v_isShared_6334_ = v_isSharedCheck_6338_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6339_ = lean_ctor_get(v___x_6330_, 0);
                    v_isSharedCheck_6346_ = (!lean_is_exclusive(v___x_6330_)) as u8;
                    if v_isSharedCheck_6346_ == 0 {
                        v___x_6341_ = v___x_6330_;
                        v_isShared_6342_ = v_isSharedCheck_6346_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6339_);
                        lean_dec(v___x_6330_);
                        v___x_6341_ = lean_box(0);
                        v_isShared_6342_ = v_isSharedCheck_6346_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6334_ == 0 {
                    v___x_6336_ = v___x_6333_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6337_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6337_, 0, v_a_6331_);
                    v___x_6336_ = v_reuseFailAlloc_6337_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6336_;
            }
            3 => {
                if v_isShared_6342_ == 0 {
                    v___x_6344_ = v___x_6341_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6345_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6345_, 0, v_a_6339_);
                    v___x_6344_ = v_reuseFailAlloc_6345_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6344_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4___boxed(
    mut v_j_6347_: *mut LeanObject,
    mut v_k_6348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6349_: *mut LeanObject = core::ptr::null_mut();
    v_res_6349_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4(
            v_j_6347_, v_k_6348_,
        );
    lean_dec_ref(v_k_6348_);
    return v_res_6349_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__9(
    mut v_sz_6350_: usize,
    mut v_i_6351_: usize,
    mut v_bs_6352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6353_: u8 = 0;
    let mut v___x_6354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6360_: u8 = 0;
    let mut v___x_6362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6364_: u8 = 0;
    let mut v_a_6365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: usize = 0;
    let mut v___x_6369_: usize = 0;
    let mut v___x_6370_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6353_ = lean_usize_dec_lt(v_i_6351_, v_sz_6350_);
                if v___x_6353_ == 0 {
                    v___x_6354_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6354_, 0, v_bs_6352_);
                    return v___x_6354_;
                } else {
                    v_v_6355_ = lean_array_uget_borrowed(v_bs_6352_, v_i_6351_);
                    lean_inc(v_v_6355_);
                    v___x_6356_ = l_Lean_Plugin_fromJson_x3f(v_v_6355_);
                    if lean_obj_tag(v___x_6356_) == 0 {
                        lean_dec_ref(v_bs_6352_);
                        v_a_6357_ = lean_ctor_get(v___x_6356_, 0);
                        v_isSharedCheck_6364_ = (!lean_is_exclusive(v___x_6356_)) as u8;
                        if v_isSharedCheck_6364_ == 0 {
                            v___x_6359_ = v___x_6356_;
                            v_isShared_6360_ = v_isSharedCheck_6364_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6357_);
                            lean_dec(v___x_6356_);
                            v___x_6359_ = lean_box(0);
                            v_isShared_6360_ = v_isSharedCheck_6364_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6365_ = lean_ctor_get(v___x_6356_, 0);
                        lean_inc(v_a_6365_);
                        lean_dec_ref_known(v___x_6356_, 1);
                        v___x_6366_ = lean_unsigned_to_nat(0);
                        v_bs_x27_6367_ = lean_array_uset(v_bs_6352_, v_i_6351_, v___x_6366_);
                        v___x_6368_ = 1usize;
                        v___x_6369_ = lean_usize_add(v_i_6351_, v___x_6368_);
                        v___x_6370_ = lean_array_uset(v_bs_x27_6367_, v_i_6351_, v_a_6365_);
                        v_i_6351_ = v___x_6369_;
                        v_bs_6352_ = v___x_6370_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6360_ == 0 {
                    v___x_6362_ = v___x_6359_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6363_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6363_, 0, v_a_6357_);
                    v___x_6362_ = v_reuseFailAlloc_6363_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6362_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__9___boxed(
    mut v_sz_6372_: *mut LeanObject,
    mut v_i_6373_: *mut LeanObject,
    mut v_bs_6374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6375_: usize = 0;
    let mut v_i_boxed_6376_: usize = 0;
    let mut v_res_6377_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6375_ = lean_unbox_usize(v_sz_6372_);
    lean_dec(v_sz_6372_);
    v_i_boxed_6376_ = lean_unbox_usize(v_i_6373_);
    lean_dec(v_i_6373_);
    v_res_6377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__9(v_sz_boxed_6375_, v_i_boxed_6376_, v_bs_6374_);
    return v_res_6377_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6(
    mut v_x_6378_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6378_) == 4 {
        let mut v_elems_6379_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_6380_: usize = 0;
        let mut v___x_6381_: usize = 0;
        let mut v___x_6382_: *mut LeanObject = core::ptr::null_mut();
        v_elems_6379_ = lean_ctor_get(v_x_6378_, 0);
        lean_inc_ref(v_elems_6379_);
        lean_dec_ref_known(v_x_6378_, 1);
        v_sz_6380_ = lean_array_size(v_elems_6379_);
        v___x_6381_ = 0usize;
        v___x_6382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6_spec__9(v_sz_6380_, v___x_6381_, v_elems_6379_);
        return v___x_6382_;
    } else {
        let mut v___x_6383_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6384_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6385_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6386_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6387_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6388_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6389_: *mut LeanObject = core::ptr::null_mut();
        v___x_6383_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0;
        v___x_6384_ = lean_unsigned_to_nat(80);
        v___x_6385_ = l_Lean_Json_pretty(v_x_6378_, v___x_6384_);
        v___x_6386_ = lean_string_append(v___x_6383_, v___x_6385_);
        lean_dec_ref(v___x_6385_);
        v___x_6387_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1;
        v___x_6388_ = lean_string_append(v___x_6386_, v___x_6387_);
        v___x_6389_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_6389_, 0, v___x_6388_);
        return v___x_6389_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3(
    mut v_j_6390_: *mut LeanObject,
    mut v_k_6391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6393_: *mut LeanObject = core::ptr::null_mut();
    v___x_6392_ = l_Lean_Json_getObjValD(v_j_6390_, v_k_6391_);
    v___x_6393_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3_spec__6(v___x_6392_);
    return v___x_6393_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3___boxed(
    mut v_j_6394_: *mut LeanObject,
    mut v_k_6395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6396_: *mut LeanObject = core::ptr::null_mut();
    v_res_6396_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3(
            v_j_6394_, v_k_6395_,
        );
    lean_dec_ref(v_k_6395_);
    return v_res_6396_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0(
    mut v_x_6399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6405_: u8 = 0;
    let mut v___x_6407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6409_: u8 = 0;
    let mut v_a_6410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6413_: u8 = 0;
    let mut v___x_6414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6418_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6399_) == 0 {
                    v___x_6400_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0___closed__0;
                    return v___x_6400_;
                } else {
                    v___x_6401_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0(v_x_6399_);
                    if lean_obj_tag(v___x_6401_) == 0 {
                        v_a_6402_ = lean_ctor_get(v___x_6401_, 0);
                        v_isSharedCheck_6409_ = (!lean_is_exclusive(v___x_6401_)) as u8;
                        if v_isSharedCheck_6409_ == 0 {
                            v___x_6404_ = v___x_6401_;
                            v_isShared_6405_ = v_isSharedCheck_6409_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6402_);
                            lean_dec(v___x_6401_);
                            v___x_6404_ = lean_box(0);
                            v_isShared_6405_ = v_isSharedCheck_6409_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6410_ = lean_ctor_get(v___x_6401_, 0);
                        v_isSharedCheck_6418_ = (!lean_is_exclusive(v___x_6401_)) as u8;
                        if v_isSharedCheck_6418_ == 0 {
                            v___x_6412_ = v___x_6401_;
                            v_isShared_6413_ = v_isSharedCheck_6418_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6410_);
                            lean_dec(v___x_6401_);
                            v___x_6412_ = lean_box(0);
                            v_isShared_6413_ = v_isSharedCheck_6418_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6405_ == 0 {
                    v___x_6407_ = v___x_6404_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6408_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6408_, 0, v_a_6402_);
                    v___x_6407_ = v_reuseFailAlloc_6408_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6407_;
            }
            3 => {
                v___x_6414_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6414_, 0, v_a_6410_);
                if v_isShared_6413_ == 0 {
                    lean_ctor_set(v___x_6412_, 0, v___x_6414_);
                    v___x_6416_ = v___x_6412_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6417_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6417_, 0, v___x_6414_);
                    v___x_6416_ = v_reuseFailAlloc_6417_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6416_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0(
    mut v_j_6419_: *mut LeanObject,
    mut v_k_6420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut LeanObject = core::ptr::null_mut();
    v___x_6421_ = l_Lean_Json_getObjValD(v_j_6419_, v_k_6420_);
    v___x_6422_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0_spec__0(v___x_6421_);
    return v___x_6422_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0___boxed(
    mut v_j_6423_: *mut LeanObject,
    mut v_k_6424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6425_: *mut LeanObject = core::ptr::null_mut();
    v_res_6425_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0(
            v_j_6423_, v_k_6424_,
        );
    lean_dec_ref(v_k_6424_);
    return v_res_6425_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__6(
    mut v_sz_6426_: usize,
    mut v_i_6427_: usize,
    mut v_bs_6428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6429_: u8 = 0;
    let mut v___x_6430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6436_: u8 = 0;
    let mut v___x_6438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6440_: u8 = 0;
    let mut v_a_6441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6444_: usize = 0;
    let mut v___x_6445_: usize = 0;
    let mut v___x_6446_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6429_ = lean_usize_dec_lt(v_i_6427_, v_sz_6426_);
                if v___x_6429_ == 0 {
                    v___x_6430_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6430_, 0, v_bs_6428_);
                    return v___x_6430_;
                } else {
                    v_v_6431_ = lean_array_uget_borrowed(v_bs_6428_, v_i_6427_);
                    lean_inc(v_v_6431_);
                    v___x_6432_ = l_Lean_Json_getStr_x3f(v_v_6431_);
                    if lean_obj_tag(v___x_6432_) == 0 {
                        lean_dec_ref(v_bs_6428_);
                        v_a_6433_ = lean_ctor_get(v___x_6432_, 0);
                        v_isSharedCheck_6440_ = (!lean_is_exclusive(v___x_6432_)) as u8;
                        if v_isSharedCheck_6440_ == 0 {
                            v___x_6435_ = v___x_6432_;
                            v_isShared_6436_ = v_isSharedCheck_6440_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6433_);
                            lean_dec(v___x_6432_);
                            v___x_6435_ = lean_box(0);
                            v_isShared_6436_ = v_isSharedCheck_6440_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6441_ = lean_ctor_get(v___x_6432_, 0);
                        lean_inc(v_a_6441_);
                        lean_dec_ref_known(v___x_6432_, 1);
                        v___x_6442_ = lean_unsigned_to_nat(0);
                        v_bs_x27_6443_ = lean_array_uset(v_bs_6428_, v_i_6427_, v___x_6442_);
                        v___x_6444_ = 1usize;
                        v___x_6445_ = lean_usize_add(v_i_6427_, v___x_6444_);
                        v___x_6446_ = lean_array_uset(v_bs_x27_6443_, v_i_6427_, v_a_6441_);
                        v_i_6427_ = v___x_6445_;
                        v_bs_6428_ = v___x_6446_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6436_ == 0 {
                    v___x_6438_ = v___x_6435_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6439_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6439_, 0, v_a_6433_);
                    v___x_6438_ = v_reuseFailAlloc_6439_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6438_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__6___boxed(
    mut v_sz_6448_: *mut LeanObject,
    mut v_i_6449_: *mut LeanObject,
    mut v_bs_6450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6451_: usize = 0;
    let mut v_i_boxed_6452_: usize = 0;
    let mut v_res_6453_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6451_ = lean_unbox_usize(v_sz_6448_);
    lean_dec(v_sz_6448_);
    v_i_boxed_6452_ = lean_unbox_usize(v_i_6449_);
    lean_dec(v_i_6449_);
    v_res_6453_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__6(v_sz_boxed_6451_, v_i_boxed_6452_, v_bs_6450_);
    return v_res_6453_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4(
    mut v_x_6454_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6454_) == 4 {
        let mut v_elems_6455_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_6456_: usize = 0;
        let mut v___x_6457_: usize = 0;
        let mut v___x_6458_: *mut LeanObject = core::ptr::null_mut();
        v_elems_6455_ = lean_ctor_get(v_x_6454_, 0);
        lean_inc_ref(v_elems_6455_);
        lean_dec_ref_known(v_x_6454_, 1);
        v_sz_6456_ = lean_array_size(v_elems_6455_);
        v___x_6457_ = 0usize;
        v___x_6458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4_spec__6(v_sz_6456_, v___x_6457_, v_elems_6455_);
        return v___x_6458_;
    } else {
        let mut v___x_6459_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6460_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6461_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6462_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6463_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6464_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6465_: *mut LeanObject = core::ptr::null_mut();
        v___x_6459_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__0;
        v___x_6460_ = lean_unsigned_to_nat(80);
        v___x_6461_ = l_Lean_Json_pretty(v_x_6454_, v___x_6460_);
        v___x_6462_ = lean_string_append(v___x_6459_, v___x_6461_);
        lean_dec_ref(v___x_6461_);
        v___x_6463_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1;
        v___x_6464_ = lean_string_append(v___x_6462_, v___x_6463_);
        v___x_6465_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_6465_, 0, v___x_6464_);
        return v___x_6465_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3(
    mut v_init_6466_: *mut LeanObject,
    mut v_x_6467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_6468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6476_: u8 = 0;
    let mut v___x_6477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6478_: u8 = 0;
    let mut v_n_6479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6480_: u8 = 0;
    let mut v___x_6481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6485_: u8 = 0;
    let mut v___x_6487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6489_: u8 = 0;
    let mut v_a_6490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6504_: u8 = 0;
    let mut v___x_6506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6508_: u8 = 0;
    let mut v_a_6509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6513_: u8 = 0;
    let mut v___x_6514_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6467_) == 0 {
                    v_k_6468_ = lean_ctor_get(v_x_6467_, 1);
                    lean_inc(v_k_6468_);
                    v_v_6469_ = lean_ctor_get(v_x_6467_, 2);
                    lean_inc(v_v_6469_);
                    v_l_6470_ = lean_ctor_get(v_x_6467_, 3);
                    lean_inc(v_l_6470_);
                    v_r_6471_ = lean_ctor_get(v_x_6467_, 4);
                    lean_inc(v_r_6471_);
                    lean_dec_ref_known(v_x_6467_, 5);
                    v___x_6472_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3(v_init_6466_, v_l_6470_);
                    if lean_obj_tag(v___x_6472_) == 0 {
                        lean_dec(v_r_6471_);
                        lean_dec(v_v_6469_);
                        lean_dec(v_k_6468_);
                        return v___x_6472_;
                    } else {
                        v_a_6473_ = lean_ctor_get(v___x_6472_, 0);
                        v_isSharedCheck_6513_ = (!lean_is_exclusive(v___x_6472_)) as u8;
                        if v_isSharedCheck_6513_ == 0 {
                            v___x_6475_ = v___x_6472_;
                            v_isShared_6476_ = v_isSharedCheck_6513_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6473_);
                            lean_dec(v___x_6472_);
                            v___x_6475_ = lean_box(0);
                            v_isShared_6476_ = v_isSharedCheck_6513_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_6514_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6514_, 0, v_init_6466_);
                    return v___x_6514_;
                }
            }
            1 => {
                v___x_6477_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__2;
                v___x_6478_ = lean_string_dec_eq(v_k_6468_, v___x_6477_);
                if v___x_6478_ == 0 {
                    lean_inc(v_k_6468_);
                    v_n_6479_ = l_String_toName(v_k_6468_);
                    v___x_6480_ = l_Lean_Name_isAnonymous(v_n_6479_);
                    if v___x_6480_ == 0 {
                        lean_del_object(v___x_6475_);
                        lean_dec(v_k_6468_);
                        v___x_6481_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4(v_v_6469_);
                        if lean_obj_tag(v___x_6481_) == 0 {
                            lean_dec(v_n_6479_);
                            lean_dec(v_a_6473_);
                            lean_dec(v_r_6471_);
                            v_a_6482_ = lean_ctor_get(v___x_6481_, 0);
                            v_isSharedCheck_6489_ = (!lean_is_exclusive(v___x_6481_)) as u8;
                            if v_isSharedCheck_6489_ == 0 {
                                v___x_6484_ = v___x_6481_;
                                v_isShared_6485_ = v_isSharedCheck_6489_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_6482_);
                                lean_dec(v___x_6481_);
                                v___x_6484_ = lean_box(0);
                                v_isShared_6485_ = v_isSharedCheck_6489_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_a_6490_ = lean_ctor_get(v___x_6481_, 0);
                            lean_inc(v_a_6490_);
                            lean_dec_ref_known(v___x_6481_, 1);
                            v___x_6491_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_6479_, v_a_6490_, v_a_6473_);
                            v_init_6466_ = v___x_6491_;
                            v_x_6467_ = v_r_6471_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec(v_n_6479_);
                        lean_dec(v_a_6473_);
                        lean_dec(v_r_6471_);
                        lean_dec(v_v_6469_);
                        v___x_6493_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8_spec__12___closed__4;
                        v___x_6494_ = lean_string_append(v___x_6493_, v_k_6468_);
                        lean_dec(v_k_6468_);
                        v___x_6495_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1;
                        v___x_6496_ = lean_string_append(v___x_6494_, v___x_6495_);
                        if v_isShared_6476_ == 0 {
                            lean_ctor_set_tag(v___x_6475_, 0);
                            lean_ctor_set(v___x_6475_, 0, v___x_6496_);
                            v___x_6498_ = v___x_6475_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_6499_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6499_, 0, v___x_6496_);
                            v___x_6498_ = v_reuseFailAlloc_6499_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_6475_);
                    lean_dec(v_k_6468_);
                    v___x_6500_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4(v_v_6469_);
                    if lean_obj_tag(v___x_6500_) == 0 {
                        lean_dec(v_a_6473_);
                        lean_dec(v_r_6471_);
                        v_a_6501_ = lean_ctor_get(v___x_6500_, 0);
                        v_isSharedCheck_6508_ = (!lean_is_exclusive(v___x_6500_)) as u8;
                        if v_isSharedCheck_6508_ == 0 {
                            v___x_6503_ = v___x_6500_;
                            v_isShared_6504_ = v_isSharedCheck_6508_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_6501_);
                            lean_dec(v___x_6500_);
                            v___x_6503_ = lean_box(0);
                            v_isShared_6504_ = v_isSharedCheck_6508_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_6509_ = lean_ctor_get(v___x_6500_, 0);
                        lean_inc(v_a_6509_);
                        lean_dec_ref_known(v___x_6500_, 1);
                        v___x_6510_ = lean_box(0);
                        v___x_6511_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_6510_, v_a_6509_, v_a_6473_);
                        v_init_6466_ = v___x_6511_;
                        v_x_6467_ = v_r_6471_;
                        state = 0;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6485_ == 0 {
                    v___x_6487_ = v___x_6484_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6488_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6488_, 0, v_a_6482_);
                    v___x_6487_ = v_reuseFailAlloc_6488_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6487_;
            }
            4 => {
                return v___x_6498_;
            }
            5 => {
                if v_isShared_6504_ == 0 {
                    v___x_6506_ = v___x_6503_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6507_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6507_, 0, v_a_6501_);
                    v___x_6506_ = v_reuseFailAlloc_6507_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6506_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2(
    mut v_x_6515_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6515_) == 5 {
        let mut v_kvPairs_6516_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6517_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6518_: *mut LeanObject = core::ptr::null_mut();
        v_kvPairs_6516_ = lean_ctor_get(v_x_6515_, 0);
        lean_inc(v_kvPairs_6516_);
        lean_dec_ref_known(v_x_6515_, 1);
        v___x_6517_ = lean_box(1);
        v___x_6518_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2_spec__3(v___x_6517_, v_kvPairs_6516_);
        return v___x_6518_;
    } else {
        let mut v___x_6519_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6520_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6521_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6522_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6523_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6524_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6525_: *mut LeanObject = core::ptr::null_mut();
        v___x_6519_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4_spec__8___closed__0;
        v___x_6520_ = lean_unsigned_to_nat(80);
        v___x_6521_ = l_Lean_Json_pretty(v_x_6515_, v___x_6520_);
        v___x_6522_ = lean_string_append(v___x_6519_, v___x_6521_);
        lean_dec_ref(v___x_6521_);
        v___x_6523_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleHeader_fromJson_spec__0_spec__0___closed__1;
        v___x_6524_ = lean_string_append(v___x_6522_, v___x_6523_);
        v___x_6525_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_6525_, 0, v___x_6524_);
        return v___x_6525_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1(
    mut v_j_6526_: *mut LeanObject,
    mut v_k_6527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: *mut LeanObject = core::ptr::null_mut();
    v___x_6528_ = l_Lean_Json_getObjValD(v_j_6526_, v_k_6527_);
    v___x_6529_ = l_Lean_NameMap_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1_spec__2(v___x_6528_);
    return v___x_6529_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1___boxed(
    mut v_j_6530_: *mut LeanObject,
    mut v_k_6531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6532_: *mut LeanObject = core::ptr::null_mut();
    v_res_6532_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1(
            v_j_6530_, v_k_6531_,
        );
    lean_dec_ref(v_k_6531_);
    return v_res_6532_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2(
    mut v_j_6533_: *mut LeanObject,
    mut v_k_6534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut LeanObject = core::ptr::null_mut();
    v___x_6535_ = l_Lean_Json_getObjValD(v_j_6533_, v_k_6534_);
    v___x_6536_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2_spec__4(v___x_6535_);
    return v___x_6536_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2___boxed(
    mut v_j_6537_: *mut LeanObject,
    mut v_k_6538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6539_: *mut LeanObject = core::ptr::null_mut();
    v_res_6539_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2(
            v_j_6537_, v_k_6538_,
        );
    lean_dec_ref(v_k_6538_);
    return v_res_6539_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__2() -> *mut LeanObject {
    let mut v___x_6544_: u8 = 0;
    let mut v___x_6545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut LeanObject = core::ptr::null_mut();
    v___x_6544_ = 1;
    v___x_6545_ = l_Lean_instFromJsonModuleSetup_fromJson___closed__1;
    v___x_6546_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_6545_, v___x_6544_);
    return v___x_6546_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3() -> *mut LeanObject {
    let mut v___x_6547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut LeanObject = core::ptr::null_mut();
    v___x_6547_ = l_Lean_instFromJsonImport_fromJson___closed__4;
    v___x_6548_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__2_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__2,
    );
    v___x_6549_ = lean_string_append(v___x_6548_, v___x_6547_);
    return v___x_6549_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__5() -> *mut LeanObject {
    let mut v___x_6552_: u8 = 0;
    let mut v___x_6553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut LeanObject = core::ptr::null_mut();
    v___x_6552_ = 1;
    v___x_6553_ = l_Lean_instFromJsonModuleSetup_fromJson___closed__4;
    v___x_6554_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_6553_, v___x_6552_);
    return v___x_6554_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__6() -> *mut LeanObject {
    let mut v___x_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut LeanObject = core::ptr::null_mut();
    v___x_6555_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__5),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__5_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__5,
    );
    v___x_6556_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3,
    );
    v___x_6557_ = lean_string_append(v___x_6556_, v___x_6555_);
    return v___x_6557_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__7() -> *mut LeanObject {
    let mut v___x_6558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: *mut LeanObject = core::ptr::null_mut();
    v___x_6558_ = l_Lean_instFromJsonImport_fromJson___closed__9;
    v___x_6559_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__6_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__6,
    );
    v___x_6560_ = lean_string_append(v___x_6559_, v___x_6558_);
    return v___x_6560_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__9() -> *mut LeanObject {
    let mut v___x_6563_: u8 = 0;
    let mut v___x_6564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6565_: *mut LeanObject = core::ptr::null_mut();
    v___x_6563_ = 1;
    v___x_6564_ = l_Lean_instFromJsonModuleSetup_fromJson___closed__8;
    v___x_6565_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_6564_, v___x_6563_);
    return v___x_6565_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__10() -> *mut LeanObject {
    let mut v___x_6566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut LeanObject = core::ptr::null_mut();
    v___x_6566_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__9),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__9_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__9,
    );
    v___x_6567_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3,
    );
    v___x_6568_ = lean_string_append(v___x_6567_, v___x_6566_);
    return v___x_6568_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__11() -> *mut LeanObject {
    let mut v___x_6569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut LeanObject = core::ptr::null_mut();
    v___x_6569_ = l_Lean_instFromJsonImport_fromJson___closed__9;
    v___x_6570_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__10),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__10_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__10,
    );
    v___x_6571_ = lean_string_append(v___x_6570_, v___x_6569_);
    return v___x_6571_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__12() -> *mut LeanObject {
    let mut v___x_6572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut LeanObject = core::ptr::null_mut();
    v___x_6572_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleHeader_fromJson___closed__9),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleHeader_fromJson___closed__9_once),
        _init_l_Lean_instFromJsonModuleHeader_fromJson___closed__9,
    );
    v___x_6573_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3,
    );
    v___x_6574_ = lean_string_append(v___x_6573_, v___x_6572_);
    return v___x_6574_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__13() -> *mut LeanObject {
    let mut v___x_6575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: *mut LeanObject = core::ptr::null_mut();
    v___x_6575_ = l_Lean_instFromJsonImport_fromJson___closed__9;
    v___x_6576_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__12),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__12_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__12,
    );
    v___x_6577_ = lean_string_append(v___x_6576_, v___x_6575_);
    return v___x_6577_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__15() -> *mut LeanObject {
    let mut v___x_6580_: u8 = 0;
    let mut v___x_6581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut LeanObject = core::ptr::null_mut();
    v___x_6580_ = 1;
    v___x_6581_ = l_Lean_instFromJsonModuleSetup_fromJson___closed__14;
    v___x_6582_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_6581_, v___x_6580_);
    return v___x_6582_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__16() -> *mut LeanObject {
    let mut v___x_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6585_: *mut LeanObject = core::ptr::null_mut();
    v___x_6583_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__15),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__15_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__15,
    );
    v___x_6584_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3,
    );
    v___x_6585_ = lean_string_append(v___x_6584_, v___x_6583_);
    return v___x_6585_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__17() -> *mut LeanObject {
    let mut v___x_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut LeanObject = core::ptr::null_mut();
    v___x_6586_ = l_Lean_instFromJsonImport_fromJson___closed__9;
    v___x_6587_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__16),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__16_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__16,
    );
    v___x_6588_ = lean_string_append(v___x_6587_, v___x_6586_);
    return v___x_6588_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__19() -> *mut LeanObject {
    let mut v___x_6591_: u8 = 0;
    let mut v___x_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6593_: *mut LeanObject = core::ptr::null_mut();
    v___x_6591_ = 1;
    v___x_6592_ = l_Lean_instFromJsonModuleSetup_fromJson___closed__18;
    v___x_6593_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_6592_, v___x_6591_);
    return v___x_6593_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__20() -> *mut LeanObject {
    let mut v___x_6594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6596_: *mut LeanObject = core::ptr::null_mut();
    v___x_6594_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__19),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__19_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__19,
    );
    v___x_6595_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3,
    );
    v___x_6596_ = lean_string_append(v___x_6595_, v___x_6594_);
    return v___x_6596_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__21() -> *mut LeanObject {
    let mut v___x_6597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6599_: *mut LeanObject = core::ptr::null_mut();
    v___x_6597_ = l_Lean_instFromJsonImport_fromJson___closed__9;
    v___x_6598_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__20),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__20_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__20,
    );
    v___x_6599_ = lean_string_append(v___x_6598_, v___x_6597_);
    return v___x_6599_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__23() -> *mut LeanObject {
    let mut v___x_6602_: u8 = 0;
    let mut v___x_6603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6604_: *mut LeanObject = core::ptr::null_mut();
    v___x_6602_ = 1;
    v___x_6603_ = l_Lean_instFromJsonModuleSetup_fromJson___closed__22;
    v___x_6604_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_6603_, v___x_6602_);
    return v___x_6604_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__24() -> *mut LeanObject {
    let mut v___x_6605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: *mut LeanObject = core::ptr::null_mut();
    v___x_6605_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__23),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__23_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__23,
    );
    v___x_6606_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3,
    );
    v___x_6607_ = lean_string_append(v___x_6606_, v___x_6605_);
    return v___x_6607_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__25() -> *mut LeanObject {
    let mut v___x_6608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6610_: *mut LeanObject = core::ptr::null_mut();
    v___x_6608_ = l_Lean_instFromJsonImport_fromJson___closed__9;
    v___x_6609_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__24),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__24_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__24,
    );
    v___x_6610_ = lean_string_append(v___x_6609_, v___x_6608_);
    return v___x_6610_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__27() -> *mut LeanObject {
    let mut v___x_6613_: u8 = 0;
    let mut v___x_6614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut LeanObject = core::ptr::null_mut();
    v___x_6613_ = 1;
    v___x_6614_ = l_Lean_instFromJsonModuleSetup_fromJson___closed__26;
    v___x_6615_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_6614_, v___x_6613_);
    return v___x_6615_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__28() -> *mut LeanObject {
    let mut v___x_6616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6618_: *mut LeanObject = core::ptr::null_mut();
    v___x_6616_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__27),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__27_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__27,
    );
    v___x_6617_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3,
    );
    v___x_6618_ = lean_string_append(v___x_6617_, v___x_6616_);
    return v___x_6618_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__29() -> *mut LeanObject {
    let mut v___x_6619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6621_: *mut LeanObject = core::ptr::null_mut();
    v___x_6619_ = l_Lean_instFromJsonImport_fromJson___closed__9;
    v___x_6620_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__28),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__28_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__28,
    );
    v___x_6621_ = lean_string_append(v___x_6620_, v___x_6619_);
    return v___x_6621_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__31() -> *mut LeanObject {
    let mut v___x_6624_: u8 = 0;
    let mut v___x_6625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6626_: *mut LeanObject = core::ptr::null_mut();
    v___x_6624_ = 1;
    v___x_6625_ = l_Lean_instFromJsonModuleSetup_fromJson___closed__30;
    v___x_6626_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_6625_, v___x_6624_);
    return v___x_6626_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__32() -> *mut LeanObject {
    let mut v___x_6627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6629_: *mut LeanObject = core::ptr::null_mut();
    v___x_6627_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__31),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__31_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__31,
    );
    v___x_6628_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__3_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__3,
    );
    v___x_6629_ = lean_string_append(v___x_6628_, v___x_6627_);
    return v___x_6629_;
}
pub unsafe fn _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__33() -> *mut LeanObject {
    let mut v___x_6630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut LeanObject = core::ptr::null_mut();
    v___x_6630_ = l_Lean_instFromJsonImport_fromJson___closed__9;
    v___x_6631_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__32),
        core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__32_once),
        _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__32,
    );
    v___x_6632_ = lean_string_append(v___x_6631_, v___x_6630_);
    return v___x_6632_;
}
pub unsafe fn l_Lean_instFromJsonModuleSetup_fromJson(
    mut v_json_6633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6639_: u8 = 0;
    let mut v___x_6640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6645_: u8 = 0;
    let mut v_a_6646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6649_: u8 = 0;
    let mut v___x_6651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6653_: u8 = 0;
    let mut v_a_6654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6660_: u8 = 0;
    let mut v___x_6661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6666_: u8 = 0;
    let mut v_a_6667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6670_: u8 = 0;
    let mut v___x_6672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6674_: u8 = 0;
    let mut v_a_6675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6681_: u8 = 0;
    let mut v___x_6682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6687_: u8 = 0;
    let mut v_a_6688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6691_: u8 = 0;
    let mut v___x_6693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6695_: u8 = 0;
    let mut v_a_6696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6702_: u8 = 0;
    let mut v___x_6703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6708_: u8 = 0;
    let mut v_a_6709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6712_: u8 = 0;
    let mut v___x_6714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6716_: u8 = 0;
    let mut v_a_6717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6723_: u8 = 0;
    let mut v___x_6724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6729_: u8 = 0;
    let mut v_a_6730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6733_: u8 = 0;
    let mut v___x_6735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6737_: u8 = 0;
    let mut v_a_6738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6744_: u8 = 0;
    let mut v___x_6745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6750_: u8 = 0;
    let mut v_a_6751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6754_: u8 = 0;
    let mut v___x_6756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6758_: u8 = 0;
    let mut v_a_6759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6765_: u8 = 0;
    let mut v___x_6766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6771_: u8 = 0;
    let mut v_a_6772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6775_: u8 = 0;
    let mut v___x_6777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6779_: u8 = 0;
    let mut v_a_6780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6786_: u8 = 0;
    let mut v___x_6787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6792_: u8 = 0;
    let mut v_a_6793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6796_: u8 = 0;
    let mut v___x_6798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6800_: u8 = 0;
    let mut v_a_6801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6804_: u8 = 0;
    let mut v___x_6805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: u8 = 0;
    let mut v___x_6808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6810_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6634_ = l_Lean_instReprModuleSetup_repr___redArg___closed__0;
                lean_inc(v_json_6633_);
                v___x_6635_ =
                    l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__0(
                        v_json_6633_,
                        v___x_6634_,
                    );
                if lean_obj_tag(v___x_6635_) == 0 {
                    lean_dec(v_json_6633_);
                    v_a_6636_ = lean_ctor_get(v___x_6635_, 0);
                    v_isSharedCheck_6645_ = (!lean_is_exclusive(v___x_6635_)) as u8;
                    if v_isSharedCheck_6645_ == 0 {
                        v___x_6638_ = v___x_6635_;
                        v_isShared_6639_ = v_isSharedCheck_6645_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6636_);
                        lean_dec(v___x_6635_);
                        v___x_6638_ = lean_box(0);
                        v_isShared_6639_ = v_isSharedCheck_6645_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_6635_) == 0 {
                        lean_dec(v_json_6633_);
                        v_a_6646_ = lean_ctor_get(v___x_6635_, 0);
                        v_isSharedCheck_6653_ = (!lean_is_exclusive(v___x_6635_)) as u8;
                        if v_isSharedCheck_6653_ == 0 {
                            v___x_6648_ = v___x_6635_;
                            v_isShared_6649_ = v_isSharedCheck_6653_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6646_);
                            lean_dec(v___x_6635_);
                            v___x_6648_ = lean_box(0);
                            v_isShared_6649_ = v_isSharedCheck_6653_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_6654_ = lean_ctor_get(v___x_6635_, 0);
                        lean_inc(v_a_6654_);
                        lean_dec_ref_known(v___x_6635_, 1);
                        v___x_6655_ = l_Lean_instToJsonModuleSetup_toJson___closed__0;
                        lean_inc(v_json_6633_);
                        v___x_6656_ =
                            l_Lean_Json_getObjValAs_x3f___at___00Lean_Plugin_fromJson_x3f_spec__1(
                                v_json_6633_,
                                v___x_6655_,
                            );
                        if lean_obj_tag(v___x_6656_) == 0 {
                            lean_dec(v_a_6654_);
                            lean_dec(v_json_6633_);
                            v_a_6657_ = lean_ctor_get(v___x_6656_, 0);
                            v_isSharedCheck_6666_ = (!lean_is_exclusive(v___x_6656_)) as u8;
                            if v_isSharedCheck_6666_ == 0 {
                                v___x_6659_ = v___x_6656_;
                                v_isShared_6660_ = v_isSharedCheck_6666_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_6657_);
                                lean_dec(v___x_6656_);
                                v___x_6659_ = lean_box(0);
                                v_isShared_6660_ = v_isSharedCheck_6666_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_6656_) == 0 {
                                lean_dec(v_a_6654_);
                                lean_dec(v_json_6633_);
                                v_a_6667_ = lean_ctor_get(v___x_6656_, 0);
                                v_isSharedCheck_6674_ = (!lean_is_exclusive(v___x_6656_)) as u8;
                                if v_isSharedCheck_6674_ == 0 {
                                    v___x_6669_ = v___x_6656_;
                                    v_isShared_6670_ = v_isSharedCheck_6674_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_6667_);
                                    lean_dec(v___x_6656_);
                                    v___x_6669_ = lean_box(0);
                                    v_isShared_6670_ = v_isSharedCheck_6674_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_6675_ = lean_ctor_get(v___x_6656_, 0);
                                lean_inc(v_a_6675_);
                                lean_dec_ref_known(v___x_6656_, 1);
                                v___x_6676_ = l_Lean_instReprModuleHeader_repr___redArg___closed__5;
                                lean_inc(v_json_6633_);
                                v___x_6677_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonImport_fromJson_spec__1(v_json_6633_, v___x_6676_);
                                if lean_obj_tag(v___x_6677_) == 0 {
                                    lean_dec(v_a_6675_);
                                    lean_dec(v_a_6654_);
                                    lean_dec(v_json_6633_);
                                    v_a_6678_ = lean_ctor_get(v___x_6677_, 0);
                                    v_isSharedCheck_6687_ = (!lean_is_exclusive(v___x_6677_)) as u8;
                                    if v_isSharedCheck_6687_ == 0 {
                                        v___x_6680_ = v___x_6677_;
                                        v_isShared_6681_ = v_isSharedCheck_6687_;
                                        state = 9;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6678_);
                                        lean_dec(v___x_6677_);
                                        v___x_6680_ = lean_box(0);
                                        v_isShared_6681_ = v_isSharedCheck_6687_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if lean_obj_tag(v___x_6677_) == 0 {
                                        lean_dec(v_a_6675_);
                                        lean_dec(v_a_6654_);
                                        lean_dec(v_json_6633_);
                                        v_a_6688_ = lean_ctor_get(v___x_6677_, 0);
                                        v_isSharedCheck_6695_ =
                                            (!lean_is_exclusive(v___x_6677_)) as u8;
                                        if v_isSharedCheck_6695_ == 0 {
                                            v___x_6690_ = v___x_6677_;
                                            v_isShared_6691_ = v_isSharedCheck_6695_;
                                            state = 11;
                                            continue;
                                        } else {
                                            lean_inc(v_a_6688_);
                                            lean_dec(v___x_6677_);
                                            v___x_6690_ = lean_box(0);
                                            v_isShared_6691_ = v_isSharedCheck_6695_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_6696_ = lean_ctor_get(v___x_6677_, 0);
                                        lean_inc(v_a_6696_);
                                        lean_dec_ref_known(v___x_6677_, 1);
                                        v___x_6697_ =
                                            l_Lean_instReprModuleHeader_repr___redArg___closed__0;
                                        lean_inc(v_json_6633_);
                                        v___x_6698_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__0(v_json_6633_, v___x_6697_);
                                        if lean_obj_tag(v___x_6698_) == 0 {
                                            lean_dec(v_a_6696_);
                                            lean_dec(v_a_6675_);
                                            lean_dec(v_a_6654_);
                                            lean_dec(v_json_6633_);
                                            v_a_6699_ = lean_ctor_get(v___x_6698_, 0);
                                            v_isSharedCheck_6708_ =
                                                (!lean_is_exclusive(v___x_6698_)) as u8;
                                            if v_isSharedCheck_6708_ == 0 {
                                                v___x_6701_ = v___x_6698_;
                                                v_isShared_6702_ = v_isSharedCheck_6708_;
                                                state = 13;
                                                continue;
                                            } else {
                                                lean_inc(v_a_6699_);
                                                lean_dec(v___x_6698_);
                                                v___x_6701_ = lean_box(0);
                                                v_isShared_6702_ = v_isSharedCheck_6708_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            if lean_obj_tag(v___x_6698_) == 0 {
                                                lean_dec(v_a_6696_);
                                                lean_dec(v_a_6675_);
                                                lean_dec(v_a_6654_);
                                                lean_dec(v_json_6633_);
                                                v_a_6709_ = lean_ctor_get(v___x_6698_, 0);
                                                v_isSharedCheck_6716_ =
                                                    (!lean_is_exclusive(v___x_6698_)) as u8;
                                                if v_isSharedCheck_6716_ == 0 {
                                                    v___x_6711_ = v___x_6698_;
                                                    v_isShared_6712_ = v_isSharedCheck_6716_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_6709_);
                                                    lean_dec(v___x_6698_);
                                                    v___x_6711_ = lean_box(0);
                                                    v_isShared_6712_ = v_isSharedCheck_6716_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_6717_ = lean_ctor_get(v___x_6698_, 0);
                                                lean_inc(v_a_6717_);
                                                lean_dec_ref_known(v___x_6698_, 1);
                                                v___x_6718_ = l_Lean_instReprModuleSetup_repr___redArg___closed__8;
                                                lean_inc(v_json_6633_);
                                                v___x_6719_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__1(v_json_6633_, v___x_6718_);
                                                if lean_obj_tag(v___x_6719_) == 0 {
                                                    lean_dec(v_a_6717_);
                                                    lean_dec(v_a_6696_);
                                                    lean_dec(v_a_6675_);
                                                    lean_dec(v_a_6654_);
                                                    lean_dec(v_json_6633_);
                                                    v_a_6720_ = lean_ctor_get(v___x_6719_, 0);
                                                    v_isSharedCheck_6729_ =
                                                        (!lean_is_exclusive(v___x_6719_)) as u8;
                                                    if v_isSharedCheck_6729_ == 0 {
                                                        v___x_6722_ = v___x_6719_;
                                                        v_isShared_6723_ = v_isSharedCheck_6729_;
                                                        state = 17;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_6720_);
                                                        lean_dec(v___x_6719_);
                                                        v___x_6722_ = lean_box(0);
                                                        v_isShared_6723_ = v_isSharedCheck_6729_;
                                                        state = 17;
                                                        continue;
                                                    }
                                                } else {
                                                    if lean_obj_tag(v___x_6719_) == 0 {
                                                        lean_dec(v_a_6717_);
                                                        lean_dec(v_a_6696_);
                                                        lean_dec(v_a_6675_);
                                                        lean_dec(v_a_6654_);
                                                        lean_dec(v_json_6633_);
                                                        v_a_6730_ = lean_ctor_get(v___x_6719_, 0);
                                                        v_isSharedCheck_6737_ =
                                                            (!lean_is_exclusive(v___x_6719_)) as u8;
                                                        if v_isSharedCheck_6737_ == 0 {
                                                            v___x_6732_ = v___x_6719_;
                                                            v_isShared_6733_ =
                                                                v_isSharedCheck_6737_;
                                                            state = 19;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_6730_);
                                                            lean_dec(v___x_6719_);
                                                            v___x_6732_ = lean_box(0);
                                                            v_isShared_6733_ =
                                                                v_isSharedCheck_6737_;
                                                            state = 19;
                                                            continue;
                                                        }
                                                    } else {
                                                        v_a_6738_ = lean_ctor_get(v___x_6719_, 0);
                                                        lean_inc(v_a_6738_);
                                                        lean_dec_ref_known(v___x_6719_, 1);
                                                        v___x_6739_ = l_Lean_instReprModuleSetup_repr___redArg___closed__12;
                                                        lean_inc(v_json_6633_);
                                                        v___x_6740_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__2(v_json_6633_, v___x_6739_);
                                                        if lean_obj_tag(v___x_6740_) == 0 {
                                                            lean_dec(v_a_6738_);
                                                            lean_dec(v_a_6717_);
                                                            lean_dec(v_a_6696_);
                                                            lean_dec(v_a_6675_);
                                                            lean_dec(v_a_6654_);
                                                            lean_dec(v_json_6633_);
                                                            v_a_6741_ =
                                                                lean_ctor_get(v___x_6740_, 0);
                                                            v_isSharedCheck_6750_ =
                                                                (!lean_is_exclusive(v___x_6740_))
                                                                    as u8;
                                                            if v_isSharedCheck_6750_ == 0 {
                                                                v___x_6743_ = v___x_6740_;
                                                                v_isShared_6744_ =
                                                                    v_isSharedCheck_6750_;
                                                                state = 21;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_6741_);
                                                                lean_dec(v___x_6740_);
                                                                v___x_6743_ = lean_box(0);
                                                                v_isShared_6744_ =
                                                                    v_isSharedCheck_6750_;
                                                                state = 21;
                                                                continue;
                                                            }
                                                        } else {
                                                            if lean_obj_tag(v___x_6740_) == 0 {
                                                                lean_dec(v_a_6738_);
                                                                lean_dec(v_a_6717_);
                                                                lean_dec(v_a_6696_);
                                                                lean_dec(v_a_6675_);
                                                                lean_dec(v_a_6654_);
                                                                lean_dec(v_json_6633_);
                                                                v_a_6751_ =
                                                                    lean_ctor_get(v___x_6740_, 0);
                                                                v_isSharedCheck_6758_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_6740_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_6758_ == 0 {
                                                                    v___x_6753_ = v___x_6740_;
                                                                    v_isShared_6754_ =
                                                                        v_isSharedCheck_6758_;
                                                                    state = 23;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_6751_);
                                                                    lean_dec(v___x_6740_);
                                                                    v___x_6753_ = lean_box(0);
                                                                    v_isShared_6754_ =
                                                                        v_isSharedCheck_6758_;
                                                                    state = 23;
                                                                    continue;
                                                                }
                                                            } else {
                                                                v_a_6759_ =
                                                                    lean_ctor_get(v___x_6740_, 0);
                                                                lean_inc(v_a_6759_);
                                                                lean_dec_ref_known(v___x_6740_, 1);
                                                                v___x_6760_ = l_Lean_instReprModuleSetup_repr___redArg___closed__14;
                                                                lean_inc(v_json_6633_);
                                                                v___x_6761_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__3(v_json_6633_, v___x_6760_);
                                                                if lean_obj_tag(v___x_6761_) == 0 {
                                                                    lean_dec(v_a_6759_);
                                                                    lean_dec(v_a_6738_);
                                                                    lean_dec(v_a_6717_);
                                                                    lean_dec(v_a_6696_);
                                                                    lean_dec(v_a_6675_);
                                                                    lean_dec(v_a_6654_);
                                                                    lean_dec(v_json_6633_);
                                                                    v_a_6762_ = lean_ctor_get(
                                                                        v___x_6761_,
                                                                        0,
                                                                    );
                                                                    v_isSharedCheck_6771_ =
                                                                        (!lean_is_exclusive(
                                                                            v___x_6761_,
                                                                        ))
                                                                            as u8;
                                                                    if v_isSharedCheck_6771_ == 0 {
                                                                        v___x_6764_ = v___x_6761_;
                                                                        v_isShared_6765_ =
                                                                            v_isSharedCheck_6771_;
                                                                        state = 25;
                                                                        continue;
                                                                    } else {
                                                                        lean_inc(v_a_6762_);
                                                                        lean_dec(v___x_6761_);
                                                                        v___x_6764_ = lean_box(0);
                                                                        v_isShared_6765_ =
                                                                            v_isSharedCheck_6771_;
                                                                        state = 25;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    if lean_obj_tag(v___x_6761_)
                                                                        == 0
                                                                    {
                                                                        lean_dec(v_a_6759_);
                                                                        lean_dec(v_a_6738_);
                                                                        lean_dec(v_a_6717_);
                                                                        lean_dec(v_a_6696_);
                                                                        lean_dec(v_a_6675_);
                                                                        lean_dec(v_a_6654_);
                                                                        lean_dec(v_json_6633_);
                                                                        v_a_6772_ = lean_ctor_get(
                                                                            v___x_6761_,
                                                                            0,
                                                                        );
                                                                        v_isSharedCheck_6779_ =
                                                                            (!lean_is_exclusive(
                                                                                v___x_6761_,
                                                                            ))
                                                                                as u8;
                                                                        if v_isSharedCheck_6779_
                                                                            == 0
                                                                        {
                                                                            v___x_6774_ =
                                                                                v___x_6761_;
                                                                            v_isShared_6775_ = v_isSharedCheck_6779_;
                                                                            state = 27;
                                                                            continue;
                                                                        } else {
                                                                            lean_inc(v_a_6772_);
                                                                            lean_dec(v___x_6761_);
                                                                            v___x_6774_ =
                                                                                lean_box(0);
                                                                            v_isShared_6775_ = v_isSharedCheck_6779_;
                                                                            state = 27;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        v_a_6780_ = lean_ctor_get(
                                                                            v___x_6761_,
                                                                            0,
                                                                        );
                                                                        lean_inc(v_a_6780_);
                                                                        lean_dec_ref_known(
                                                                            v___x_6761_,
                                                                            1,
                                                                        );
                                                                        v___x_6781_ = l_Lean_instReprModuleSetup_repr___redArg___closed__16;
                                                                        v___x_6782_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonModuleSetup_fromJson_spec__4(v_json_6633_, v___x_6781_);
                                                                        if lean_obj_tag(v___x_6782_)
                                                                            == 0
                                                                        {
                                                                            lean_dec(v_a_6780_);
                                                                            lean_dec(v_a_6759_);
                                                                            lean_dec(v_a_6738_);
                                                                            lean_dec(v_a_6717_);
                                                                            lean_dec(v_a_6696_);
                                                                            lean_dec(v_a_6675_);
                                                                            lean_dec(v_a_6654_);
                                                                            v_a_6783_ =
                                                                                lean_ctor_get(
                                                                                    v___x_6782_,
                                                                                    0,
                                                                                );
                                                                            v_isSharedCheck_6792_ =
                                                                                (!lean_is_exclusive(
                                                                                    v___x_6782_,
                                                                                ))
                                                                                    as u8;
                                                                            if v_isSharedCheck_6792_
                                                                                == 0
                                                                            {
                                                                                v___x_6785_ =
                                                                                    v___x_6782_;
                                                                                v_isShared_6786_ = v_isSharedCheck_6792_;
                                                                                state = 29;
                                                                                continue;
                                                                            } else {
                                                                                lean_inc(v_a_6783_);
                                                                                lean_dec(
                                                                                    v___x_6782_,
                                                                                );
                                                                                v___x_6785_ =
                                                                                    lean_box(0);
                                                                                v_isShared_6786_ = v_isSharedCheck_6792_;
                                                                                state = 29;
                                                                                continue;
                                                                            }
                                                                        } else {
                                                                            if lean_obj_tag(
                                                                                v___x_6782_,
                                                                            ) == 0
                                                                            {
                                                                                lean_dec(v_a_6780_);
                                                                                lean_dec(v_a_6759_);
                                                                                lean_dec(v_a_6738_);
                                                                                lean_dec(v_a_6717_);
                                                                                lean_dec(v_a_6696_);
                                                                                lean_dec(v_a_6675_);
                                                                                lean_dec(v_a_6654_);
                                                                                v_a_6793_ =
                                                                                    lean_ctor_get(
                                                                                        v___x_6782_,
                                                                                        0,
                                                                                    );
                                                                                v_isSharedCheck_6800_ = (!lean_is_exclusive(v___x_6782_)) as u8;
                                                                                if v_isSharedCheck_6800_ == 0 {
v___x_6795_ = v___x_6782_;
v_isShared_6796_ = v_isSharedCheck_6800_;
state = 31; continue;
} else {
lean_inc(v_a_6793_);
lean_dec(v___x_6782_);
v___x_6795_ = lean_box(0);
v_isShared_6796_ = v_isSharedCheck_6800_;
state = 31; continue;
}
                                                                            } else {
                                                                                v_a_6801_ =
                                                                                    lean_ctor_get(
                                                                                        v___x_6782_,
                                                                                        0,
                                                                                    );
                                                                                v_isSharedCheck_6810_ = (!lean_is_exclusive(v___x_6782_)) as u8;
                                                                                if v_isSharedCheck_6810_ == 0 {
v___x_6803_ = v___x_6782_;
v_isShared_6804_ = v_isSharedCheck_6810_;
state = 33; continue;
} else {
lean_inc(v_a_6801_);
lean_dec(v___x_6782_);
v___x_6803_ = lean_box(0);
v_isShared_6804_ = v_isSharedCheck_6810_;
state = 33; continue;
}
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_6640_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleSetup_fromJson___closed__7_once
                    ),
                    _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__7,
                );
                v___x_6641_ = lean_string_append(v___x_6640_, v_a_6636_);
                lean_dec(v_a_6636_);
                if v_isShared_6639_ == 0 {
                    lean_ctor_set(v___x_6638_, 0, v___x_6641_);
                    v___x_6643_ = v___x_6638_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6644_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6644_, 0, v___x_6641_);
                    v___x_6643_ = v_reuseFailAlloc_6644_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6643_;
            }
            3 => {
                if v_isShared_6649_ == 0 {
                    lean_ctor_set_tag(v___x_6648_, 0);
                    v___x_6651_ = v___x_6648_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6652_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6652_, 0, v_a_6646_);
                    v___x_6651_ = v_reuseFailAlloc_6652_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6651_;
            }
            5 => {
                v___x_6661_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleSetup_fromJson___closed__11_once
                    ),
                    _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__11,
                );
                v___x_6662_ = lean_string_append(v___x_6661_, v_a_6657_);
                lean_dec(v_a_6657_);
                if v_isShared_6660_ == 0 {
                    lean_ctor_set(v___x_6659_, 0, v___x_6662_);
                    v___x_6664_ = v___x_6659_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6665_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6665_, 0, v___x_6662_);
                    v___x_6664_ = v_reuseFailAlloc_6665_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6664_;
            }
            7 => {
                if v_isShared_6670_ == 0 {
                    lean_ctor_set_tag(v___x_6669_, 0);
                    v___x_6672_ = v___x_6669_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6673_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6673_, 0, v_a_6667_);
                    v___x_6672_ = v_reuseFailAlloc_6673_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6672_;
            }
            9 => {
                v___x_6682_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__13),
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleSetup_fromJson___closed__13_once
                    ),
                    _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__13,
                );
                v___x_6683_ = lean_string_append(v___x_6682_, v_a_6678_);
                lean_dec(v_a_6678_);
                if v_isShared_6681_ == 0 {
                    lean_ctor_set(v___x_6680_, 0, v___x_6683_);
                    v___x_6685_ = v___x_6680_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6686_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6686_, 0, v___x_6683_);
                    v___x_6685_ = v_reuseFailAlloc_6686_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6685_;
            }
            11 => {
                if v_isShared_6691_ == 0 {
                    lean_ctor_set_tag(v___x_6690_, 0);
                    v___x_6693_ = v___x_6690_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6694_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6694_, 0, v_a_6688_);
                    v___x_6693_ = v_reuseFailAlloc_6694_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6693_;
            }
            13 => {
                v___x_6703_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__17),
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleSetup_fromJson___closed__17_once
                    ),
                    _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__17,
                );
                v___x_6704_ = lean_string_append(v___x_6703_, v_a_6699_);
                lean_dec(v_a_6699_);
                if v_isShared_6702_ == 0 {
                    lean_ctor_set(v___x_6701_, 0, v___x_6704_);
                    v___x_6706_ = v___x_6701_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6707_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6707_, 0, v___x_6704_);
                    v___x_6706_ = v_reuseFailAlloc_6707_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6706_;
            }
            15 => {
                if v_isShared_6712_ == 0 {
                    lean_ctor_set_tag(v___x_6711_, 0);
                    v___x_6714_ = v___x_6711_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6715_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6715_, 0, v_a_6709_);
                    v___x_6714_ = v_reuseFailAlloc_6715_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_6714_;
            }
            17 => {
                v___x_6724_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__21),
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleSetup_fromJson___closed__21_once
                    ),
                    _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__21,
                );
                v___x_6725_ = lean_string_append(v___x_6724_, v_a_6720_);
                lean_dec(v_a_6720_);
                if v_isShared_6723_ == 0 {
                    lean_ctor_set(v___x_6722_, 0, v___x_6725_);
                    v___x_6727_ = v___x_6722_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6728_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6728_, 0, v___x_6725_);
                    v___x_6727_ = v_reuseFailAlloc_6728_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_6727_;
            }
            19 => {
                if v_isShared_6733_ == 0 {
                    lean_ctor_set_tag(v___x_6732_, 0);
                    v___x_6735_ = v___x_6732_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_6736_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6736_, 0, v_a_6730_);
                    v___x_6735_ = v_reuseFailAlloc_6736_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_6735_;
            }
            21 => {
                v___x_6745_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__25),
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleSetup_fromJson___closed__25_once
                    ),
                    _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__25,
                );
                v___x_6746_ = lean_string_append(v___x_6745_, v_a_6741_);
                lean_dec(v_a_6741_);
                if v_isShared_6744_ == 0 {
                    lean_ctor_set(v___x_6743_, 0, v___x_6746_);
                    v___x_6748_ = v___x_6743_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_6749_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6749_, 0, v___x_6746_);
                    v___x_6748_ = v_reuseFailAlloc_6749_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_6748_;
            }
            23 => {
                if v_isShared_6754_ == 0 {
                    lean_ctor_set_tag(v___x_6753_, 0);
                    v___x_6756_ = v___x_6753_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_6757_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6757_, 0, v_a_6751_);
                    v___x_6756_ = v_reuseFailAlloc_6757_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_6756_;
            }
            25 => {
                v___x_6766_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__29),
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleSetup_fromJson___closed__29_once
                    ),
                    _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__29,
                );
                v___x_6767_ = lean_string_append(v___x_6766_, v_a_6762_);
                lean_dec(v_a_6762_);
                if v_isShared_6765_ == 0 {
                    lean_ctor_set(v___x_6764_, 0, v___x_6767_);
                    v___x_6769_ = v___x_6764_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_6770_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6770_, 0, v___x_6767_);
                    v___x_6769_ = v_reuseFailAlloc_6770_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_6769_;
            }
            27 => {
                if v_isShared_6775_ == 0 {
                    lean_ctor_set_tag(v___x_6774_, 0);
                    v___x_6777_ = v___x_6774_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_6778_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6778_, 0, v_a_6772_);
                    v___x_6777_ = v_reuseFailAlloc_6778_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_6777_;
            }
            29 => {
                v___x_6787_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instFromJsonModuleSetup_fromJson___closed__33),
                    core::ptr::addr_of_mut!(
                        l_Lean_instFromJsonModuleSetup_fromJson___closed__33_once
                    ),
                    _init_l_Lean_instFromJsonModuleSetup_fromJson___closed__33,
                );
                v___x_6788_ = lean_string_append(v___x_6787_, v_a_6783_);
                lean_dec(v_a_6783_);
                if v_isShared_6786_ == 0 {
                    lean_ctor_set(v___x_6785_, 0, v___x_6788_);
                    v___x_6790_ = v___x_6785_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_6791_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6791_, 0, v___x_6788_);
                    v___x_6790_ = v_reuseFailAlloc_6791_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_6790_;
            }
            31 => {
                if v_isShared_6796_ == 0 {
                    lean_ctor_set_tag(v___x_6795_, 0);
                    v___x_6798_ = v___x_6795_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_6799_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6799_, 0, v_a_6793_);
                    v___x_6798_ = v_reuseFailAlloc_6799_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_6798_;
            }
            33 => {
                v___x_6805_ = lean_alloc_ctor(0, 7, (1) as u32);
                lean_ctor_set(v___x_6805_, 0, v_a_6654_);
                lean_ctor_set(v___x_6805_, 1, v_a_6675_);
                lean_ctor_set(v___x_6805_, 2, v_a_6717_);
                lean_ctor_set(v___x_6805_, 3, v_a_6738_);
                lean_ctor_set(v___x_6805_, 4, v_a_6759_);
                lean_ctor_set(v___x_6805_, 5, v_a_6780_);
                lean_ctor_set(v___x_6805_, 6, v_a_6801_);
                v___x_6806_ = (lean_unbox(v_a_6696_) as u8);
                lean_dec(v_a_6696_);
                lean_ctor_set_uint8(
                    v___x_6805_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v___x_6806_,
                );
                if v_isShared_6804_ == 0 {
                    lean_ctor_set(v___x_6803_, 0, v___x_6805_);
                    v___x_6808_ = v___x_6803_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_6809_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6809_, 0, v___x_6805_);
                    v___x_6808_ = v_reuseFailAlloc_6809_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_6808_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ModuleSetup_load(mut v_path_6814_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6820_: u8 = 0;
    let mut v_a_6822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6840_: u8 = 0;
    let mut v___x_6842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6844_: u8 = 0;
    let mut v_isSharedCheck_6845_: u8 = 0;
    let mut v_a_6846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6849_: u8 = 0;
    let mut v___x_6851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6853_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6816_ = l_IO_FS_readFile(v_path_6814_);
                if lean_obj_tag(v___x_6816_) == 0 {
                    v_a_6817_ = lean_ctor_get(v___x_6816_, 0);
                    v_isSharedCheck_6845_ = (!lean_is_exclusive(v___x_6816_)) as u8;
                    if v_isSharedCheck_6845_ == 0 {
                        v___x_6819_ = v___x_6816_;
                        v_isShared_6820_ = v_isSharedCheck_6845_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6817_);
                        lean_dec(v___x_6816_);
                        v___x_6819_ = lean_box(0);
                        v_isShared_6820_ = v_isSharedCheck_6845_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6846_ = lean_ctor_get(v___x_6816_, 0);
                    v_isSharedCheck_6853_ = (!lean_is_exclusive(v___x_6816_)) as u8;
                    if v_isSharedCheck_6853_ == 0 {
                        v___x_6848_ = v___x_6816_;
                        v_isShared_6849_ = v_isSharedCheck_6853_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_6846_);
                        lean_dec(v___x_6816_);
                        v___x_6848_ = lean_box(0);
                        v_isShared_6849_ = v_isSharedCheck_6853_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6832_ = l_Lean_Json_parse(v_a_6817_);
                if lean_obj_tag(v___x_6832_) == 0 {
                    v_a_6833_ = lean_ctor_get(v___x_6832_, 0);
                    lean_inc(v_a_6833_);
                    lean_dec_ref_known(v___x_6832_, 1);
                    v_a_6822_ = v_a_6833_;
                    state = 2;
                    continue;
                } else {
                    v_a_6834_ = lean_ctor_get(v___x_6832_, 0);
                    lean_inc(v_a_6834_);
                    lean_dec_ref_known(v___x_6832_, 1);
                    v___x_6835_ = l_Lean_instFromJsonModuleSetup_fromJson(v_a_6834_);
                    if lean_obj_tag(v___x_6835_) == 0 {
                        v_a_6836_ = lean_ctor_get(v___x_6835_, 0);
                        lean_inc(v_a_6836_);
                        lean_dec_ref_known(v___x_6835_, 1);
                        v_a_6822_ = v_a_6836_;
                        state = 2;
                        continue;
                    } else {
                        lean_del_object(v___x_6819_);
                        v_a_6837_ = lean_ctor_get(v___x_6835_, 0);
                        v_isSharedCheck_6844_ = (!lean_is_exclusive(v___x_6835_)) as u8;
                        if v_isSharedCheck_6844_ == 0 {
                            v___x_6839_ = v___x_6835_;
                            v_isShared_6840_ = v_isSharedCheck_6844_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_6837_);
                            lean_dec(v___x_6835_);
                            v___x_6839_ = lean_box(0);
                            v_isShared_6840_ = v_isSharedCheck_6844_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_6823_ = l_Lean_ModuleSetup_load___closed__0;
                v___x_6824_ = lean_string_append(v___x_6823_, v_path_6814_);
                v___x_6825_ = l_Lean_instFromJsonImport_fromJson___closed__9;
                v___x_6826_ = lean_string_append(v___x_6824_, v___x_6825_);
                v___x_6827_ = lean_string_append(v___x_6826_, v_a_6822_);
                lean_dec_ref(v_a_6822_);
                v___x_6828_ = lean_mk_io_user_error(v___x_6827_);
                if v_isShared_6820_ == 0 {
                    lean_ctor_set_tag(v___x_6819_, 1);
                    lean_ctor_set(v___x_6819_, 0, v___x_6828_);
                    v___x_6830_ = v___x_6819_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6831_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6831_, 0, v___x_6828_);
                    v___x_6830_ = v_reuseFailAlloc_6831_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6830_;
            }
            4 => {
                if v_isShared_6840_ == 0 {
                    lean_ctor_set_tag(v___x_6839_, 0);
                    v___x_6842_ = v___x_6839_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6843_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6843_, 0, v_a_6837_);
                    v___x_6842_ = v_reuseFailAlloc_6843_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6842_;
            }
            6 => {
                if v_isShared_6849_ == 0 {
                    v___x_6851_ = v___x_6848_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6852_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6852_, 0, v_a_6846_);
                    v___x_6851_ = v_reuseFailAlloc_6852_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6851_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ModuleSetup_load___boxed(
    mut v_path_6854_: *mut LeanObject,
    mut v_a_6855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6856_: *mut LeanObject = core::ptr::null_mut();
    v_res_6856_ = l_Lean_ModuleSetup_load(v_path_6854_);
    lean_dec_ref(v_path_6854_);
    return v_res_6856_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Setup(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Json_Parser(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_LeanOptions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_instInhabitedIRPhases_default = _init_l_Lean_instInhabitedIRPhases_default();
    l_Lean_instInhabitedIRPhases = _init_l_Lean_instInhabitedIRPhases();
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Setup(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Setup(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Json_Parser(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_LeanOptions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Setup(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Setup(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Setup(builtin);
}
