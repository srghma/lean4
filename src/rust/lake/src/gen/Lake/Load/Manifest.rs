// Lean compiler output
// Module: Lake.Load.Manifest
// Imports: Lake.Util.Version Lake.Config.Defaults Lake.Util.Git Lake.Util.Error Lake.Util.FilePath Lake.Util.JsonObject Init.Data.Option.Coe
use crate::r#gen::Init::Data::List::Basic::l_List_appendTR___redArg;
use crate::r#gen::Init::Data::Option::Coe::{
    initialize_Init_Data_Option_Coe, runtime_initialize_Init_Data_Option_Coe,
};
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Meta::Defs::l_String_toName;
use crate::r#gen::Init::System::IO::{l_IO_FS_readFile, l_IO_FS_writeFile};
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lake::Config::Defaults::{
    initialize_Lake_Config_Defaults, l_Lake_defaultConfigFile, l_Lake_defaultLakeDir,
    l_Lake_defaultManifestFile, runtime_initialize_Lake_Config_Defaults,
};
use crate::r#gen::Lake::Util::Error::{
    initialize_Lake_Util_Error, runtime_initialize_Lake_Util_Error,
};
use crate::r#gen::Lake::Util::FilePath::{
    initialize_Lake_Util_FilePath, l_Lake_joinRelative, l_Lake_mkRelPathString,
    runtime_initialize_Lake_Util_FilePath,
};
use crate::r#gen::Lake::Util::Git::{initialize_Lake_Util_Git, runtime_initialize_Lake_Util_Git};
use crate::r#gen::Lake::Util::JsonObject::{
    initialize_Lake_Util_JsonObject, l_Lake_JsonObject_getJson_x3f,
    runtime_initialize_Lake_Util_JsonObject,
};
use crate::r#gen::Lake::Util::Version::{
    initialize_Lake_Util_Version, l_Lake_SemVerCore_toString, l_Lake_StdVer_compare,
    l_Lake_StdVer_parse, l_Lake_StdVer_toString, l_Lake_instOrdSemVerCore_ord,
    runtime_initialize_Lake_Util_Version,
};
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getBool_x3f, l_Lean_Json_getObj_x3f, l_Lean_Json_getStr_x3f, l_Lean_Json_mkObj,
};
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::{
    l_Lean_Json_getTag_x3f, l_Lean_Json_parseCtorFields, l_Lean_Name_fromJson_x3f,
};
use crate::r#gen::Lean::Data::Json::Parser::l_Lean_Json_parse;
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_pretty;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg;
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::{
    lean_int_dec_lt, lean_nat_abs, lean_nat_to_int,
};
use crate::ffi::lean_string_compare;
use crate::ffi::lean_string_push;
use crate::ffi::lean_string_append;
use crate::ffi::{lean_usize_add, lean_usize_dec_lt};
use crate::ffi::{
    lean_array_get, lean_array_get_borrowed, lean_array_push, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_lt, lean_nat_mul, lean_panic_fn_borrowed, lean_string_dec_eq,
};
pub static l_Lake_Manifest_version___closed__0_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Manifest_version___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_version___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Manifest_version___closed__1_value: crate::leanh::LeanStringObject<1> =
    crate::leanh::LeanStringObject {
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
static mut l_Lake_Manifest_version___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_version___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Manifest_version___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Manifest_version___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Manifest_version___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Manifest_version___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_version___closed__2_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Manifest_version: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_version___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [91, 97, 110, 111, 110, 121, 109, 111, 117, 115, 93, 0]};
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__1_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 96, 78, 97, 109, 101, 96, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0___closed__0_value: crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 96, 78, 97, 109, 101, 77, 97, 112, 96, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__0_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 97, 103, 32, 102, 111, 117, 110, 100, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 97, 116, 104, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [103, 105, 116, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__4_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 109, 97, 116, 99, 104, 101, 100, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__5_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 97, 109, 101, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6_value) as *mut crate::leanh::LeanObject,5949480926448383572 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__8_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [111, 112, 116, 115, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__8_value) as *mut crate::leanh::LeanObject,6757902475951869745 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 104, 101, 114, 105, 116, 101, 100, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10_value) as *mut crate::leanh::LeanObject,12300627446236246789 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [117, 114, 108, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12_value) as *mut crate::leanh::LeanObject,13553787595962583263 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [114, 101, 118, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14_value) as *mut crate::leanh::LeanObject,13413232538026238679 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 112, 117, 116, 82, 101, 118, 63, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__16_value) as *mut crate::leanh::LeanObject,12690480075422432291 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__18_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [115, 117, 98, 68, 105, 114, 63, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__19_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__18_value) as *mut crate::leanh::LeanObject,2445562219981734856 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__20_value: crate::leanh::LeanArrayObject<7> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*7) as u16, other: 0, tag: 246 }, m_size: 7, m_capacity: 7, m_data: [core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__9_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__11_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__13_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__15_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__17_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__19_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__21_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__20_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [100, 105, 114, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__23_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22_value) as *mut crate::leanh::LeanObject,13475008931517935237 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__24_value: crate::leanh::LeanArrayObject<4> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4) as u16, other: 0, tag: 246 }, m_size: 4, m_capacity: 4, m_data: [core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__9_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__11_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__23_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__25_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__24_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6___closed__0_value:
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
    m_fun: l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 66, 97, 108, 97, 110, 99, 105, 110, 103, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 76, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__2_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 76, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__5_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 82, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__6_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 82, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6___closed__0_value:
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
    m_fun: l___private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedPackageEntryV6_default___closed__0_value:
    crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 8) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_Manifest_version___closed__1_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instInhabitedPackageEntryV6_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedPackageEntryV6_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedPackageEntryV6_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedPackageEntryV6_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedPackageEntryV6_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedPackageEntrySrc_default___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Manifest_version___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instInhabitedPackageEntrySrc_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedPackageEntrySrc_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedPackageEntrySrc_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedPackageEntrySrc_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedPackageEntrySrc: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedPackageEntrySrc_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instInhabitedPackageEntry_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedPackageEntry_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedPackageEntry_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedPackageEntry: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_PackageEntry_toJson___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [115, 99, 111, 112, 101, 0],
    };
static mut l_Lake_PackageEntry_toJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_toJson___closed__1_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [99, 111, 110, 102, 105, 103, 70, 105, 108, 101, 0],
    };
static mut l_Lake_PackageEntry_toJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_toJson___closed__2_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [109, 97, 110, 105, 102, 101, 115, 116, 70, 105, 108, 101, 0],
    };
static mut l_Lake_PackageEntry_toJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_toJson___closed__3_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [116, 121, 112, 101, 0],
    };
static mut l_Lake_PackageEntry_toJson___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_toJson___closed__4_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake_PackageEntry_toJson___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_toJson___closed__5_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_PackageEntry_toJson___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_toJson___closed__6_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3_value) as *mut crate::leanh::LeanObject] };
static mut l_Lake_PackageEntry_toJson___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_toJson___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_PackageEntry_toJson___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_toJson___closed__8_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [105, 110, 112, 117, 116, 82, 101, 118, 0],
    };
static mut l_Lake_PackageEntry_toJson___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_toJson___closed__9_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [115, 117, 98, 68, 105, 114, 0],
    };
static mut l_Lake_PackageEntry_toJson___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_instToJson___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_PackageEntry_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_PackageEntry_instToJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_instToJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_PackageEntry_instToJson: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_instToJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___lam__0___closed__0_value:
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
        112, 97, 99, 107, 97, 103, 101, 32, 101, 110, 116, 114, 121, 58, 32, 0,
    ],
};
static mut l_Lake_PackageEntry_fromJson_x3f___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__0_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
            58, 32, 110, 97, 109, 101, 0,
        ],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__1_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [110, 97, 109, 101, 58, 32, 0],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__2_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
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
            112, 97, 99, 107, 97, 103, 101, 32, 101, 110, 116, 114, 121, 32, 39, 0,
        ],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__3_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [39, 58, 32, 0],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__4_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [115, 117, 98, 68, 105, 114, 58, 32, 0],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__5_value: crate::leanh::LeanStringObject<29> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            117, 110, 107, 110, 111, 119, 110, 32, 112, 97, 99, 107, 97, 103, 101, 32, 101, 110,
            116, 114, 121, 32, 116, 121, 112, 101, 32, 39, 0,
        ],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__6_value: crate::leanh::LeanStringObject<24> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
            58, 32, 117, 114, 108, 0,
        ],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__7_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [117, 114, 108, 58, 32, 0],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__8_value: crate::leanh::LeanStringObject<24> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
            58, 32, 114, 101, 118, 0,
        ],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__9_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [114, 101, 118, 58, 32, 0],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__10_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [105, 110, 112, 117, 116, 82, 101, 118, 58, 32, 0],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__11_value: crate::leanh::LeanStringObject<24> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
            58, 32, 100, 105, 114, 0,
        ],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__12_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [100, 105, 114, 58, 32, 0],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__13_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            109, 97, 110, 105, 102, 101, 115, 116, 70, 105, 108, 101, 58, 32, 0,
        ],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__14_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
            58, 32, 116, 121, 112, 101, 0,
        ],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__15_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [116, 121, 112, 101, 58, 32, 0],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__16_value: crate::leanh::LeanStringObject<30> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
            58, 32, 105, 110, 104, 101, 114, 105, 116, 101, 100, 0,
        ],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__17_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [105, 110, 104, 101, 114, 105, 116, 101, 100, 58, 32, 0],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__18_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [99, 111, 110, 102, 105, 103, 70, 105, 108, 101, 58, 32, 0],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__19_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [115, 99, 111, 112, 101, 58, 32, 0],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PackageEntry_instFromJson___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_PackageEntry_fromJson_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_PackageEntry_instFromJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_instFromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_PackageEntry_instFromJson: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_instFromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Manifest_toJson___closed__0_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_Manifest_toJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_toJson___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_Manifest_toJson___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Manifest_toJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Manifest_toJson___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Manifest_toJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Manifest_toJson___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Manifest_toJson___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Manifest_toJson___closed__4_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            102, 105, 120, 101, 100, 84, 111, 111, 108, 99, 104, 97, 105, 110, 0,
        ],
    };
static mut l_Lake_Manifest_toJson___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_toJson___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Manifest_toJson___closed__5_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [108, 97, 107, 101, 68, 105, 114, 0],
    };
static mut l_Lake_Manifest_toJson___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_toJson___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Manifest_toJson___closed__6_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [112, 97, 99, 107, 97, 103, 101, 115, 68, 105, 114, 0],
    };
static mut l_Lake_Manifest_toJson___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_toJson___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Manifest_toJson___closed__7_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [112, 97, 99, 107, 97, 103, 101, 115, 0],
    };
static mut l_Lake_Manifest_toJson___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_toJson___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Manifest_instToJson___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Manifest_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Manifest_instToJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_instToJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Manifest_instToJson: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_instToJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__0_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        105, 110, 99, 111, 109, 112, 97, 116, 105, 98, 108, 101, 32, 109, 97, 110, 105, 102, 101,
        115, 116, 32, 118, 101, 114, 115, 105, 111, 110, 32, 39, 0,
    ],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((5 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__2_value:
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
        115, 99, 104, 101, 109, 97, 32, 118, 101, 114, 115, 105, 111, 110, 32, 39, 0,
    ],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__3_value:
    crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 50,
    m_capacity: 50,
    m_length: 49,
    m_data: [
        39, 32, 105, 115, 32, 111, 102, 32, 97, 32, 104, 105, 103, 104, 101, 114, 32, 109, 97, 106,
        111, 114, 32, 118, 101, 114, 115, 105, 111, 110, 32, 116, 104, 97, 110, 32, 116, 104, 105,
        115, 32, 76, 97, 107, 101, 39, 115, 32, 39, 0,
    ],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4_value:
    crate::leanh::LeanStringObject<48> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 48,
    m_capacity: 48,
    m_length: 47,
    m_data: [
        39, 59, 32, 121, 111, 117, 32, 109, 97, 121, 32, 110, 101, 101, 100, 32, 116, 111, 32, 117,
        112, 100, 97, 116, 101, 32, 121, 111, 117, 114, 32, 39, 108, 101, 97, 110, 45, 116, 111,
        111, 108, 99, 104, 97, 105, 110, 39, 0,
    ],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__5_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 118, 101, 114, 115, 105, 111, 110, 32, 39, 0,
    ],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        115, 99, 104, 101, 109, 97, 86, 101, 114, 115, 105, 111, 110, 0,
    ],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__8_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 58,
        32, 115, 99, 104, 101, 109, 97, 86, 101, 114, 115, 105, 111, 110, 0,
    ],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__9_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__8_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1___closed__0_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__0_value:
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
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__1_value:
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
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__1_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((7 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__4_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_Manifest_version___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__5_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [112, 97, 99, 107, 97, 103, 101, 115, 58, 32, 0],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_Manifest_fromJson_x3f___closed__0_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [112, 97, 99, 107, 97, 103, 101, 115, 68, 105, 114, 58, 32, 0],
    };
static mut l_Lake_Manifest_fromJson_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_fromJson_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Manifest_fromJson_x3f___closed__1_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [108, 97, 107, 101, 68, 105, 114, 58, 32, 0],
    };
static mut l_Lake_Manifest_fromJson_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_fromJson_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Manifest_fromJson_x3f___closed__2_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
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
            102, 105, 120, 101, 100, 84, 111, 111, 108, 99, 104, 97, 105, 110, 58, 32, 0,
        ],
    };
static mut l_Lake_Manifest_fromJson_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_fromJson_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Manifest_instFromJson___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Manifest_fromJson_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Manifest_instFromJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_instFromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Manifest_instFromJson: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_instFromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Manifest_parse___closed__0_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 74, 83, 79, 78, 58, 32, 0,
        ],
    };
static mut l_Lake_Manifest_parse___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_parse___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Manifest_load___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_Manifest_load___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_load___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_Manifest_saveEntries___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Manifest_saveEntries___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorIdx(
    mut v_x_2328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2328_) == 0 {
        let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2329_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2329_;
    } else {
        let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2330_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_2330_;
    }
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorIdx___boxed(
    mut v_x_2331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2332_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorIdx(v_x_2331_);
    crate::leanh::lean_dec_ref(v_x_2331_);
    return v_res_2332_;
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(
    mut v_t_2333_: *mut crate::leanh::LeanObject,
    mut v_k_2334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_2333_) == 0 {
        let mut v_name_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_opts_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_inherited_2337_: u8 = 0;
        let mut v_dir_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_name_2335_ = crate::leanh::lean_ctor_get(v_t_2333_, 0);
        crate::leanh::lean_inc(v_name_2335_);
        v_opts_2336_ = crate::leanh::lean_ctor_get(v_t_2333_, 1);
        crate::leanh::lean_inc(v_opts_2336_);
        v_inherited_2337_ = crate::leanh::lean_ctor_get_uint8(
            v_t_2333_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        );
        v_dir_2338_ = crate::leanh::lean_ctor_get(v_t_2333_, 2);
        crate::leanh::lean_inc_ref(v_dir_2338_);
        crate::leanh::lean_dec_ref_known(v_t_2333_, 3);
        v___x_2339_ = crate::leanh::lean_box((v_inherited_2337_) as usize);
        v___x_2340_ = crate::leanh::lean_apply_4(
            v_k_2334_,
            v_name_2335_,
            v_opts_2336_,
            v___x_2339_,
            v_dir_2338_,
        );
        return v___x_2340_;
    } else {
        let mut v_name_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_opts_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_inherited_2343_: u8 = 0;
        let mut v_url_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rev_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_inputRev_x3f_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_subDir_x3f_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_name_2341_ = crate::leanh::lean_ctor_get(v_t_2333_, 0);
        crate::leanh::lean_inc(v_name_2341_);
        v_opts_2342_ = crate::leanh::lean_ctor_get(v_t_2333_, 1);
        crate::leanh::lean_inc(v_opts_2342_);
        v_inherited_2343_ = crate::leanh::lean_ctor_get_uint8(
            v_t_2333_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
        );
        v_url_2344_ = crate::leanh::lean_ctor_get(v_t_2333_, 2);
        crate::leanh::lean_inc_ref(v_url_2344_);
        v_rev_2345_ = crate::leanh::lean_ctor_get(v_t_2333_, 3);
        crate::leanh::lean_inc_ref(v_rev_2345_);
        v_inputRev_x3f_2346_ = crate::leanh::lean_ctor_get(v_t_2333_, 4);
        crate::leanh::lean_inc(v_inputRev_x3f_2346_);
        v_subDir_x3f_2347_ = crate::leanh::lean_ctor_get(v_t_2333_, 5);
        crate::leanh::lean_inc(v_subDir_x3f_2347_);
        crate::leanh::lean_dec_ref_known(v_t_2333_, 6);
        v___x_2348_ = crate::leanh::lean_box((v_inherited_2343_) as usize);
        v___x_2349_ = crate::leanh::lean_apply_7(
            v_k_2334_,
            v_name_2341_,
            v_opts_2342_,
            v___x_2348_,
            v_url_2344_,
            v_rev_2345_,
            v_inputRev_x3f_2346_,
            v_subDir_x3f_2347_,
        );
        return v___x_2349_;
    }
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim(
    mut v_motive_2350_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2351_: *mut crate::leanh::LeanObject,
    mut v_t_2352_: *mut crate::leanh::LeanObject,
    mut v_h_2353_: *mut crate::leanh::LeanObject,
    mut v_k_2354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2355_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(
        v_t_2352_, v_k_2354_,
    );
    return v___x_2355_;
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___boxed(
    mut v_motive_2356_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2357_: *mut crate::leanh::LeanObject,
    mut v_t_2358_: *mut crate::leanh::LeanObject,
    mut v_h_2359_: *mut crate::leanh::LeanObject,
    mut v_k_2360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2361_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim(
        v_motive_2356_,
        v_ctorIdx_2357_,
        v_t_2358_,
        v_h_2359_,
        v_k_2360_,
    );
    crate::leanh::lean_dec(v_ctorIdx_2357_);
    return v_res_2361_;
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_path_elim___redArg(
    mut v_t_2362_: *mut crate::leanh::LeanObject,
    mut v_path_2363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2364_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(
        v_t_2362_,
        v_path_2363_,
    );
    return v___x_2364_;
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_path_elim(
    mut v_motive_2365_: *mut crate::leanh::LeanObject,
    mut v_t_2366_: *mut crate::leanh::LeanObject,
    mut v_h_2367_: *mut crate::leanh::LeanObject,
    mut v_path_2368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2369_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(
        v_t_2366_,
        v_path_2368_,
    );
    return v___x_2369_;
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_git_elim___redArg(
    mut v_t_2370_: *mut crate::leanh::LeanObject,
    mut v_git_2371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2372_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(
        v_t_2370_,
        v_git_2371_,
    );
    return v___x_2372_;
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_git_elim(
    mut v_motive_2373_: *mut crate::leanh::LeanObject,
    mut v_t_2374_: *mut crate::leanh::LeanObject,
    mut v_h_2375_: *mut crate::leanh::LeanObject,
    mut v_git_2376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2377_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(
        v_t_2374_,
        v_git_2376_,
    );
    return v___x_2377_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(
    mut v_x_2380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2386_: u8 = 0;
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2390_: u8 = 0;
    let mut v_a_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2394_: u8 = 0;
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2399_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2380_) == 0 {
                    v___x_2381_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0;
                    return v___x_2381_;
                } else {
                    v___x_2382_ = l_Lean_Json_getStr_x3f(v_x_2380_);
                    if crate::leanh::lean_obj_tag(v___x_2382_) == 0 {
                        v_a_2383_ = crate::leanh::lean_ctor_get(v___x_2382_, 0);
                        v_isSharedCheck_2390_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2382_)) as u8;
                        if v_isSharedCheck_2390_ == 0 {
                            v___x_2385_ = v___x_2382_;
                            v_isShared_2386_ = v_isSharedCheck_2390_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2383_);
                            crate::leanh::lean_dec(v___x_2382_);
                            v___x_2385_ = crate::leanh::lean_box(0);
                            v_isShared_2386_ = v_isSharedCheck_2390_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2391_ = crate::leanh::lean_ctor_get(v___x_2382_, 0);
                        v_isSharedCheck_2399_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2382_)) as u8;
                        if v_isSharedCheck_2399_ == 0 {
                            v___x_2393_ = v___x_2382_;
                            v_isShared_2394_ = v_isSharedCheck_2399_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2391_);
                            crate::leanh::lean_dec(v___x_2382_);
                            v___x_2393_ = crate::leanh::lean_box(0);
                            v_isShared_2394_ = v_isSharedCheck_2399_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2386_ == 0 {
                    v___x_2388_ = v___x_2385_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2389_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2383_);
                    v___x_2388_ = v_reuseFailAlloc_2389_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2388_;
            }
            3 => {
                v___x_2395_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2395_, 0, v_a_2391_);
                if v_isShared_2394_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2393_, 0, v___x_2395_);
                    v___x_2397_ = v___x_2393_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2398_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2395_);
                    v___x_2397_ = v_reuseFailAlloc_2398_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2397_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(
    mut v_x_2400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2406_: u8 = 0;
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2410_: u8 = 0;
    let mut v_a_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2414_: u8 = 0;
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2419_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2400_) == 0 {
                    v___x_2401_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0;
                    return v___x_2401_;
                } else {
                    v___x_2402_ = l_Lean_Json_getStr_x3f(v_x_2400_);
                    if crate::leanh::lean_obj_tag(v___x_2402_) == 0 {
                        v_a_2403_ = crate::leanh::lean_ctor_get(v___x_2402_, 0);
                        v_isSharedCheck_2410_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2402_)) as u8;
                        if v_isSharedCheck_2410_ == 0 {
                            v___x_2405_ = v___x_2402_;
                            v_isShared_2406_ = v_isSharedCheck_2410_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2403_);
                            crate::leanh::lean_dec(v___x_2402_);
                            v___x_2405_ = crate::leanh::lean_box(0);
                            v_isShared_2406_ = v_isSharedCheck_2410_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2411_ = crate::leanh::lean_ctor_get(v___x_2402_, 0);
                        v_isSharedCheck_2419_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2402_)) as u8;
                        if v_isSharedCheck_2419_ == 0 {
                            v___x_2413_ = v___x_2402_;
                            v_isShared_2414_ = v_isSharedCheck_2419_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2411_);
                            crate::leanh::lean_dec(v___x_2402_);
                            v___x_2413_ = crate::leanh::lean_box(0);
                            v_isShared_2414_ = v_isSharedCheck_2419_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2406_ == 0 {
                    v___x_2408_ = v___x_2405_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2409_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_a_2403_);
                    v___x_2408_ = v_reuseFailAlloc_2409_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2408_;
            }
            3 => {
                v___x_2415_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2415_, 0, v_a_2411_);
                if v_isShared_2414_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2413_, 0, v___x_2415_);
                    v___x_2417_ = v___x_2413_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2418_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2415_);
                    v___x_2417_ = v_reuseFailAlloc_2418_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2417_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0(
    mut v_init_2423_: *mut crate::leanh::LeanObject,
    mut v_x_2424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2433_: u8 = 0;
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: u8 = 0;
    let mut v_n_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: u8 = 0;
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2442_: u8 = 0;
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2446_: u8 = 0;
    let mut v_a_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2461_: u8 = 0;
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2465_: u8 = 0;
    let mut v_a_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2470_: u8 = 0;
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2424_) == 0 {
                    v_k_2425_ = crate::leanh::lean_ctor_get(v_x_2424_, 1);
                    crate::leanh::lean_inc(v_k_2425_);
                    v_v_2426_ = crate::leanh::lean_ctor_get(v_x_2424_, 2);
                    crate::leanh::lean_inc(v_v_2426_);
                    v_l_2427_ = crate::leanh::lean_ctor_get(v_x_2424_, 3);
                    crate::leanh::lean_inc(v_l_2427_);
                    v_r_2428_ = crate::leanh::lean_ctor_get(v_x_2424_, 4);
                    crate::leanh::lean_inc(v_r_2428_);
                    crate::leanh::lean_dec_ref_known(v_x_2424_, 5);
                    v___x_2429_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0(v_init_2423_, v_l_2427_);
                    if crate::leanh::lean_obj_tag(v___x_2429_) == 0 {
                        crate::leanh::lean_dec(v_r_2428_);
                        crate::leanh::lean_dec(v_v_2426_);
                        crate::leanh::lean_dec(v_k_2425_);
                        return v___x_2429_;
                    } else {
                        v_a_2430_ = crate::leanh::lean_ctor_get(v___x_2429_, 0);
                        v_isSharedCheck_2470_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2429_)) as u8;
                        if v_isSharedCheck_2470_ == 0 {
                            v___x_2432_ = v___x_2429_;
                            v_isShared_2433_ = v_isSharedCheck_2470_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2430_);
                            crate::leanh::lean_dec(v___x_2429_);
                            v___x_2432_ = crate::leanh::lean_box(0);
                            v_isShared_2433_ = v_isSharedCheck_2470_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_2471_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2471_, 0, v_init_2423_);
                    return v___x_2471_;
                }
            }
            1 => {
                v___x_2434_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__0;
                v___x_2435_ = lean_string_dec_eq(v_k_2425_, v___x_2434_);
                if v___x_2435_ == 0 {
                    crate::leanh::lean_inc(v_k_2425_);
                    v_n_2436_ = l_String_toName(v_k_2425_);
                    v___x_2437_ = l_Lean_Name_isAnonymous(v_n_2436_);
                    if v___x_2437_ == 0 {
                        crate::leanh::lean_del_object(v___x_2432_);
                        crate::leanh::lean_dec(v_k_2425_);
                        v___x_2438_ = l_Lean_Json_getStr_x3f(v_v_2426_);
                        if crate::leanh::lean_obj_tag(v___x_2438_) == 0 {
                            crate::leanh::lean_dec(v_n_2436_);
                            crate::leanh::lean_dec(v_a_2430_);
                            crate::leanh::lean_dec(v_r_2428_);
                            v_a_2439_ = crate::leanh::lean_ctor_get(v___x_2438_, 0);
                            v_isSharedCheck_2446_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2438_)) as u8;
                            if v_isSharedCheck_2446_ == 0 {
                                v___x_2441_ = v___x_2438_;
                                v_isShared_2442_ = v_isSharedCheck_2446_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2439_);
                                crate::leanh::lean_dec(v___x_2438_);
                                v___x_2441_ = crate::leanh::lean_box(0);
                                v_isShared_2442_ = v_isSharedCheck_2446_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_a_2447_ = crate::leanh::lean_ctor_get(v___x_2438_, 0);
                            crate::leanh::lean_inc(v_a_2447_);
                            crate::leanh::lean_dec_ref_known(v___x_2438_, 1);
                            v___x_2448_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_2436_, v_a_2447_, v_a_2430_);
                            v_init_2423_ = v___x_2448_;
                            v_x_2424_ = v_r_2428_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_n_2436_);
                        crate::leanh::lean_dec(v_a_2430_);
                        crate::leanh::lean_dec(v_r_2428_);
                        crate::leanh::lean_dec(v_v_2426_);
                        v___x_2450_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__1;
                        v___x_2451_ = lean_string_append(v___x_2450_, v_k_2425_);
                        crate::leanh::lean_dec(v_k_2425_);
                        v___x_2452_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2;
                        v___x_2453_ = lean_string_append(v___x_2451_, v___x_2452_);
                        if v_isShared_2433_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_2432_, 0);
                            crate::leanh::lean_ctor_set(v___x_2432_, 0, v___x_2453_);
                            v___x_2455_ = v___x_2432_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2456_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2453_);
                            v___x_2455_ = v_reuseFailAlloc_2456_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2432_);
                    crate::leanh::lean_dec(v_k_2425_);
                    v___x_2457_ = l_Lean_Json_getStr_x3f(v_v_2426_);
                    if crate::leanh::lean_obj_tag(v___x_2457_) == 0 {
                        crate::leanh::lean_dec(v_a_2430_);
                        crate::leanh::lean_dec(v_r_2428_);
                        v_a_2458_ = crate::leanh::lean_ctor_get(v___x_2457_, 0);
                        v_isSharedCheck_2465_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2457_)) as u8;
                        if v_isSharedCheck_2465_ == 0 {
                            v___x_2460_ = v___x_2457_;
                            v_isShared_2461_ = v_isSharedCheck_2465_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2458_);
                            crate::leanh::lean_dec(v___x_2457_);
                            v___x_2460_ = crate::leanh::lean_box(0);
                            v_isShared_2461_ = v_isSharedCheck_2465_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_2466_ = crate::leanh::lean_ctor_get(v___x_2457_, 0);
                        crate::leanh::lean_inc(v_a_2466_);
                        crate::leanh::lean_dec_ref_known(v___x_2457_, 1);
                        v___x_2467_ = crate::leanh::lean_box(0);
                        v___x_2468_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2467_, v_a_2466_, v_a_2430_);
                        v_init_2423_ = v___x_2468_;
                        v_x_2424_ = v_r_2428_;
                        state = 0;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2442_ == 0 {
                    v___x_2444_ = v___x_2441_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2445_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2439_);
                    v___x_2444_ = v_reuseFailAlloc_2445_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2444_;
            }
            4 => {
                return v___x_2455_;
            }
            5 => {
                if v_isShared_2461_ == 0 {
                    v___x_2463_ = v___x_2460_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2464_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
                    v___x_2463_ = v_reuseFailAlloc_2464_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2463_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0(
    mut v_x_2473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2473_) == 5 {
        let mut v_kvPairs_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_kvPairs_2474_ = crate::leanh::lean_ctor_get(v_x_2473_, 0);
        crate::leanh::lean_inc(v_kvPairs_2474_);
        crate::leanh::lean_dec_ref_known(v_x_2473_, 1);
        v___x_2475_ = crate::leanh::lean_box(1);
        v___x_2476_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0(v___x_2475_, v_kvPairs_2474_);
        return v___x_2476_;
    } else {
        let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2477_ = l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0___closed__0;
        v___x_2478_ = crate::leanh::lean_unsigned_to_nat(80);
        v___x_2479_ = l_Lean_Json_pretty(v_x_2473_, v___x_2478_);
        v___x_2480_ = lean_string_append(v___x_2477_, v___x_2479_);
        crate::leanh::lean_dec_ref(v___x_2479_);
        v___x_2481_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2;
        v___x_2482_ = lean_string_append(v___x_2480_, v___x_2481_);
        v___x_2483_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2483_, 0, v___x_2482_);
        return v___x_2483_;
    }
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson(
    mut v_json_2546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: u8 = 0;
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: u8 = 0;
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2562_: u8 = 0;
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2566_: u8 = 0;
    let mut v_a_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2574_: u8 = 0;
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2578_: u8 = 0;
    let mut v_a_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2586_: u8 = 0;
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2590_: u8 = 0;
    let mut v_a_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2598_: u8 = 0;
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2602_: u8 = 0;
    let mut v_a_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2610_: u8 = 0;
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2614_: u8 = 0;
    let mut v_a_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2622_: u8 = 0;
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2626_: u8 = 0;
    let mut v_a_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2634_: u8 = 0;
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2638_: u8 = 0;
    let mut v_a_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2646_: u8 = 0;
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2650_: u8 = 0;
    let mut v_a_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2654_: u8 = 0;
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: u8 = 0;
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2660_: u8 = 0;
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2667_: u8 = 0;
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2671_: u8 = 0;
    let mut v_a_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2679_: u8 = 0;
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2683_: u8 = 0;
    let mut v_a_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2691_: u8 = 0;
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2695_: u8 = 0;
    let mut v_a_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2703_: u8 = 0;
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2707_: u8 = 0;
    let mut v_a_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2715_: u8 = 0;
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2719_: u8 = 0;
    let mut v_a_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2723_: u8 = 0;
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: u8 = 0;
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2729_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_json_2546_);
                v___x_2547_ = l_Lean_Json_getTag_x3f(v_json_2546_);
                if crate::leanh::lean_obj_tag(v___x_2547_) == 0 {
                    crate::leanh::lean_dec(v_json_2546_);
                    v___x_2548_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__1;
                    return v___x_2548_;
                } else {
                    v_val_2549_ = crate::leanh::lean_ctor_get(v___x_2547_, 0);
                    crate::leanh::lean_inc(v_val_2549_);
                    crate::leanh::lean_dec_ref_known(v___x_2547_, 1);
                    v___x_2550_ = crate::leanh::lean_box(0);
                    v___x_2551_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2;
                    v___x_2552_ = lean_string_dec_eq(v_val_2549_, v___x_2551_);
                    if v___x_2552_ == 0 {
                        v___x_2553_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3;
                        v___x_2554_ = lean_string_dec_eq(v_val_2549_, v___x_2553_);
                        crate::leanh::lean_dec(v_val_2549_);
                        if v___x_2554_ == 0 {
                            crate::leanh::lean_dec(v_json_2546_);
                            v___x_2555_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__5;
                            return v___x_2555_;
                        } else {
                            v___x_2556_ = crate::leanh::lean_unsigned_to_nat(7);
                            v___x_2557_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__21;
                            v___x_2558_ = l_Lean_Json_parseCtorFields(
                                v_json_2546_,
                                v___x_2553_,
                                v___x_2556_,
                                v___x_2557_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2558_) == 0 {
                                v_a_2559_ = crate::leanh::lean_ctor_get(v___x_2558_, 0);
                                v_isSharedCheck_2566_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2558_)) as u8;
                                if v_isSharedCheck_2566_ == 0 {
                                    v___x_2561_ = v___x_2558_;
                                    v_isShared_2562_ = v_isSharedCheck_2566_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2559_);
                                    crate::leanh::lean_dec(v___x_2558_);
                                    v___x_2561_ = crate::leanh::lean_box(0);
                                    v_isShared_2562_ = v_isSharedCheck_2566_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_2567_ = crate::leanh::lean_ctor_get(v___x_2558_, 0);
                                crate::leanh::lean_inc(v_a_2567_);
                                crate::leanh::lean_dec_ref_known(v___x_2558_, 1);
                                v___x_2568_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_2569_ =
                                    lean_array_get_borrowed(v___x_2550_, v_a_2567_, v___x_2568_);
                                crate::leanh::lean_inc(v___x_2569_);
                                v___x_2570_ = l_Lean_Name_fromJson_x3f(v___x_2569_);
                                if crate::leanh::lean_obj_tag(v___x_2570_) == 0 {
                                    crate::leanh::lean_dec(v_a_2567_);
                                    v_a_2571_ = crate::leanh::lean_ctor_get(v___x_2570_, 0);
                                    v_isSharedCheck_2578_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2570_)) as u8;
                                    if v_isSharedCheck_2578_ == 0 {
                                        v___x_2573_ = v___x_2570_;
                                        v_isShared_2574_ = v_isSharedCheck_2578_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2571_);
                                        crate::leanh::lean_dec(v___x_2570_);
                                        v___x_2573_ = crate::leanh::lean_box(0);
                                        v_isShared_2574_ = v_isSharedCheck_2578_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    v_a_2579_ = crate::leanh::lean_ctor_get(v___x_2570_, 0);
                                    crate::leanh::lean_inc(v_a_2579_);
                                    crate::leanh::lean_dec_ref_known(v___x_2570_, 1);
                                    v___x_2580_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_2581_ = lean_array_get_borrowed(
                                        v___x_2550_,
                                        v_a_2567_,
                                        v___x_2580_,
                                    );
                                    crate::leanh::lean_inc(v___x_2581_);
                                    v___x_2582_ = l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0(v___x_2581_);
                                    if crate::leanh::lean_obj_tag(v___x_2582_) == 0 {
                                        crate::leanh::lean_dec(v_a_2579_);
                                        crate::leanh::lean_dec(v_a_2567_);
                                        v_a_2583_ = crate::leanh::lean_ctor_get(v___x_2582_, 0);
                                        v_isSharedCheck_2590_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2582_)) as u8;
                                        if v_isSharedCheck_2590_ == 0 {
                                            v___x_2585_ = v___x_2582_;
                                            v_isShared_2586_ = v_isSharedCheck_2590_;
                                            state = 5;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2583_);
                                            crate::leanh::lean_dec(v___x_2582_);
                                            v___x_2585_ = crate::leanh::lean_box(0);
                                            v_isShared_2586_ = v_isSharedCheck_2590_;
                                            state = 5;
                                            continue;
                                        }
                                    } else {
                                        v_a_2591_ = crate::leanh::lean_ctor_get(v___x_2582_, 0);
                                        crate::leanh::lean_inc(v_a_2591_);
                                        crate::leanh::lean_dec_ref_known(v___x_2582_, 1);
                                        v___x_2592_ = crate::leanh::lean_unsigned_to_nat(2);
                                        v___x_2593_ = lean_array_get_borrowed(
                                            v___x_2550_,
                                            v_a_2567_,
                                            v___x_2592_,
                                        );
                                        v___x_2594_ = l_Lean_Json_getBool_x3f(v___x_2593_);
                                        if crate::leanh::lean_obj_tag(v___x_2594_) == 0 {
                                            crate::leanh::lean_dec(v_a_2591_);
                                            crate::leanh::lean_dec(v_a_2579_);
                                            crate::leanh::lean_dec(v_a_2567_);
                                            v_a_2595_ = crate::leanh::lean_ctor_get(v___x_2594_, 0);
                                            v_isSharedCheck_2602_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2594_))
                                                    as u8;
                                            if v_isSharedCheck_2602_ == 0 {
                                                v___x_2597_ = v___x_2594_;
                                                v_isShared_2598_ = v_isSharedCheck_2602_;
                                                state = 7;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2595_);
                                                crate::leanh::lean_dec(v___x_2594_);
                                                v___x_2597_ = crate::leanh::lean_box(0);
                                                v_isShared_2598_ = v_isSharedCheck_2602_;
                                                state = 7;
                                                continue;
                                            }
                                        } else {
                                            v_a_2603_ = crate::leanh::lean_ctor_get(v___x_2594_, 0);
                                            crate::leanh::lean_inc(v_a_2603_);
                                            crate::leanh::lean_dec_ref_known(v___x_2594_, 1);
                                            v___x_2604_ = crate::leanh::lean_unsigned_to_nat(3);
                                            v___x_2605_ = lean_array_get_borrowed(
                                                v___x_2550_,
                                                v_a_2567_,
                                                v___x_2604_,
                                            );
                                            crate::leanh::lean_inc(v___x_2605_);
                                            v___x_2606_ = l_Lean_Json_getStr_x3f(v___x_2605_);
                                            if crate::leanh::lean_obj_tag(v___x_2606_) == 0 {
                                                crate::leanh::lean_dec(v_a_2603_);
                                                crate::leanh::lean_dec(v_a_2591_);
                                                crate::leanh::lean_dec(v_a_2579_);
                                                crate::leanh::lean_dec(v_a_2567_);
                                                v_a_2607_ =
                                                    crate::leanh::lean_ctor_get(v___x_2606_, 0);
                                                v_isSharedCheck_2614_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2606_))
                                                        as u8;
                                                if v_isSharedCheck_2614_ == 0 {
                                                    v___x_2609_ = v___x_2606_;
                                                    v_isShared_2610_ = v_isSharedCheck_2614_;
                                                    state = 9;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_2607_);
                                                    crate::leanh::lean_dec(v___x_2606_);
                                                    v___x_2609_ = crate::leanh::lean_box(0);
                                                    v_isShared_2610_ = v_isSharedCheck_2614_;
                                                    state = 9;
                                                    continue;
                                                }
                                            } else {
                                                v_a_2615_ =
                                                    crate::leanh::lean_ctor_get(v___x_2606_, 0);
                                                crate::leanh::lean_inc(v_a_2615_);
                                                crate::leanh::lean_dec_ref_known(v___x_2606_, 1);
                                                v___x_2616_ = crate::leanh::lean_unsigned_to_nat(4);
                                                v___x_2617_ = lean_array_get_borrowed(
                                                    v___x_2550_,
                                                    v_a_2567_,
                                                    v___x_2616_,
                                                );
                                                crate::leanh::lean_inc(v___x_2617_);
                                                v___x_2618_ = l_Lean_Json_getStr_x3f(v___x_2617_);
                                                if crate::leanh::lean_obj_tag(v___x_2618_) == 0 {
                                                    crate::leanh::lean_dec(v_a_2615_);
                                                    crate::leanh::lean_dec(v_a_2603_);
                                                    crate::leanh::lean_dec(v_a_2591_);
                                                    crate::leanh::lean_dec(v_a_2579_);
                                                    crate::leanh::lean_dec(v_a_2567_);
                                                    v_a_2619_ =
                                                        crate::leanh::lean_ctor_get(v___x_2618_, 0);
                                                    v_isSharedCheck_2626_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_2618_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_2626_ == 0 {
                                                        v___x_2621_ = v___x_2618_;
                                                        v_isShared_2622_ = v_isSharedCheck_2626_;
                                                        state = 11;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_2619_);
                                                        crate::leanh::lean_dec(v___x_2618_);
                                                        v___x_2621_ = crate::leanh::lean_box(0);
                                                        v_isShared_2622_ = v_isSharedCheck_2626_;
                                                        state = 11;
                                                        continue;
                                                    }
                                                } else {
                                                    v_a_2627_ =
                                                        crate::leanh::lean_ctor_get(v___x_2618_, 0);
                                                    crate::leanh::lean_inc(v_a_2627_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_2618_,
                                                        1,
                                                    );
                                                    v___x_2628_ =
                                                        crate::leanh::lean_unsigned_to_nat(5);
                                                    v___x_2629_ = lean_array_get_borrowed(
                                                        v___x_2550_,
                                                        v_a_2567_,
                                                        v___x_2628_,
                                                    );
                                                    crate::leanh::lean_inc(v___x_2629_);
                                                    v___x_2630_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(v___x_2629_);
                                                    if crate::leanh::lean_obj_tag(v___x_2630_) == 0
                                                    {
                                                        crate::leanh::lean_dec(v_a_2627_);
                                                        crate::leanh::lean_dec(v_a_2615_);
                                                        crate::leanh::lean_dec(v_a_2603_);
                                                        crate::leanh::lean_dec(v_a_2591_);
                                                        crate::leanh::lean_dec(v_a_2579_);
                                                        crate::leanh::lean_dec(v_a_2567_);
                                                        v_a_2631_ = crate::leanh::lean_ctor_get(
                                                            v___x_2630_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_2638_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_2630_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_2638_ == 0 {
                                                            v___x_2633_ = v___x_2630_;
                                                            v_isShared_2634_ =
                                                                v_isSharedCheck_2638_;
                                                            state = 13;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_2631_);
                                                            crate::leanh::lean_dec(v___x_2630_);
                                                            v___x_2633_ = crate::leanh::lean_box(0);
                                                            v_isShared_2634_ =
                                                                v_isSharedCheck_2638_;
                                                            state = 13;
                                                            continue;
                                                        }
                                                    } else {
                                                        v_a_2639_ = crate::leanh::lean_ctor_get(
                                                            v___x_2630_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_2639_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_2630_,
                                                            1,
                                                        );
                                                        v___x_2640_ =
                                                            crate::leanh::lean_unsigned_to_nat(6);
                                                        v___x_2641_ = lean_array_get(
                                                            v___x_2550_,
                                                            v_a_2567_,
                                                            v___x_2640_,
                                                        );
                                                        crate::leanh::lean_dec(v_a_2567_);
                                                        v___x_2642_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v___x_2641_);
                                                        if crate::leanh::lean_obj_tag(v___x_2642_)
                                                            == 0
                                                        {
                                                            crate::leanh::lean_dec(v_a_2639_);
                                                            crate::leanh::lean_dec(v_a_2627_);
                                                            crate::leanh::lean_dec(v_a_2615_);
                                                            crate::leanh::lean_dec(v_a_2603_);
                                                            crate::leanh::lean_dec(v_a_2591_);
                                                            crate::leanh::lean_dec(v_a_2579_);
                                                            v_a_2643_ = crate::leanh::lean_ctor_get(
                                                                v___x_2642_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_2650_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_2642_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_2650_ == 0 {
                                                                v___x_2645_ = v___x_2642_;
                                                                v_isShared_2646_ =
                                                                    v_isSharedCheck_2650_;
                                                                state = 15;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_2643_);
                                                                crate::leanh::lean_dec(v___x_2642_);
                                                                v___x_2645_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_2646_ =
                                                                    v_isSharedCheck_2650_;
                                                                state = 15;
                                                                continue;
                                                            }
                                                        } else {
                                                            v_a_2651_ = crate::leanh::lean_ctor_get(
                                                                v___x_2642_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_2660_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_2642_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_2660_ == 0 {
                                                                v___x_2653_ = v___x_2642_;
                                                                v_isShared_2654_ =
                                                                    v_isSharedCheck_2660_;
                                                                state = 17;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_2651_);
                                                                crate::leanh::lean_dec(v___x_2642_);
                                                                v___x_2653_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_2654_ =
                                                                    v_isSharedCheck_2660_;
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
                    } else {
                        crate::leanh::lean_dec(v_val_2549_);
                        v___x_2661_ = crate::leanh::lean_unsigned_to_nat(4);
                        v___x_2662_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__25;
                        v___x_2663_ = l_Lean_Json_parseCtorFields(
                            v_json_2546_,
                            v___x_2551_,
                            v___x_2661_,
                            v___x_2662_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2663_) == 0 {
                            v_a_2664_ = crate::leanh::lean_ctor_get(v___x_2663_, 0);
                            v_isSharedCheck_2671_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2663_)) as u8;
                            if v_isSharedCheck_2671_ == 0 {
                                v___x_2666_ = v___x_2663_;
                                v_isShared_2667_ = v_isSharedCheck_2671_;
                                state = 19;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2664_);
                                crate::leanh::lean_dec(v___x_2663_);
                                v___x_2666_ = crate::leanh::lean_box(0);
                                v_isShared_2667_ = v_isSharedCheck_2671_;
                                state = 19;
                                continue;
                            }
                        } else {
                            v_a_2672_ = crate::leanh::lean_ctor_get(v___x_2663_, 0);
                            crate::leanh::lean_inc(v_a_2672_);
                            crate::leanh::lean_dec_ref_known(v___x_2663_, 1);
                            v___x_2673_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_2674_ =
                                lean_array_get_borrowed(v___x_2550_, v_a_2672_, v___x_2673_);
                            crate::leanh::lean_inc(v___x_2674_);
                            v___x_2675_ = l_Lean_Name_fromJson_x3f(v___x_2674_);
                            if crate::leanh::lean_obj_tag(v___x_2675_) == 0 {
                                crate::leanh::lean_dec(v_a_2672_);
                                v_a_2676_ = crate::leanh::lean_ctor_get(v___x_2675_, 0);
                                v_isSharedCheck_2683_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2675_)) as u8;
                                if v_isSharedCheck_2683_ == 0 {
                                    v___x_2678_ = v___x_2675_;
                                    v_isShared_2679_ = v_isSharedCheck_2683_;
                                    state = 21;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2676_);
                                    crate::leanh::lean_dec(v___x_2675_);
                                    v___x_2678_ = crate::leanh::lean_box(0);
                                    v_isShared_2679_ = v_isSharedCheck_2683_;
                                    state = 21;
                                    continue;
                                }
                            } else {
                                v_a_2684_ = crate::leanh::lean_ctor_get(v___x_2675_, 0);
                                crate::leanh::lean_inc(v_a_2684_);
                                crate::leanh::lean_dec_ref_known(v___x_2675_, 1);
                                v___x_2685_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_2686_ =
                                    lean_array_get_borrowed(v___x_2550_, v_a_2672_, v___x_2685_);
                                crate::leanh::lean_inc(v___x_2686_);
                                v___x_2687_ = l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0(v___x_2686_);
                                if crate::leanh::lean_obj_tag(v___x_2687_) == 0 {
                                    crate::leanh::lean_dec(v_a_2684_);
                                    crate::leanh::lean_dec(v_a_2672_);
                                    v_a_2688_ = crate::leanh::lean_ctor_get(v___x_2687_, 0);
                                    v_isSharedCheck_2695_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2687_)) as u8;
                                    if v_isSharedCheck_2695_ == 0 {
                                        v___x_2690_ = v___x_2687_;
                                        v_isShared_2691_ = v_isSharedCheck_2695_;
                                        state = 23;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2688_);
                                        crate::leanh::lean_dec(v___x_2687_);
                                        v___x_2690_ = crate::leanh::lean_box(0);
                                        v_isShared_2691_ = v_isSharedCheck_2695_;
                                        state = 23;
                                        continue;
                                    }
                                } else {
                                    v_a_2696_ = crate::leanh::lean_ctor_get(v___x_2687_, 0);
                                    crate::leanh::lean_inc(v_a_2696_);
                                    crate::leanh::lean_dec_ref_known(v___x_2687_, 1);
                                    v___x_2697_ = crate::leanh::lean_unsigned_to_nat(2);
                                    v___x_2698_ = lean_array_get_borrowed(
                                        v___x_2550_,
                                        v_a_2672_,
                                        v___x_2697_,
                                    );
                                    v___x_2699_ = l_Lean_Json_getBool_x3f(v___x_2698_);
                                    if crate::leanh::lean_obj_tag(v___x_2699_) == 0 {
                                        crate::leanh::lean_dec(v_a_2696_);
                                        crate::leanh::lean_dec(v_a_2684_);
                                        crate::leanh::lean_dec(v_a_2672_);
                                        v_a_2700_ = crate::leanh::lean_ctor_get(v___x_2699_, 0);
                                        v_isSharedCheck_2707_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2699_)) as u8;
                                        if v_isSharedCheck_2707_ == 0 {
                                            v___x_2702_ = v___x_2699_;
                                            v_isShared_2703_ = v_isSharedCheck_2707_;
                                            state = 25;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2700_);
                                            crate::leanh::lean_dec(v___x_2699_);
                                            v___x_2702_ = crate::leanh::lean_box(0);
                                            v_isShared_2703_ = v_isSharedCheck_2707_;
                                            state = 25;
                                            continue;
                                        }
                                    } else {
                                        v_a_2708_ = crate::leanh::lean_ctor_get(v___x_2699_, 0);
                                        crate::leanh::lean_inc(v_a_2708_);
                                        crate::leanh::lean_dec_ref_known(v___x_2699_, 1);
                                        v___x_2709_ = crate::leanh::lean_unsigned_to_nat(3);
                                        v___x_2710_ =
                                            lean_array_get(v___x_2550_, v_a_2672_, v___x_2709_);
                                        crate::leanh::lean_dec(v_a_2672_);
                                        v___x_2711_ = l_Lean_Json_getStr_x3f(v___x_2710_);
                                        if crate::leanh::lean_obj_tag(v___x_2711_) == 0 {
                                            crate::leanh::lean_dec(v_a_2708_);
                                            crate::leanh::lean_dec(v_a_2696_);
                                            crate::leanh::lean_dec(v_a_2684_);
                                            v_a_2712_ = crate::leanh::lean_ctor_get(v___x_2711_, 0);
                                            v_isSharedCheck_2719_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2711_))
                                                    as u8;
                                            if v_isSharedCheck_2719_ == 0 {
                                                v___x_2714_ = v___x_2711_;
                                                v_isShared_2715_ = v_isSharedCheck_2719_;
                                                state = 27;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2712_);
                                                crate::leanh::lean_dec(v___x_2711_);
                                                v___x_2714_ = crate::leanh::lean_box(0);
                                                v_isShared_2715_ = v_isSharedCheck_2719_;
                                                state = 27;
                                                continue;
                                            }
                                        } else {
                                            v_a_2720_ = crate::leanh::lean_ctor_get(v___x_2711_, 0);
                                            v_isSharedCheck_2729_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2711_))
                                                    as u8;
                                            if v_isSharedCheck_2729_ == 0 {
                                                v___x_2722_ = v___x_2711_;
                                                v_isShared_2723_ = v_isSharedCheck_2729_;
                                                state = 29;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2720_);
                                                crate::leanh::lean_dec(v___x_2711_);
                                                v___x_2722_ = crate::leanh::lean_box(0);
                                                v_isShared_2723_ = v_isSharedCheck_2729_;
                                                state = 29;
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
            1 => {
                if v_isShared_2562_ == 0 {
                    v___x_2564_ = v___x_2561_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2565_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
                    v___x_2564_ = v_reuseFailAlloc_2565_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2564_;
            }
            3 => {
                if v_isShared_2574_ == 0 {
                    v___x_2576_ = v___x_2573_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2577_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
                    v___x_2576_ = v_reuseFailAlloc_2577_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2576_;
            }
            5 => {
                if v_isShared_2586_ == 0 {
                    v___x_2588_ = v___x_2585_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2589_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
                    v___x_2588_ = v_reuseFailAlloc_2589_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2588_;
            }
            7 => {
                if v_isShared_2598_ == 0 {
                    v___x_2600_ = v___x_2597_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2601_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
                    v___x_2600_ = v_reuseFailAlloc_2601_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2600_;
            }
            9 => {
                if v_isShared_2610_ == 0 {
                    v___x_2612_ = v___x_2609_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2613_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
                    v___x_2612_ = v_reuseFailAlloc_2613_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2612_;
            }
            11 => {
                if v_isShared_2622_ == 0 {
                    v___x_2624_ = v___x_2621_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2625_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
                    v___x_2624_ = v_reuseFailAlloc_2625_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2624_;
            }
            13 => {
                if v_isShared_2634_ == 0 {
                    v___x_2636_ = v___x_2633_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2637_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
                    v___x_2636_ = v_reuseFailAlloc_2637_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2636_;
            }
            15 => {
                if v_isShared_2646_ == 0 {
                    v___x_2648_ = v___x_2645_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2649_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
                    v___x_2648_ = v_reuseFailAlloc_2649_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2648_;
            }
            17 => {
                v___x_2655_ = crate::leanh::lean_alloc_ctor(1, 6, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2655_, 0, v_a_2579_);
                crate::leanh::lean_ctor_set(v___x_2655_, 1, v_a_2591_);
                crate::leanh::lean_ctor_set(v___x_2655_, 2, v_a_2615_);
                crate::leanh::lean_ctor_set(v___x_2655_, 3, v_a_2627_);
                crate::leanh::lean_ctor_set(v___x_2655_, 4, v_a_2639_);
                crate::leanh::lean_ctor_set(v___x_2655_, 5, v_a_2651_);
                v___x_2656_ = (crate::leanh::lean_unbox(v_a_2603_) as u8);
                crate::leanh::lean_dec(v_a_2603_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2655_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                    v___x_2656_,
                );
                if v_isShared_2654_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2653_, 0, v___x_2655_);
                    v___x_2658_ = v___x_2653_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2659_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2655_);
                    v___x_2658_ = v_reuseFailAlloc_2659_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2658_;
            }
            19 => {
                if v_isShared_2667_ == 0 {
                    v___x_2669_ = v___x_2666_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2670_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
                    v___x_2669_ = v_reuseFailAlloc_2670_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2669_;
            }
            21 => {
                if v_isShared_2679_ == 0 {
                    v___x_2681_ = v___x_2678_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2682_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
                    v___x_2681_ = v_reuseFailAlloc_2682_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2681_;
            }
            23 => {
                if v_isShared_2691_ == 0 {
                    v___x_2693_ = v___x_2690_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2694_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
                    v___x_2693_ = v_reuseFailAlloc_2694_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2693_;
            }
            25 => {
                if v_isShared_2703_ == 0 {
                    v___x_2705_ = v___x_2702_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2706_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
                    v___x_2705_ = v_reuseFailAlloc_2706_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_2705_;
            }
            27 => {
                if v_isShared_2715_ == 0 {
                    v___x_2717_ = v___x_2714_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2718_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2712_);
                    v___x_2717_ = v_reuseFailAlloc_2718_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2717_;
            }
            29 => {
                v___x_2724_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2724_, 0, v_a_2684_);
                crate::leanh::lean_ctor_set(v___x_2724_, 1, v_a_2696_);
                crate::leanh::lean_ctor_set(v___x_2724_, 2, v_a_2720_);
                v___x_2725_ = (crate::leanh::lean_unbox(v_a_2708_) as u8);
                crate::leanh::lean_dec(v_a_2708_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2724_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_2725_,
                );
                if v_isShared_2723_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2722_, 0, v___x_2724_);
                    v___x_2727_ = v___x_2722_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2728_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2724_);
                    v___x_2727_ = v_reuseFailAlloc_2728_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_2727_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__1(
    mut v_x_2732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2737_: u8 = 0;
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2741_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2732_) == 0 {
                    v___x_2733_ = crate::leanh::lean_box(0);
                    return v___x_2733_;
                } else {
                    v_val_2734_ = crate::leanh::lean_ctor_get(v_x_2732_, 0);
                    v_isSharedCheck_2741_ = (!crate::leanh::lean_is_exclusive(v_x_2732_)) as u8;
                    if v_isSharedCheck_2741_ == 0 {
                        v___x_2736_ = v_x_2732_;
                        v_isShared_2737_ = v_isSharedCheck_2741_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2734_);
                        crate::leanh::lean_dec(v_x_2732_);
                        v___x_2736_ = crate::leanh::lean_box(0);
                        v_isShared_2737_ = v_isSharedCheck_2741_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2737_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2736_, 3);
                    v___x_2739_ = v___x_2736_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2740_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_val_2734_);
                    v___x_2739_ = v_reuseFailAlloc_2740_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2739_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(
    mut v_x_2742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2747_: u8 = 0;
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2752_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2742_) == 0 {
                    v___x_2743_ = crate::leanh::lean_box(0);
                    return v___x_2743_;
                } else {
                    v_val_2744_ = crate::leanh::lean_ctor_get(v_x_2742_, 0);
                    v_isSharedCheck_2752_ = (!crate::leanh::lean_is_exclusive(v_x_2742_)) as u8;
                    if v_isSharedCheck_2752_ == 0 {
                        v___x_2746_ = v_x_2742_;
                        v_isShared_2747_ = v_isSharedCheck_2752_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2744_);
                        crate::leanh::lean_dec(v_x_2742_);
                        v___x_2746_ = crate::leanh::lean_box(0);
                        v_isShared_2747_ = v_isSharedCheck_2752_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2748_ = l_Lake_mkRelPathString(v_val_2744_);
                if v_isShared_2747_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2746_, 3);
                    crate::leanh::lean_ctor_set(v___x_2746_, 0, v___x_2748_);
                    v___x_2750_ = v___x_2746_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2751_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2748_);
                    v___x_2750_ = v_reuseFailAlloc_2751_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2750_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(
    mut v_msg_2753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2754_ = crate::leanh::lean_box(1);
    v___x_2755_ = lean_panic_fn_borrowed(v___x_2754_, v_msg_2753_);
    return v___x_2755_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2759_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__2;
    v___x_2760_ = crate::leanh::lean_unsigned_to_nat(35);
    v___x_2761_ = crate::leanh::lean_unsigned_to_nat(182);
    v___x_2762_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__1;
    v___x_2763_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__0;
    v___x_2764_ = l_mkPanicMessageWithDecl(
        v___x_2763_,
        v___x_2762_,
        v___x_2761_,
        v___x_2760_,
        v___x_2759_,
    );
    return v___x_2764_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2765_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__2;
    v___x_2766_ = crate::leanh::lean_unsigned_to_nat(21);
    v___x_2767_ = crate::leanh::lean_unsigned_to_nat(183);
    v___x_2768_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__1;
    v___x_2769_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__0;
    v___x_2770_ = l_mkPanicMessageWithDecl(
        v___x_2769_,
        v___x_2768_,
        v___x_2767_,
        v___x_2766_,
        v___x_2765_,
    );
    return v___x_2770_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2773_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__6;
    v___x_2774_ = crate::leanh::lean_unsigned_to_nat(35);
    v___x_2775_ = crate::leanh::lean_unsigned_to_nat(276);
    v___x_2776_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__5;
    v___x_2777_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__0;
    v___x_2778_ = l_mkPanicMessageWithDecl(
        v___x_2777_,
        v___x_2776_,
        v___x_2775_,
        v___x_2774_,
        v___x_2773_,
    );
    return v___x_2778_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2779_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__6;
    v___x_2780_ = crate::leanh::lean_unsigned_to_nat(21);
    v___x_2781_ = crate::leanh::lean_unsigned_to_nat(277);
    v___x_2782_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__5;
    v___x_2783_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__0;
    v___x_2784_ = l_mkPanicMessageWithDecl(
        v___x_2783_,
        v___x_2782_,
        v___x_2781_,
        v___x_2780_,
        v___x_2779_,
    );
    return v___x_2784_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(
    mut v_k_2785_: *mut crate::leanh::LeanObject,
    mut v_v_2786_: *mut crate::leanh::LeanObject,
    mut v_t_2787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2795_: u8 = 0;
    let mut v___x_2796_: u8 = 0;
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: u8 = 0;
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2815_: u8 = 0;
    let mut v_size_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: u8 = 0;
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2827_: u8 = 0;
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2854_: u8 = 0;
    let mut v_unused_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2869_: u8 = 0;
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2873_: u8 = 0;
    let mut v_unused_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2884_: u8 = 0;
    let mut v_unused_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2903_: u8 = 0;
    let mut v_size_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2914_: u8 = 0;
    let mut v_unused_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2921_: u8 = 0;
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2930_: u8 = 0;
    let mut v_unused_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2939_: u8 = 0;
    let mut v_k_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2944_: u8 = 0;
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2956_: u8 = 0;
    let mut v_unused_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2960_: u8 = 0;
    let mut v_unused_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: u8 = 0;
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2993_: u8 = 0;
    let mut v_size_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: u8 = 0;
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3005_: u8 = 0;
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3031_: u8 = 0;
    let mut v_unused_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3045_: u8 = 0;
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3049_: u8 = 0;
    let mut v_unused_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3060_: u8 = 0;
    let mut v_unused_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3079_: u8 = 0;
    let mut v_size_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3090_: u8 = 0;
    let mut v_unused_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3097_: u8 = 0;
    let mut v_k_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3102_: u8 = 0;
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3114_: u8 = 0;
    let mut v_unused_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3118_: u8 = 0;
    let mut v_unused_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3127_: u8 = 0;
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3136_: u8 = 0;
    let mut v_unused_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3148_: u8 = 0;
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_2787_) == 0 {
                    v_size_2788_ = crate::leanh::lean_ctor_get(v_t_2787_, 0);
                    v_k_2789_ = crate::leanh::lean_ctor_get(v_t_2787_, 1);
                    v_v_2790_ = crate::leanh::lean_ctor_get(v_t_2787_, 2);
                    v_l_2791_ = crate::leanh::lean_ctor_get(v_t_2787_, 3);
                    v_r_2792_ = crate::leanh::lean_ctor_get(v_t_2787_, 4);
                    v_isSharedCheck_3148_ = (!crate::leanh::lean_is_exclusive(v_t_2787_)) as u8;
                    if v_isSharedCheck_3148_ == 0 {
                        v___x_2794_ = v_t_2787_;
                        v_isShared_2795_ = v_isSharedCheck_3148_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_2792_);
                        crate::leanh::lean_inc(v_l_2791_);
                        crate::leanh::lean_inc(v_v_2790_);
                        crate::leanh::lean_inc(v_k_2789_);
                        crate::leanh::lean_inc(v_size_2788_);
                        crate::leanh::lean_dec(v_t_2787_);
                        v___x_2794_ = crate::leanh::lean_box(0);
                        v_isShared_2795_ = v_isSharedCheck_3148_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3149_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3150_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3150_, 0, v___x_3149_);
                    crate::leanh::lean_ctor_set(v___x_3150_, 1, v_k_2785_);
                    crate::leanh::lean_ctor_set(v___x_3150_, 2, v_v_2786_);
                    crate::leanh::lean_ctor_set(v___x_3150_, 3, v_t_2787_);
                    crate::leanh::lean_ctor_set(v___x_3150_, 4, v_t_2787_);
                    return v___x_3150_;
                }
            }
            1 => {
                v___x_2796_ = lean_string_compare(v_k_2785_, v_k_2789_);
                match v___x_2796_ {
                    0 => {
                        crate::leanh::lean_dec(v_size_2788_);
                        v___x_2797_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(v_k_2785_, v_v_2786_, v_l_2791_);
                        if crate::leanh::lean_obj_tag(v_r_2792_) == 0 {
                            if crate::leanh::lean_obj_tag(v___x_2797_) == 0 {
                                v_size_2798_ = crate::leanh::lean_ctor_get(v_r_2792_, 0);
                                v_size_2799_ = crate::leanh::lean_ctor_get(v___x_2797_, 0);
                                crate::leanh::lean_inc(v_size_2799_);
                                v_k_2800_ = crate::leanh::lean_ctor_get(v___x_2797_, 1);
                                crate::leanh::lean_inc(v_k_2800_);
                                v_v_2801_ = crate::leanh::lean_ctor_get(v___x_2797_, 2);
                                crate::leanh::lean_inc(v_v_2801_);
                                v_l_2802_ = crate::leanh::lean_ctor_get(v___x_2797_, 3);
                                crate::leanh::lean_inc(v_l_2802_);
                                v_r_2803_ = crate::leanh::lean_ctor_get(v___x_2797_, 4);
                                crate::leanh::lean_inc(v_r_2803_);
                                v___x_2804_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_2805_ = lean_nat_mul(v___x_2804_, v_size_2798_);
                                v___x_2806_ = lean_nat_dec_lt(v___x_2805_, v_size_2799_);
                                crate::leanh::lean_dec(v___x_2805_);
                                if v___x_2806_ == 0 {
                                    crate::leanh::lean_dec(v_r_2803_);
                                    crate::leanh::lean_dec(v_l_2802_);
                                    crate::leanh::lean_dec(v_v_2801_);
                                    crate::leanh::lean_dec(v_k_2800_);
                                    v___x_2807_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_2808_ = lean_nat_add(v___x_2807_, v_size_2799_);
                                    crate::leanh::lean_dec(v_size_2799_);
                                    v___x_2809_ = lean_nat_add(v___x_2808_, v_size_2798_);
                                    crate::leanh::lean_dec(v___x_2808_);
                                    if v_isShared_2795_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_2794_, 3, v___x_2797_);
                                        crate::leanh::lean_ctor_set(v___x_2794_, 0, v___x_2809_);
                                        v___x_2811_ = v___x_2794_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2812_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2812_,
                                            0,
                                            v___x_2809_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2812_,
                                            1,
                                            v_k_2789_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2812_,
                                            2,
                                            v_v_2790_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2812_,
                                            3,
                                            v___x_2797_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2812_,
                                            4,
                                            v_r_2792_,
                                        );
                                        v___x_2811_ = v_reuseFailAlloc_2812_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v_isSharedCheck_2884_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2797_)) as u8;
                                    if v_isSharedCheck_2884_ == 0 {
                                        v_unused_2885_ =
                                            crate::leanh::lean_ctor_get(v___x_2797_, 4);
                                        crate::leanh::lean_dec(v_unused_2885_);
                                        v_unused_2886_ =
                                            crate::leanh::lean_ctor_get(v___x_2797_, 3);
                                        crate::leanh::lean_dec(v_unused_2886_);
                                        v_unused_2887_ =
                                            crate::leanh::lean_ctor_get(v___x_2797_, 2);
                                        crate::leanh::lean_dec(v_unused_2887_);
                                        v_unused_2888_ =
                                            crate::leanh::lean_ctor_get(v___x_2797_, 1);
                                        crate::leanh::lean_dec(v_unused_2888_);
                                        v_unused_2889_ =
                                            crate::leanh::lean_ctor_get(v___x_2797_, 0);
                                        crate::leanh::lean_dec(v_unused_2889_);
                                        v___x_2814_ = v___x_2797_;
                                        v_isShared_2815_ = v_isSharedCheck_2884_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_2797_);
                                        v___x_2814_ = crate::leanh::lean_box(0);
                                        v_isShared_2815_ = v_isSharedCheck_2884_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_2890_ = crate::leanh::lean_ctor_get(v_r_2792_, 0);
                                v___x_2891_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_2892_ = lean_nat_add(v___x_2891_, v_size_2890_);
                                if v_isShared_2795_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2794_, 3, v___x_2797_);
                                    crate::leanh::lean_ctor_set(v___x_2794_, 0, v___x_2892_);
                                    v___x_2894_ = v___x_2794_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2895_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2895_,
                                        0,
                                        v___x_2892_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2895_,
                                        1,
                                        v_k_2789_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2895_,
                                        2,
                                        v_v_2790_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2895_,
                                        3,
                                        v___x_2797_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2895_,
                                        4,
                                        v_r_2792_,
                                    );
                                    v___x_2894_ = v_reuseFailAlloc_2895_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_2797_) == 0 {
                                v_l_2896_ = crate::leanh::lean_ctor_get(v___x_2797_, 3);
                                crate::leanh::lean_inc(v_l_2896_);
                                if crate::leanh::lean_obj_tag(v_l_2896_) == 0 {
                                    v_r_2897_ = crate::leanh::lean_ctor_get(v___x_2797_, 4);
                                    crate::leanh::lean_inc(v_r_2897_);
                                    if crate::leanh::lean_obj_tag(v_r_2897_) == 0 {
                                        v_size_2898_ = crate::leanh::lean_ctor_get(v___x_2797_, 0);
                                        v_k_2899_ = crate::leanh::lean_ctor_get(v___x_2797_, 1);
                                        v_v_2900_ = crate::leanh::lean_ctor_get(v___x_2797_, 2);
                                        v_isSharedCheck_2914_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2797_)) as u8;
                                        if v_isSharedCheck_2914_ == 0 {
                                            v_unused_2915_ =
                                                crate::leanh::lean_ctor_get(v___x_2797_, 4);
                                            crate::leanh::lean_dec(v_unused_2915_);
                                            v_unused_2916_ =
                                                crate::leanh::lean_ctor_get(v___x_2797_, 3);
                                            crate::leanh::lean_dec(v_unused_2916_);
                                            v___x_2902_ = v___x_2797_;
                                            v_isShared_2903_ = v_isSharedCheck_2914_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_2900_);
                                            crate::leanh::lean_inc(v_k_2899_);
                                            crate::leanh::lean_inc(v_size_2898_);
                                            crate::leanh::lean_dec(v___x_2797_);
                                            v___x_2902_ = crate::leanh::lean_box(0);
                                            v_isShared_2903_ = v_isSharedCheck_2914_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_2917_ = crate::leanh::lean_ctor_get(v___x_2797_, 1);
                                        v_v_2918_ = crate::leanh::lean_ctor_get(v___x_2797_, 2);
                                        v_isSharedCheck_2930_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2797_)) as u8;
                                        if v_isSharedCheck_2930_ == 0 {
                                            v_unused_2931_ =
                                                crate::leanh::lean_ctor_get(v___x_2797_, 4);
                                            crate::leanh::lean_dec(v_unused_2931_);
                                            v_unused_2932_ =
                                                crate::leanh::lean_ctor_get(v___x_2797_, 3);
                                            crate::leanh::lean_dec(v_unused_2932_);
                                            v_unused_2933_ =
                                                crate::leanh::lean_ctor_get(v___x_2797_, 0);
                                            crate::leanh::lean_dec(v_unused_2933_);
                                            v___x_2920_ = v___x_2797_;
                                            v_isShared_2921_ = v_isSharedCheck_2930_;
                                            state = 17;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_2918_);
                                            crate::leanh::lean_inc(v_k_2917_);
                                            crate::leanh::lean_dec(v___x_2797_);
                                            v___x_2920_ = crate::leanh::lean_box(0);
                                            v_isShared_2921_ = v_isSharedCheck_2930_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_2934_ = crate::leanh::lean_ctor_get(v___x_2797_, 4);
                                    crate::leanh::lean_inc(v_r_2934_);
                                    if crate::leanh::lean_obj_tag(v_r_2934_) == 0 {
                                        v_k_2935_ = crate::leanh::lean_ctor_get(v___x_2797_, 1);
                                        v_v_2936_ = crate::leanh::lean_ctor_get(v___x_2797_, 2);
                                        v_isSharedCheck_2960_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2797_)) as u8;
                                        if v_isSharedCheck_2960_ == 0 {
                                            v_unused_2961_ =
                                                crate::leanh::lean_ctor_get(v___x_2797_, 4);
                                            crate::leanh::lean_dec(v_unused_2961_);
                                            v_unused_2962_ =
                                                crate::leanh::lean_ctor_get(v___x_2797_, 3);
                                            crate::leanh::lean_dec(v_unused_2962_);
                                            v_unused_2963_ =
                                                crate::leanh::lean_ctor_get(v___x_2797_, 0);
                                            crate::leanh::lean_dec(v_unused_2963_);
                                            v___x_2938_ = v___x_2797_;
                                            v_isShared_2939_ = v_isSharedCheck_2960_;
                                            state = 20;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_2936_);
                                            crate::leanh::lean_inc(v_k_2935_);
                                            crate::leanh::lean_dec(v___x_2797_);
                                            v___x_2938_ = crate::leanh::lean_box(0);
                                            v_isShared_2939_ = v_isSharedCheck_2960_;
                                            state = 20;
                                            continue;
                                        }
                                    } else {
                                        v___x_2964_ = crate::leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_2795_ == 0 {
                                            crate::leanh::lean_ctor_set(v___x_2794_, 4, v_r_2934_);
                                            crate::leanh::lean_ctor_set(
                                                v___x_2794_,
                                                3,
                                                v___x_2797_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_2794_,
                                                0,
                                                v___x_2964_,
                                            );
                                            v___x_2966_ = v___x_2794_;
                                            state = 25;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_2967_ =
                                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2967_,
                                                0,
                                                v___x_2964_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2967_,
                                                1,
                                                v_k_2789_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2967_,
                                                2,
                                                v_v_2790_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2967_,
                                                3,
                                                v___x_2797_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2967_,
                                                4,
                                                v_r_2934_,
                                            );
                                            v___x_2966_ = v_reuseFailAlloc_2967_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_2968_ = crate::leanh::lean_unsigned_to_nat(1);
                                if v_isShared_2795_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2794_, 4, v___x_2797_);
                                    crate::leanh::lean_ctor_set(v___x_2794_, 3, v___x_2797_);
                                    crate::leanh::lean_ctor_set(v___x_2794_, 0, v___x_2968_);
                                    v___x_2970_ = v___x_2794_;
                                    state = 26;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2971_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2971_,
                                        0,
                                        v___x_2968_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2971_,
                                        1,
                                        v_k_2789_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2971_,
                                        2,
                                        v_v_2790_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2971_,
                                        3,
                                        v___x_2797_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2971_,
                                        4,
                                        v___x_2797_,
                                    );
                                    v___x_2970_ = v_reuseFailAlloc_2971_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_v_2790_);
                        crate::leanh::lean_dec(v_k_2789_);
                        if v_isShared_2795_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2794_, 2, v_v_2786_);
                            crate::leanh::lean_ctor_set(v___x_2794_, 1, v_k_2785_);
                            v___x_2973_ = v___x_2794_;
                            state = 27;
                            continue;
                        } else {
                            v_reuseFailAlloc_2974_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_size_2788_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 1, v_k_2785_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 2, v_v_2786_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 3, v_l_2791_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 4, v_r_2792_);
                            v___x_2973_ = v_reuseFailAlloc_2974_;
                            state = 27;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_size_2788_);
                        v___x_2975_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(v_k_2785_, v_v_2786_, v_r_2792_);
                        if crate::leanh::lean_obj_tag(v_l_2791_) == 0 {
                            if crate::leanh::lean_obj_tag(v___x_2975_) == 0 {
                                v_size_2976_ = crate::leanh::lean_ctor_get(v_l_2791_, 0);
                                v_size_2977_ = crate::leanh::lean_ctor_get(v___x_2975_, 0);
                                crate::leanh::lean_inc(v_size_2977_);
                                v_k_2978_ = crate::leanh::lean_ctor_get(v___x_2975_, 1);
                                crate::leanh::lean_inc(v_k_2978_);
                                v_v_2979_ = crate::leanh::lean_ctor_get(v___x_2975_, 2);
                                crate::leanh::lean_inc(v_v_2979_);
                                v_l_2980_ = crate::leanh::lean_ctor_get(v___x_2975_, 3);
                                crate::leanh::lean_inc(v_l_2980_);
                                v_r_2981_ = crate::leanh::lean_ctor_get(v___x_2975_, 4);
                                crate::leanh::lean_inc(v_r_2981_);
                                v___x_2982_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_2983_ = lean_nat_mul(v___x_2982_, v_size_2976_);
                                v___x_2984_ = lean_nat_dec_lt(v___x_2983_, v_size_2977_);
                                crate::leanh::lean_dec(v___x_2983_);
                                if v___x_2984_ == 0 {
                                    crate::leanh::lean_dec(v_r_2981_);
                                    crate::leanh::lean_dec(v_l_2980_);
                                    crate::leanh::lean_dec(v_v_2979_);
                                    crate::leanh::lean_dec(v_k_2978_);
                                    v___x_2985_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_2986_ = lean_nat_add(v___x_2985_, v_size_2976_);
                                    v___x_2987_ = lean_nat_add(v___x_2986_, v_size_2977_);
                                    crate::leanh::lean_dec(v_size_2977_);
                                    crate::leanh::lean_dec(v___x_2986_);
                                    if v_isShared_2795_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_2794_, 4, v___x_2975_);
                                        crate::leanh::lean_ctor_set(v___x_2794_, 0, v___x_2987_);
                                        v___x_2989_ = v___x_2794_;
                                        state = 28;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2990_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2990_,
                                            0,
                                            v___x_2987_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2990_,
                                            1,
                                            v_k_2789_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2990_,
                                            2,
                                            v_v_2790_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2990_,
                                            3,
                                            v_l_2791_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2990_,
                                            4,
                                            v___x_2975_,
                                        );
                                        v___x_2989_ = v_reuseFailAlloc_2990_;
                                        state = 28;
                                        continue;
                                    }
                                } else {
                                    v_isSharedCheck_3060_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2975_)) as u8;
                                    if v_isSharedCheck_3060_ == 0 {
                                        v_unused_3061_ =
                                            crate::leanh::lean_ctor_get(v___x_2975_, 4);
                                        crate::leanh::lean_dec(v_unused_3061_);
                                        v_unused_3062_ =
                                            crate::leanh::lean_ctor_get(v___x_2975_, 3);
                                        crate::leanh::lean_dec(v_unused_3062_);
                                        v_unused_3063_ =
                                            crate::leanh::lean_ctor_get(v___x_2975_, 2);
                                        crate::leanh::lean_dec(v_unused_3063_);
                                        v_unused_3064_ =
                                            crate::leanh::lean_ctor_get(v___x_2975_, 1);
                                        crate::leanh::lean_dec(v_unused_3064_);
                                        v_unused_3065_ =
                                            crate::leanh::lean_ctor_get(v___x_2975_, 0);
                                        crate::leanh::lean_dec(v_unused_3065_);
                                        v___x_2992_ = v___x_2975_;
                                        v_isShared_2993_ = v_isSharedCheck_3060_;
                                        state = 29;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_2975_);
                                        v___x_2992_ = crate::leanh::lean_box(0);
                                        v_isShared_2993_ = v_isSharedCheck_3060_;
                                        state = 29;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_3066_ = crate::leanh::lean_ctor_get(v_l_2791_, 0);
                                v___x_3067_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_3068_ = lean_nat_add(v___x_3067_, v_size_3066_);
                                if v_isShared_2795_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2794_, 4, v___x_2975_);
                                    crate::leanh::lean_ctor_set(v___x_2794_, 0, v___x_3068_);
                                    v___x_3070_ = v___x_2794_;
                                    state = 39;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3071_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3071_,
                                        0,
                                        v___x_3068_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3071_,
                                        1,
                                        v_k_2789_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3071_,
                                        2,
                                        v_v_2790_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3071_,
                                        3,
                                        v_l_2791_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3071_,
                                        4,
                                        v___x_2975_,
                                    );
                                    v___x_3070_ = v_reuseFailAlloc_3071_;
                                    state = 39;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_2975_) == 0 {
                                v_l_3072_ = crate::leanh::lean_ctor_get(v___x_2975_, 3);
                                crate::leanh::lean_inc(v_l_3072_);
                                if crate::leanh::lean_obj_tag(v_l_3072_) == 0 {
                                    v_r_3073_ = crate::leanh::lean_ctor_get(v___x_2975_, 4);
                                    crate::leanh::lean_inc(v_r_3073_);
                                    if crate::leanh::lean_obj_tag(v_r_3073_) == 0 {
                                        v_size_3074_ = crate::leanh::lean_ctor_get(v___x_2975_, 0);
                                        v_k_3075_ = crate::leanh::lean_ctor_get(v___x_2975_, 1);
                                        v_v_3076_ = crate::leanh::lean_ctor_get(v___x_2975_, 2);
                                        v_isSharedCheck_3090_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2975_)) as u8;
                                        if v_isSharedCheck_3090_ == 0 {
                                            v_unused_3091_ =
                                                crate::leanh::lean_ctor_get(v___x_2975_, 4);
                                            crate::leanh::lean_dec(v_unused_3091_);
                                            v_unused_3092_ =
                                                crate::leanh::lean_ctor_get(v___x_2975_, 3);
                                            crate::leanh::lean_dec(v_unused_3092_);
                                            v___x_3078_ = v___x_2975_;
                                            v_isShared_3079_ = v_isSharedCheck_3090_;
                                            state = 40;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_3076_);
                                            crate::leanh::lean_inc(v_k_3075_);
                                            crate::leanh::lean_inc(v_size_3074_);
                                            crate::leanh::lean_dec(v___x_2975_);
                                            v___x_3078_ = crate::leanh::lean_box(0);
                                            v_isShared_3079_ = v_isSharedCheck_3090_;
                                            state = 40;
                                            continue;
                                        }
                                    } else {
                                        v_k_3093_ = crate::leanh::lean_ctor_get(v___x_2975_, 1);
                                        v_v_3094_ = crate::leanh::lean_ctor_get(v___x_2975_, 2);
                                        v_isSharedCheck_3118_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2975_)) as u8;
                                        if v_isSharedCheck_3118_ == 0 {
                                            v_unused_3119_ =
                                                crate::leanh::lean_ctor_get(v___x_2975_, 4);
                                            crate::leanh::lean_dec(v_unused_3119_);
                                            v_unused_3120_ =
                                                crate::leanh::lean_ctor_get(v___x_2975_, 3);
                                            crate::leanh::lean_dec(v_unused_3120_);
                                            v_unused_3121_ =
                                                crate::leanh::lean_ctor_get(v___x_2975_, 0);
                                            crate::leanh::lean_dec(v_unused_3121_);
                                            v___x_3096_ = v___x_2975_;
                                            v_isShared_3097_ = v_isSharedCheck_3118_;
                                            state = 43;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_3094_);
                                            crate::leanh::lean_inc(v_k_3093_);
                                            crate::leanh::lean_dec(v___x_2975_);
                                            v___x_3096_ = crate::leanh::lean_box(0);
                                            v_isShared_3097_ = v_isSharedCheck_3118_;
                                            state = 43;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_3122_ = crate::leanh::lean_ctor_get(v___x_2975_, 4);
                                    crate::leanh::lean_inc(v_r_3122_);
                                    if crate::leanh::lean_obj_tag(v_r_3122_) == 0 {
                                        v_k_3123_ = crate::leanh::lean_ctor_get(v___x_2975_, 1);
                                        v_v_3124_ = crate::leanh::lean_ctor_get(v___x_2975_, 2);
                                        v_isSharedCheck_3136_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2975_)) as u8;
                                        if v_isSharedCheck_3136_ == 0 {
                                            v_unused_3137_ =
                                                crate::leanh::lean_ctor_get(v___x_2975_, 4);
                                            crate::leanh::lean_dec(v_unused_3137_);
                                            v_unused_3138_ =
                                                crate::leanh::lean_ctor_get(v___x_2975_, 3);
                                            crate::leanh::lean_dec(v_unused_3138_);
                                            v_unused_3139_ =
                                                crate::leanh::lean_ctor_get(v___x_2975_, 0);
                                            crate::leanh::lean_dec(v_unused_3139_);
                                            v___x_3126_ = v___x_2975_;
                                            v_isShared_3127_ = v_isSharedCheck_3136_;
                                            state = 48;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_3124_);
                                            crate::leanh::lean_inc(v_k_3123_);
                                            crate::leanh::lean_dec(v___x_2975_);
                                            v___x_3126_ = crate::leanh::lean_box(0);
                                            v_isShared_3127_ = v_isSharedCheck_3136_;
                                            state = 48;
                                            continue;
                                        }
                                    } else {
                                        v___x_3140_ = crate::leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_2795_ == 0 {
                                            crate::leanh::lean_ctor_set(
                                                v___x_2794_,
                                                4,
                                                v___x_2975_,
                                            );
                                            crate::leanh::lean_ctor_set(v___x_2794_, 3, v_r_3122_);
                                            crate::leanh::lean_ctor_set(
                                                v___x_2794_,
                                                0,
                                                v___x_3140_,
                                            );
                                            v___x_3142_ = v___x_2794_;
                                            state = 51;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3143_ =
                                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3143_,
                                                0,
                                                v___x_3140_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3143_,
                                                1,
                                                v_k_2789_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3143_,
                                                2,
                                                v_v_2790_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3143_,
                                                3,
                                                v_r_3122_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3143_,
                                                4,
                                                v___x_2975_,
                                            );
                                            v___x_3142_ = v_reuseFailAlloc_3143_;
                                            state = 51;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_3144_ = crate::leanh::lean_unsigned_to_nat(1);
                                if v_isShared_2795_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2794_, 4, v___x_2975_);
                                    crate::leanh::lean_ctor_set(v___x_2794_, 3, v___x_2975_);
                                    crate::leanh::lean_ctor_set(v___x_2794_, 0, v___x_3144_);
                                    v___x_3146_ = v___x_2794_;
                                    state = 52;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3147_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3147_,
                                        0,
                                        v___x_3144_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3147_,
                                        1,
                                        v_k_2789_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3147_,
                                        2,
                                        v_v_2790_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3147_,
                                        3,
                                        v___x_2975_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3147_,
                                        4,
                                        v___x_2975_,
                                    );
                                    v___x_3146_ = v_reuseFailAlloc_3147_;
                                    state = 52;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_2811_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_l_2802_) == 0 {
                    if crate::leanh::lean_obj_tag(v_r_2803_) == 0 {
                        v_size_2816_ = crate::leanh::lean_ctor_get(v_l_2802_, 0);
                        v_size_2817_ = crate::leanh::lean_ctor_get(v_r_2803_, 0);
                        v_k_2818_ = crate::leanh::lean_ctor_get(v_r_2803_, 1);
                        v_v_2819_ = crate::leanh::lean_ctor_get(v_r_2803_, 2);
                        v_l_2820_ = crate::leanh::lean_ctor_get(v_r_2803_, 3);
                        v_r_2821_ = crate::leanh::lean_ctor_get(v_r_2803_, 4);
                        v___x_2822_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_2823_ = lean_nat_mul(v___x_2822_, v_size_2816_);
                        v___x_2824_ = lean_nat_dec_lt(v_size_2817_, v___x_2823_);
                        crate::leanh::lean_dec(v___x_2823_);
                        if v___x_2824_ == 0 {
                            crate::leanh::lean_inc(v_r_2821_);
                            crate::leanh::lean_inc(v_l_2820_);
                            crate::leanh::lean_inc(v_v_2819_);
                            crate::leanh::lean_inc(v_k_2818_);
                            v_isSharedCheck_2854_ =
                                (!crate::leanh::lean_is_exclusive(v_r_2803_)) as u8;
                            if v_isSharedCheck_2854_ == 0 {
                                v_unused_2855_ = crate::leanh::lean_ctor_get(v_r_2803_, 4);
                                crate::leanh::lean_dec(v_unused_2855_);
                                v_unused_2856_ = crate::leanh::lean_ctor_get(v_r_2803_, 3);
                                crate::leanh::lean_dec(v_unused_2856_);
                                v_unused_2857_ = crate::leanh::lean_ctor_get(v_r_2803_, 2);
                                crate::leanh::lean_dec(v_unused_2857_);
                                v_unused_2858_ = crate::leanh::lean_ctor_get(v_r_2803_, 1);
                                crate::leanh::lean_dec(v_unused_2858_);
                                v_unused_2859_ = crate::leanh::lean_ctor_get(v_r_2803_, 0);
                                crate::leanh::lean_dec(v_unused_2859_);
                                v___x_2826_ = v_r_2803_;
                                v_isShared_2827_ = v_isSharedCheck_2854_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_r_2803_);
                                v___x_2826_ = crate::leanh::lean_box(0);
                                v_isShared_2827_ = v_isSharedCheck_2854_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2794_);
                            v___x_2860_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_2861_ = lean_nat_add(v___x_2860_, v_size_2799_);
                            crate::leanh::lean_dec(v_size_2799_);
                            v___x_2862_ = lean_nat_add(v___x_2861_, v_size_2798_);
                            crate::leanh::lean_dec(v___x_2861_);
                            v___x_2863_ = lean_nat_add(v___x_2860_, v_size_2798_);
                            v___x_2864_ = lean_nat_add(v___x_2863_, v_size_2817_);
                            crate::leanh::lean_dec(v___x_2863_);
                            crate::leanh::lean_inc_ref(v_r_2792_);
                            if v_isShared_2815_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2814_, 4, v_r_2792_);
                                crate::leanh::lean_ctor_set(v___x_2814_, 3, v_r_2803_);
                                crate::leanh::lean_ctor_set(v___x_2814_, 2, v_v_2790_);
                                crate::leanh::lean_ctor_set(v___x_2814_, 1, v_k_2789_);
                                crate::leanh::lean_ctor_set(v___x_2814_, 0, v___x_2864_);
                                v___x_2866_ = v___x_2814_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_2879_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2864_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2879_, 1, v_k_2789_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2879_, 2, v_v_2790_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2879_, 3, v_r_2803_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2879_, 4, v_r_2792_);
                                v___x_2866_ = v_reuseFailAlloc_2879_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_l_2802_, 5);
                        crate::leanh::lean_del_object(v___x_2814_);
                        crate::leanh::lean_dec(v_v_2801_);
                        crate::leanh::lean_dec(v_k_2800_);
                        crate::leanh::lean_dec(v_size_2799_);
                        crate::leanh::lean_dec_ref_known(v_r_2792_, 5);
                        crate::leanh::lean_del_object(v___x_2794_);
                        crate::leanh::lean_dec(v_v_2790_);
                        crate::leanh::lean_dec(v_k_2789_);
                        v___x_2880_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3);
                        v___x_2881_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v___x_2880_);
                        return v___x_2881_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2814_);
                    crate::leanh::lean_dec(v_r_2803_);
                    crate::leanh::lean_dec(v_v_2801_);
                    crate::leanh::lean_dec(v_k_2800_);
                    crate::leanh::lean_dec(v_size_2799_);
                    crate::leanh::lean_dec_ref_known(v_r_2792_, 5);
                    crate::leanh::lean_del_object(v___x_2794_);
                    crate::leanh::lean_dec(v_v_2790_);
                    crate::leanh::lean_dec(v_k_2789_);
                    v___x_2882_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4);
                    v___x_2883_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v___x_2882_);
                    return v___x_2883_;
                }
            }
            4 => {
                v___x_2828_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2829_ = lean_nat_add(v___x_2828_, v_size_2799_);
                crate::leanh::lean_dec(v_size_2799_);
                v___x_2830_ = lean_nat_add(v___x_2829_, v_size_2798_);
                crate::leanh::lean_dec(v___x_2829_);
                v___x_2842_ = lean_nat_add(v___x_2828_, v_size_2816_);
                if crate::leanh::lean_obj_tag(v_l_2820_) == 0 {
                    v_size_2852_ = crate::leanh::lean_ctor_get(v_l_2820_, 0);
                    crate::leanh::lean_inc(v_size_2852_);
                    v___y_2844_ = v_size_2852_;
                    state = 8;
                    continue;
                } else {
                    v___x_2853_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2844_ = v___x_2853_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_2835_ = lean_nat_add(v___y_2832_, v___y_2834_);
                crate::leanh::lean_dec(v___y_2834_);
                crate::leanh::lean_dec(v___y_2832_);
                if v_isShared_2827_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2826_, 4, v_r_2792_);
                    crate::leanh::lean_ctor_set(v___x_2826_, 3, v_r_2821_);
                    crate::leanh::lean_ctor_set(v___x_2826_, 2, v_v_2790_);
                    crate::leanh::lean_ctor_set(v___x_2826_, 1, v_k_2789_);
                    crate::leanh::lean_ctor_set(v___x_2826_, 0, v___x_2835_);
                    v___x_2837_ = v___x_2826_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2841_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2835_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2841_, 1, v_k_2789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2841_, 2, v_v_2790_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2841_, 3, v_r_2821_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2841_, 4, v_r_2792_);
                    v___x_2837_ = v_reuseFailAlloc_2841_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2815_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2814_, 4, v___x_2837_);
                    crate::leanh::lean_ctor_set(v___x_2814_, 3, v___y_2833_);
                    crate::leanh::lean_ctor_set(v___x_2814_, 2, v_v_2819_);
                    crate::leanh::lean_ctor_set(v___x_2814_, 1, v_k_2818_);
                    crate::leanh::lean_ctor_set(v___x_2814_, 0, v___x_2830_);
                    v___x_2839_ = v___x_2814_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2840_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2830_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_k_2818_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 2, v_v_2819_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 3, v___y_2833_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 4, v___x_2837_);
                    v___x_2839_ = v_reuseFailAlloc_2840_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2839_;
            }
            8 => {
                v___x_2845_ = lean_nat_add(v___x_2842_, v___y_2844_);
                crate::leanh::lean_dec(v___y_2844_);
                crate::leanh::lean_dec(v___x_2842_);
                if v_isShared_2795_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2794_, 4, v_l_2820_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 3, v_l_2802_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 2, v_v_2801_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 1, v_k_2800_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 0, v___x_2845_);
                    v___x_2847_ = v___x_2794_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2851_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2845_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2851_, 1, v_k_2800_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2851_, 2, v_v_2801_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2851_, 3, v_l_2802_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2851_, 4, v_l_2820_);
                    v___x_2847_ = v_reuseFailAlloc_2851_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2848_ = lean_nat_add(v___x_2828_, v_size_2798_);
                if crate::leanh::lean_obj_tag(v_r_2821_) == 0 {
                    v_size_2849_ = crate::leanh::lean_ctor_get(v_r_2821_, 0);
                    crate::leanh::lean_inc(v_size_2849_);
                    v___y_2832_ = v___x_2848_;
                    v___y_2833_ = v___x_2847_;
                    v___y_2834_ = v_size_2849_;
                    state = 5;
                    continue;
                } else {
                    v___x_2850_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2832_ = v___x_2848_;
                    v___y_2833_ = v___x_2847_;
                    v___y_2834_ = v___x_2850_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_2873_ = (!crate::leanh::lean_is_exclusive(v_r_2792_)) as u8;
                if v_isSharedCheck_2873_ == 0 {
                    v_unused_2874_ = crate::leanh::lean_ctor_get(v_r_2792_, 4);
                    crate::leanh::lean_dec(v_unused_2874_);
                    v_unused_2875_ = crate::leanh::lean_ctor_get(v_r_2792_, 3);
                    crate::leanh::lean_dec(v_unused_2875_);
                    v_unused_2876_ = crate::leanh::lean_ctor_get(v_r_2792_, 2);
                    crate::leanh::lean_dec(v_unused_2876_);
                    v_unused_2877_ = crate::leanh::lean_ctor_get(v_r_2792_, 1);
                    crate::leanh::lean_dec(v_unused_2877_);
                    v_unused_2878_ = crate::leanh::lean_ctor_get(v_r_2792_, 0);
                    crate::leanh::lean_dec(v_unused_2878_);
                    v___x_2868_ = v_r_2792_;
                    v_isShared_2869_ = v_isSharedCheck_2873_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_2792_);
                    v___x_2868_ = crate::leanh::lean_box(0);
                    v_isShared_2869_ = v_isSharedCheck_2873_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2869_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2868_, 4, v___x_2866_);
                    crate::leanh::lean_ctor_set(v___x_2868_, 3, v_l_2802_);
                    crate::leanh::lean_ctor_set(v___x_2868_, 2, v_v_2801_);
                    crate::leanh::lean_ctor_set(v___x_2868_, 1, v_k_2800_);
                    crate::leanh::lean_ctor_set(v___x_2868_, 0, v___x_2862_);
                    v___x_2871_ = v___x_2868_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2872_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2872_, 0, v___x_2862_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2872_, 1, v_k_2800_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2872_, 2, v_v_2801_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2872_, 3, v_l_2802_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2872_, 4, v___x_2866_);
                    v___x_2871_ = v_reuseFailAlloc_2872_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2871_;
            }
            13 => {
                return v___x_2894_;
            }
            14 => {
                v_size_2904_ = crate::leanh::lean_ctor_get(v_r_2897_, 0);
                v___x_2905_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2906_ = lean_nat_add(v___x_2905_, v_size_2898_);
                crate::leanh::lean_dec(v_size_2898_);
                v___x_2907_ = lean_nat_add(v___x_2905_, v_size_2904_);
                if v_isShared_2903_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2902_, 4, v_r_2792_);
                    crate::leanh::lean_ctor_set(v___x_2902_, 3, v_r_2897_);
                    crate::leanh::lean_ctor_set(v___x_2902_, 2, v_v_2790_);
                    crate::leanh::lean_ctor_set(v___x_2902_, 1, v_k_2789_);
                    crate::leanh::lean_ctor_set(v___x_2902_, 0, v___x_2907_);
                    v___x_2909_ = v___x_2902_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2913_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2907_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 1, v_k_2789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 2, v_v_2790_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 3, v_r_2897_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 4, v_r_2792_);
                    v___x_2909_ = v_reuseFailAlloc_2913_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_2795_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2794_, 4, v___x_2909_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 3, v_l_2896_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 2, v_v_2900_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 1, v_k_2899_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 0, v___x_2906_);
                    v___x_2911_ = v___x_2794_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2912_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2906_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_k_2899_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 2, v_v_2900_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 3, v_l_2896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 4, v___x_2909_);
                    v___x_2911_ = v_reuseFailAlloc_2912_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2911_;
            }
            17 => {
                v___x_2922_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2923_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_2921_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2920_, 3, v_r_2897_);
                    crate::leanh::lean_ctor_set(v___x_2920_, 2, v_v_2790_);
                    crate::leanh::lean_ctor_set(v___x_2920_, 1, v_k_2789_);
                    crate::leanh::lean_ctor_set(v___x_2920_, 0, v___x_2923_);
                    v___x_2925_ = v___x_2920_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2929_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2929_, 0, v___x_2923_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2929_, 1, v_k_2789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2929_, 2, v_v_2790_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2929_, 3, v_r_2897_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2929_, 4, v_r_2897_);
                    v___x_2925_ = v_reuseFailAlloc_2929_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_2795_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2794_, 4, v___x_2925_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 3, v_l_2896_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 2, v_v_2918_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 1, v_k_2917_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 0, v___x_2922_);
                    v___x_2927_ = v___x_2794_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2928_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2928_, 0, v___x_2922_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2928_, 1, v_k_2917_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2928_, 2, v_v_2918_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2928_, 3, v_l_2896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2928_, 4, v___x_2925_);
                    v___x_2927_ = v_reuseFailAlloc_2928_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2927_;
            }
            20 => {
                v_k_2940_ = crate::leanh::lean_ctor_get(v_r_2934_, 1);
                v_v_2941_ = crate::leanh::lean_ctor_get(v_r_2934_, 2);
                v_isSharedCheck_2956_ = (!crate::leanh::lean_is_exclusive(v_r_2934_)) as u8;
                if v_isSharedCheck_2956_ == 0 {
                    v_unused_2957_ = crate::leanh::lean_ctor_get(v_r_2934_, 4);
                    crate::leanh::lean_dec(v_unused_2957_);
                    v_unused_2958_ = crate::leanh::lean_ctor_get(v_r_2934_, 3);
                    crate::leanh::lean_dec(v_unused_2958_);
                    v_unused_2959_ = crate::leanh::lean_ctor_get(v_r_2934_, 0);
                    crate::leanh::lean_dec(v_unused_2959_);
                    v___x_2943_ = v_r_2934_;
                    v_isShared_2944_ = v_isSharedCheck_2956_;
                    state = 21;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_2941_);
                    crate::leanh::lean_inc(v_k_2940_);
                    crate::leanh::lean_dec(v_r_2934_);
                    v___x_2943_ = crate::leanh::lean_box(0);
                    v_isShared_2944_ = v_isSharedCheck_2956_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_2945_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2946_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_2944_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2943_, 4, v_l_2896_);
                    crate::leanh::lean_ctor_set(v___x_2943_, 3, v_l_2896_);
                    crate::leanh::lean_ctor_set(v___x_2943_, 2, v_v_2936_);
                    crate::leanh::lean_ctor_set(v___x_2943_, 1, v_k_2935_);
                    crate::leanh::lean_ctor_set(v___x_2943_, 0, v___x_2946_);
                    v___x_2948_ = v___x_2943_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2955_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2946_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 1, v_k_2935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 2, v_v_2936_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 3, v_l_2896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 4, v_l_2896_);
                    v___x_2948_ = v_reuseFailAlloc_2955_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_2939_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2938_, 4, v_l_2896_);
                    crate::leanh::lean_ctor_set(v___x_2938_, 2, v_v_2790_);
                    crate::leanh::lean_ctor_set(v___x_2938_, 1, v_k_2789_);
                    crate::leanh::lean_ctor_set(v___x_2938_, 0, v___x_2946_);
                    v___x_2950_ = v___x_2938_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2954_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2946_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_k_2789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2954_, 2, v_v_2790_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2954_, 3, v_l_2896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2954_, 4, v_l_2896_);
                    v___x_2950_ = v_reuseFailAlloc_2954_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_2795_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2794_, 4, v___x_2950_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 3, v___x_2948_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 2, v_v_2941_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 1, v_k_2940_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 0, v___x_2945_);
                    v___x_2952_ = v___x_2794_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2953_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2945_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2953_, 1, v_k_2940_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2953_, 2, v_v_2941_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2953_, 3, v___x_2948_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2953_, 4, v___x_2950_);
                    v___x_2952_ = v_reuseFailAlloc_2953_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2952_;
            }
            25 => {
                return v___x_2966_;
            }
            26 => {
                return v___x_2970_;
            }
            27 => {
                return v___x_2973_;
            }
            28 => {
                return v___x_2989_;
            }
            29 => {
                if crate::leanh::lean_obj_tag(v_l_2980_) == 0 {
                    if crate::leanh::lean_obj_tag(v_r_2981_) == 0 {
                        v_size_2994_ = crate::leanh::lean_ctor_get(v_l_2980_, 0);
                        v_k_2995_ = crate::leanh::lean_ctor_get(v_l_2980_, 1);
                        v_v_2996_ = crate::leanh::lean_ctor_get(v_l_2980_, 2);
                        v_l_2997_ = crate::leanh::lean_ctor_get(v_l_2980_, 3);
                        v_r_2998_ = crate::leanh::lean_ctor_get(v_l_2980_, 4);
                        v_size_2999_ = crate::leanh::lean_ctor_get(v_r_2981_, 0);
                        v___x_3000_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_3001_ = lean_nat_mul(v___x_3000_, v_size_2999_);
                        v___x_3002_ = lean_nat_dec_lt(v_size_2994_, v___x_3001_);
                        crate::leanh::lean_dec(v___x_3001_);
                        if v___x_3002_ == 0 {
                            crate::leanh::lean_inc(v_r_2998_);
                            crate::leanh::lean_inc(v_l_2997_);
                            crate::leanh::lean_inc(v_v_2996_);
                            crate::leanh::lean_inc(v_k_2995_);
                            v_isSharedCheck_3031_ =
                                (!crate::leanh::lean_is_exclusive(v_l_2980_)) as u8;
                            if v_isSharedCheck_3031_ == 0 {
                                v_unused_3032_ = crate::leanh::lean_ctor_get(v_l_2980_, 4);
                                crate::leanh::lean_dec(v_unused_3032_);
                                v_unused_3033_ = crate::leanh::lean_ctor_get(v_l_2980_, 3);
                                crate::leanh::lean_dec(v_unused_3033_);
                                v_unused_3034_ = crate::leanh::lean_ctor_get(v_l_2980_, 2);
                                crate::leanh::lean_dec(v_unused_3034_);
                                v_unused_3035_ = crate::leanh::lean_ctor_get(v_l_2980_, 1);
                                crate::leanh::lean_dec(v_unused_3035_);
                                v_unused_3036_ = crate::leanh::lean_ctor_get(v_l_2980_, 0);
                                crate::leanh::lean_dec(v_unused_3036_);
                                v___x_3004_ = v_l_2980_;
                                v_isShared_3005_ = v_isSharedCheck_3031_;
                                state = 30;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_l_2980_);
                                v___x_3004_ = crate::leanh::lean_box(0);
                                v_isShared_3005_ = v_isSharedCheck_3031_;
                                state = 30;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2794_);
                            v___x_3037_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_3038_ = lean_nat_add(v___x_3037_, v_size_2976_);
                            v___x_3039_ = lean_nat_add(v___x_3038_, v_size_2977_);
                            crate::leanh::lean_dec(v_size_2977_);
                            v___x_3040_ = lean_nat_add(v___x_3038_, v_size_2994_);
                            crate::leanh::lean_dec(v___x_3038_);
                            crate::leanh::lean_inc_ref(v_l_2791_);
                            if v_isShared_2993_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2992_, 4, v_l_2980_);
                                crate::leanh::lean_ctor_set(v___x_2992_, 3, v_l_2791_);
                                crate::leanh::lean_ctor_set(v___x_2992_, 2, v_v_2790_);
                                crate::leanh::lean_ctor_set(v___x_2992_, 1, v_k_2789_);
                                crate::leanh::lean_ctor_set(v___x_2992_, 0, v___x_3040_);
                                v___x_3042_ = v___x_2992_;
                                state = 36;
                                continue;
                            } else {
                                v_reuseFailAlloc_3055_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3040_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 1, v_k_2789_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 2, v_v_2790_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 3, v_l_2791_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 4, v_l_2980_);
                                v___x_3042_ = v_reuseFailAlloc_3055_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_l_2980_, 5);
                        crate::leanh::lean_del_object(v___x_2992_);
                        crate::leanh::lean_dec(v_v_2979_);
                        crate::leanh::lean_dec(v_k_2978_);
                        crate::leanh::lean_dec(v_size_2977_);
                        crate::leanh::lean_dec_ref_known(v_l_2791_, 5);
                        crate::leanh::lean_del_object(v___x_2794_);
                        crate::leanh::lean_dec(v_v_2790_);
                        crate::leanh::lean_dec(v_k_2789_);
                        v___x_3056_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7);
                        v___x_3057_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v___x_3056_);
                        return v___x_3057_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2992_);
                    crate::leanh::lean_dec(v_r_2981_);
                    crate::leanh::lean_dec(v_v_2979_);
                    crate::leanh::lean_dec(v_k_2978_);
                    crate::leanh::lean_dec(v_size_2977_);
                    crate::leanh::lean_dec_ref_known(v_l_2791_, 5);
                    crate::leanh::lean_del_object(v___x_2794_);
                    crate::leanh::lean_dec(v_v_2790_);
                    crate::leanh::lean_dec(v_k_2789_);
                    v___x_3058_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8);
                    v___x_3059_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v___x_3058_);
                    return v___x_3059_;
                }
            }
            30 => {
                v___x_3006_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3007_ = lean_nat_add(v___x_3006_, v_size_2976_);
                v___x_3008_ = lean_nat_add(v___x_3007_, v_size_2977_);
                crate::leanh::lean_dec(v_size_2977_);
                if crate::leanh::lean_obj_tag(v_l_2997_) == 0 {
                    v_size_3029_ = crate::leanh::lean_ctor_get(v_l_2997_, 0);
                    crate::leanh::lean_inc(v_size_3029_);
                    v___y_3021_ = v_size_3029_;
                    state = 34;
                    continue;
                } else {
                    v___x_3030_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3021_ = v___x_3030_;
                    state = 34;
                    continue;
                }
            }
            31 => {
                v___x_3013_ = lean_nat_add(v___y_3011_, v___y_3012_);
                crate::leanh::lean_dec(v___y_3012_);
                crate::leanh::lean_dec(v___y_3011_);
                if v_isShared_3005_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3004_, 4, v_r_2981_);
                    crate::leanh::lean_ctor_set(v___x_3004_, 3, v_r_2998_);
                    crate::leanh::lean_ctor_set(v___x_3004_, 2, v_v_2979_);
                    crate::leanh::lean_ctor_set(v___x_3004_, 1, v_k_2978_);
                    crate::leanh::lean_ctor_set(v___x_3004_, 0, v___x_3013_);
                    v___x_3015_ = v___x_3004_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3019_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_3013_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3019_, 1, v_k_2978_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3019_, 2, v_v_2979_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3019_, 3, v_r_2998_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3019_, 4, v_r_2981_);
                    v___x_3015_ = v_reuseFailAlloc_3019_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_2993_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2992_, 4, v___x_3015_);
                    crate::leanh::lean_ctor_set(v___x_2992_, 3, v___y_3010_);
                    crate::leanh::lean_ctor_set(v___x_2992_, 2, v_v_2996_);
                    crate::leanh::lean_ctor_set(v___x_2992_, 1, v_k_2995_);
                    crate::leanh::lean_ctor_set(v___x_2992_, 0, v___x_3008_);
                    v___x_3017_ = v___x_2992_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3018_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 0, v___x_3008_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 1, v_k_2995_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 2, v_v_2996_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 3, v___y_3010_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 4, v___x_3015_);
                    v___x_3017_ = v_reuseFailAlloc_3018_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3017_;
            }
            34 => {
                v___x_3022_ = lean_nat_add(v___x_3007_, v___y_3021_);
                crate::leanh::lean_dec(v___y_3021_);
                crate::leanh::lean_dec(v___x_3007_);
                if v_isShared_2795_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2794_, 4, v_l_2997_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 0, v___x_3022_);
                    v___x_3024_ = v___x_2794_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3028_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3022_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3028_, 1, v_k_2789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3028_, 2, v_v_2790_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3028_, 3, v_l_2791_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3028_, 4, v_l_2997_);
                    v___x_3024_ = v_reuseFailAlloc_3028_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_3025_ = lean_nat_add(v___x_3006_, v_size_2999_);
                if crate::leanh::lean_obj_tag(v_r_2998_) == 0 {
                    v_size_3026_ = crate::leanh::lean_ctor_get(v_r_2998_, 0);
                    crate::leanh::lean_inc(v_size_3026_);
                    v___y_3010_ = v___x_3024_;
                    v___y_3011_ = v___x_3025_;
                    v___y_3012_ = v_size_3026_;
                    state = 31;
                    continue;
                } else {
                    v___x_3027_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3010_ = v___x_3024_;
                    v___y_3011_ = v___x_3025_;
                    v___y_3012_ = v___x_3027_;
                    state = 31;
                    continue;
                }
            }
            36 => {
                v_isSharedCheck_3049_ = (!crate::leanh::lean_is_exclusive(v_l_2791_)) as u8;
                if v_isSharedCheck_3049_ == 0 {
                    v_unused_3050_ = crate::leanh::lean_ctor_get(v_l_2791_, 4);
                    crate::leanh::lean_dec(v_unused_3050_);
                    v_unused_3051_ = crate::leanh::lean_ctor_get(v_l_2791_, 3);
                    crate::leanh::lean_dec(v_unused_3051_);
                    v_unused_3052_ = crate::leanh::lean_ctor_get(v_l_2791_, 2);
                    crate::leanh::lean_dec(v_unused_3052_);
                    v_unused_3053_ = crate::leanh::lean_ctor_get(v_l_2791_, 1);
                    crate::leanh::lean_dec(v_unused_3053_);
                    v_unused_3054_ = crate::leanh::lean_ctor_get(v_l_2791_, 0);
                    crate::leanh::lean_dec(v_unused_3054_);
                    v___x_3044_ = v_l_2791_;
                    v_isShared_3045_ = v_isSharedCheck_3049_;
                    state = 37;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_2791_);
                    v___x_3044_ = crate::leanh::lean_box(0);
                    v_isShared_3045_ = v_isSharedCheck_3049_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_3045_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3044_, 4, v_r_2981_);
                    crate::leanh::lean_ctor_set(v___x_3044_, 3, v___x_3042_);
                    crate::leanh::lean_ctor_set(v___x_3044_, 2, v_v_2979_);
                    crate::leanh::lean_ctor_set(v___x_3044_, 1, v_k_2978_);
                    crate::leanh::lean_ctor_set(v___x_3044_, 0, v___x_3039_);
                    v___x_3047_ = v___x_3044_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3048_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3039_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3048_, 1, v_k_2978_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3048_, 2, v_v_2979_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3048_, 3, v___x_3042_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3048_, 4, v_r_2981_);
                    v___x_3047_ = v_reuseFailAlloc_3048_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3047_;
            }
            39 => {
                return v___x_3070_;
            }
            40 => {
                v_size_3080_ = crate::leanh::lean_ctor_get(v_l_3072_, 0);
                v___x_3081_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3082_ = lean_nat_add(v___x_3081_, v_size_3074_);
                crate::leanh::lean_dec(v_size_3074_);
                v___x_3083_ = lean_nat_add(v___x_3081_, v_size_3080_);
                if v_isShared_3079_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3078_, 4, v_l_3072_);
                    crate::leanh::lean_ctor_set(v___x_3078_, 3, v_l_2791_);
                    crate::leanh::lean_ctor_set(v___x_3078_, 2, v_v_2790_);
                    crate::leanh::lean_ctor_set(v___x_3078_, 1, v_k_2789_);
                    crate::leanh::lean_ctor_set(v___x_3078_, 0, v___x_3083_);
                    v___x_3085_ = v___x_3078_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3089_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3089_, 0, v___x_3083_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3089_, 1, v_k_2789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3089_, 2, v_v_2790_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3089_, 3, v_l_2791_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3089_, 4, v_l_3072_);
                    v___x_3085_ = v_reuseFailAlloc_3089_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                if v_isShared_2795_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2794_, 4, v_r_3073_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 3, v___x_3085_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 2, v_v_3076_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 1, v_k_3075_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 0, v___x_3082_);
                    v___x_3087_ = v___x_2794_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_3088_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3082_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3088_, 1, v_k_3075_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3088_, 2, v_v_3076_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3088_, 3, v___x_3085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3088_, 4, v_r_3073_);
                    v___x_3087_ = v_reuseFailAlloc_3088_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_3087_;
            }
            43 => {
                v_k_3098_ = crate::leanh::lean_ctor_get(v_l_3072_, 1);
                v_v_3099_ = crate::leanh::lean_ctor_get(v_l_3072_, 2);
                v_isSharedCheck_3114_ = (!crate::leanh::lean_is_exclusive(v_l_3072_)) as u8;
                if v_isSharedCheck_3114_ == 0 {
                    v_unused_3115_ = crate::leanh::lean_ctor_get(v_l_3072_, 4);
                    crate::leanh::lean_dec(v_unused_3115_);
                    v_unused_3116_ = crate::leanh::lean_ctor_get(v_l_3072_, 3);
                    crate::leanh::lean_dec(v_unused_3116_);
                    v_unused_3117_ = crate::leanh::lean_ctor_get(v_l_3072_, 0);
                    crate::leanh::lean_dec(v_unused_3117_);
                    v___x_3101_ = v_l_3072_;
                    v_isShared_3102_ = v_isSharedCheck_3114_;
                    state = 44;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_3099_);
                    crate::leanh::lean_inc(v_k_3098_);
                    crate::leanh::lean_dec(v_l_3072_);
                    v___x_3101_ = crate::leanh::lean_box(0);
                    v_isShared_3102_ = v_isSharedCheck_3114_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                v___x_3103_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3104_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_3102_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3101_, 4, v_r_3073_);
                    crate::leanh::lean_ctor_set(v___x_3101_, 3, v_r_3073_);
                    crate::leanh::lean_ctor_set(v___x_3101_, 2, v_v_2790_);
                    crate::leanh::lean_ctor_set(v___x_3101_, 1, v_k_2789_);
                    crate::leanh::lean_ctor_set(v___x_3101_, 0, v___x_3104_);
                    v___x_3106_ = v___x_3101_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_3113_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3104_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3113_, 1, v_k_2789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3113_, 2, v_v_2790_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3113_, 3, v_r_3073_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3113_, 4, v_r_3073_);
                    v___x_3106_ = v_reuseFailAlloc_3113_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_3097_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3096_, 3, v_r_3073_);
                    crate::leanh::lean_ctor_set(v___x_3096_, 0, v___x_3104_);
                    v___x_3108_ = v___x_3096_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_3112_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3112_, 0, v___x_3104_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3112_, 1, v_k_3093_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3112_, 2, v_v_3094_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3112_, 3, v_r_3073_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3112_, 4, v_r_3073_);
                    v___x_3108_ = v_reuseFailAlloc_3112_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                if v_isShared_2795_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2794_, 4, v___x_3108_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 3, v___x_3106_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 2, v_v_3099_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 1, v_k_3098_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 0, v___x_3103_);
                    v___x_3110_ = v___x_2794_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_3111_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3103_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3111_, 1, v_k_3098_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3111_, 2, v_v_3099_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3111_, 3, v___x_3106_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3111_, 4, v___x_3108_);
                    v___x_3110_ = v_reuseFailAlloc_3111_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_3110_;
            }
            48 => {
                v___x_3128_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3129_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_3127_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3126_, 4, v_l_3072_);
                    crate::leanh::lean_ctor_set(v___x_3126_, 2, v_v_2790_);
                    crate::leanh::lean_ctor_set(v___x_3126_, 1, v_k_2789_);
                    crate::leanh::lean_ctor_set(v___x_3126_, 0, v___x_3129_);
                    v___x_3131_ = v___x_3126_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_3135_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3129_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3135_, 1, v_k_2789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3135_, 2, v_v_2790_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3135_, 3, v_l_3072_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3135_, 4, v_l_3072_);
                    v___x_3131_ = v_reuseFailAlloc_3135_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                if v_isShared_2795_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2794_, 4, v_r_3122_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 3, v___x_3131_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 2, v_v_3124_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 1, v_k_3123_);
                    crate::leanh::lean_ctor_set(v___x_2794_, 0, v___x_3128_);
                    v___x_3133_ = v___x_2794_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_3134_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3128_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3134_, 1, v_k_3123_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3134_, 2, v_v_3124_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3134_, 3, v___x_3131_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3134_, 4, v_r_3122_);
                    v___x_3133_ = v_reuseFailAlloc_3134_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_3133_;
            }
            51 => {
                return v___x_3142_;
            }
            52 => {
                return v___x_3146_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1_spec__5(
    mut v_init_3151_: *mut crate::leanh::LeanObject,
    mut v_x_3152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: u8 = 0;
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3152_) == 0 {
                    v_k_3153_ = crate::leanh::lean_ctor_get(v_x_3152_, 1);
                    crate::leanh::lean_inc(v_k_3153_);
                    v_v_3154_ = crate::leanh::lean_ctor_get(v_x_3152_, 2);
                    crate::leanh::lean_inc(v_v_3154_);
                    v_l_3155_ = crate::leanh::lean_ctor_get(v_x_3152_, 3);
                    crate::leanh::lean_inc(v_l_3155_);
                    v_r_3156_ = crate::leanh::lean_ctor_get(v_x_3152_, 4);
                    crate::leanh::lean_inc(v_r_3156_);
                    crate::leanh::lean_dec_ref_known(v_x_3152_, 5);
                    v___x_3157_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1_spec__5(v_init_3151_, v_l_3155_);
                    v___x_3158_ = 1;
                    v___x_3159_ = l_Lean_Name_toString(v_k_3153_, v___x_3158_);
                    v___x_3160_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3160_, 0, v_v_3154_);
                    v___x_3161_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(v___x_3159_, v___x_3160_, v___x_3157_);
                    v_init_3151_ = v___x_3161_;
                    v_x_3152_ = v_r_3156_;
                    state = 0;
                    continue;
                } else {
                    return v_init_3151_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0(
    mut v_m_3163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3164_ = crate::leanh::lean_box(1);
    v___x_3165_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1_spec__5(v___x_3164_, v_m_3163_);
    v___x_3166_ = crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3166_, 0, v___x_3165_);
    return v___x_3166_;
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson(
    mut v_x_3167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3167_) == 0 {
        let mut v_name_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_opts_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_inherited_3170_: u8 = 0;
        let mut v_dir_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3174_: u8 = 0;
        let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_name_3168_ = crate::leanh::lean_ctor_get(v_x_3167_, 0);
        crate::leanh::lean_inc(v_name_3168_);
        v_opts_3169_ = crate::leanh::lean_ctor_get(v_x_3167_, 1);
        crate::leanh::lean_inc(v_opts_3169_);
        v_inherited_3170_ = crate::leanh::lean_ctor_get_uint8(
            v_x_3167_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        );
        v_dir_3171_ = crate::leanh::lean_ctor_get(v_x_3167_, 2);
        crate::leanh::lean_inc_ref(v_dir_3171_);
        crate::leanh::lean_dec_ref_known(v_x_3167_, 3);
        v___x_3172_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2;
        v___x_3173_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6;
        v___x_3174_ = 1;
        v___x_3175_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_name_3168_,
            v___x_3174_,
        );
        v___x_3176_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3176_, 0, v___x_3175_);
        v___x_3177_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3177_, 0, v___x_3173_);
        crate::leanh::lean_ctor_set(v___x_3177_, 1, v___x_3176_);
        v___x_3178_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__8;
        v___x_3179_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0(v_opts_3169_);
        v___x_3180_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3180_, 0, v___x_3178_);
        crate::leanh::lean_ctor_set(v___x_3180_, 1, v___x_3179_);
        v___x_3181_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10;
        v___x_3182_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
        crate::leanh::lean_ctor_set_uint8(v___x_3182_, 0 as u32, v_inherited_3170_);
        v___x_3183_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3183_, 0, v___x_3181_);
        crate::leanh::lean_ctor_set(v___x_3183_, 1, v___x_3182_);
        v___x_3184_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22;
        v___x_3185_ = l_Lake_mkRelPathString(v_dir_3171_);
        v___x_3186_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3186_, 0, v___x_3185_);
        v___x_3187_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3187_, 0, v___x_3184_);
        crate::leanh::lean_ctor_set(v___x_3187_, 1, v___x_3186_);
        v___x_3188_ = crate::leanh::lean_box(0);
        v___x_3189_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3189_, 0, v___x_3187_);
        crate::leanh::lean_ctor_set(v___x_3189_, 1, v___x_3188_);
        v___x_3190_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3190_, 0, v___x_3183_);
        crate::leanh::lean_ctor_set(v___x_3190_, 1, v___x_3189_);
        v___x_3191_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3191_, 0, v___x_3180_);
        crate::leanh::lean_ctor_set(v___x_3191_, 1, v___x_3190_);
        v___x_3192_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3192_, 0, v___x_3177_);
        crate::leanh::lean_ctor_set(v___x_3192_, 1, v___x_3191_);
        v___x_3193_ = l_Lean_Json_mkObj(v___x_3192_);
        crate::leanh::lean_dec_ref_known(v___x_3192_, 2);
        v___x_3194_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3194_, 0, v___x_3172_);
        crate::leanh::lean_ctor_set(v___x_3194_, 1, v___x_3193_);
        v___x_3195_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3195_, 0, v___x_3194_);
        crate::leanh::lean_ctor_set(v___x_3195_, 1, v___x_3188_);
        v___x_3196_ = l_Lean_Json_mkObj(v___x_3195_);
        crate::leanh::lean_dec_ref_known(v___x_3195_, 2);
        return v___x_3196_;
    } else {
        let mut v_name_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_opts_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_inherited_3199_: u8 = 0;
        let mut v_url_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rev_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_inputRev_x3f_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_subDir_x3f_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3206_: u8 = 0;
        let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_name_3197_ = crate::leanh::lean_ctor_get(v_x_3167_, 0);
        crate::leanh::lean_inc(v_name_3197_);
        v_opts_3198_ = crate::leanh::lean_ctor_get(v_x_3167_, 1);
        crate::leanh::lean_inc(v_opts_3198_);
        v_inherited_3199_ = crate::leanh::lean_ctor_get_uint8(
            v_x_3167_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
        );
        v_url_3200_ = crate::leanh::lean_ctor_get(v_x_3167_, 2);
        crate::leanh::lean_inc_ref(v_url_3200_);
        v_rev_3201_ = crate::leanh::lean_ctor_get(v_x_3167_, 3);
        crate::leanh::lean_inc_ref(v_rev_3201_);
        v_inputRev_x3f_3202_ = crate::leanh::lean_ctor_get(v_x_3167_, 4);
        crate::leanh::lean_inc(v_inputRev_x3f_3202_);
        v_subDir_x3f_3203_ = crate::leanh::lean_ctor_get(v_x_3167_, 5);
        crate::leanh::lean_inc(v_subDir_x3f_3203_);
        crate::leanh::lean_dec_ref_known(v_x_3167_, 6);
        v___x_3204_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3;
        v___x_3205_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6;
        v___x_3206_ = 1;
        v___x_3207_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_name_3197_,
            v___x_3206_,
        );
        v___x_3208_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3208_, 0, v___x_3207_);
        v___x_3209_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3209_, 0, v___x_3205_);
        crate::leanh::lean_ctor_set(v___x_3209_, 1, v___x_3208_);
        v___x_3210_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__8;
        v___x_3211_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0(v_opts_3198_);
        v___x_3212_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3212_, 0, v___x_3210_);
        crate::leanh::lean_ctor_set(v___x_3212_, 1, v___x_3211_);
        v___x_3213_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10;
        v___x_3214_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
        crate::leanh::lean_ctor_set_uint8(v___x_3214_, 0 as u32, v_inherited_3199_);
        v___x_3215_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3215_, 0, v___x_3213_);
        crate::leanh::lean_ctor_set(v___x_3215_, 1, v___x_3214_);
        v___x_3216_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12;
        v___x_3217_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3217_, 0, v_url_3200_);
        v___x_3218_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3218_, 0, v___x_3216_);
        crate::leanh::lean_ctor_set(v___x_3218_, 1, v___x_3217_);
        v___x_3219_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14;
        v___x_3220_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3220_, 0, v_rev_3201_);
        v___x_3221_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3221_, 0, v___x_3219_);
        crate::leanh::lean_ctor_set(v___x_3221_, 1, v___x_3220_);
        v___x_3222_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__16;
        v___x_3223_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__1(v_inputRev_x3f_3202_);
        v___x_3224_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3224_, 0, v___x_3222_);
        crate::leanh::lean_ctor_set(v___x_3224_, 1, v___x_3223_);
        v___x_3225_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__18;
        v___x_3226_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_subDir_x3f_3203_);
        v___x_3227_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3227_, 0, v___x_3225_);
        crate::leanh::lean_ctor_set(v___x_3227_, 1, v___x_3226_);
        v___x_3228_ = crate::leanh::lean_box(0);
        v___x_3229_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3229_, 0, v___x_3227_);
        crate::leanh::lean_ctor_set(v___x_3229_, 1, v___x_3228_);
        v___x_3230_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3230_, 0, v___x_3224_);
        crate::leanh::lean_ctor_set(v___x_3230_, 1, v___x_3229_);
        v___x_3231_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3231_, 0, v___x_3221_);
        crate::leanh::lean_ctor_set(v___x_3231_, 1, v___x_3230_);
        v___x_3232_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3232_, 0, v___x_3218_);
        crate::leanh::lean_ctor_set(v___x_3232_, 1, v___x_3231_);
        v___x_3233_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3233_, 0, v___x_3215_);
        crate::leanh::lean_ctor_set(v___x_3233_, 1, v___x_3232_);
        v___x_3234_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3234_, 0, v___x_3212_);
        crate::leanh::lean_ctor_set(v___x_3234_, 1, v___x_3233_);
        v___x_3235_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3235_, 0, v___x_3209_);
        crate::leanh::lean_ctor_set(v___x_3235_, 1, v___x_3234_);
        v___x_3236_ = l_Lean_Json_mkObj(v___x_3235_);
        crate::leanh::lean_dec_ref_known(v___x_3235_, 2);
        v___x_3237_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3237_, 0, v___x_3204_);
        crate::leanh::lean_ctor_set(v___x_3237_, 1, v___x_3236_);
        v___x_3238_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3238_, 0, v___x_3237_);
        crate::leanh::lean_ctor_set(v___x_3238_, 1, v___x_3228_);
        v___x_3239_ = l_Lean_Json_mkObj(v___x_3238_);
        crate::leanh::lean_dec_ref_known(v___x_3238_, 2);
        return v___x_3239_;
    }
}
pub unsafe fn l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3(
    mut v_00_u03b2_3240_: *mut crate::leanh::LeanObject,
    mut v_msg_3241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3242_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v_msg_3241_);
    return v___x_3242_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0(
    mut v_00_u03b2_3243_: *mut crate::leanh::LeanObject,
    mut v_k_3244_: *mut crate::leanh::LeanObject,
    mut v_v_3245_: *mut crate::leanh::LeanObject,
    mut v_t_3246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3247_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(v_k_3244_, v_v_3245_, v_t_3246_);
    return v___x_3247_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1(
    mut v_init_3248_: *mut crate::leanh::LeanObject,
    mut v_t_3249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3250_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1_spec__5(v_init_3248_, v_t_3249_);
    return v___x_3250_;
}
pub unsafe fn l_Lake_PackageEntrySrc_ctorIdx(
    mut v_x_3260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3260_) == 0 {
        let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3261_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_3261_;
    } else {
        let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3262_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_3262_;
    }
}
pub unsafe fn l_Lake_PackageEntrySrc_ctorIdx___boxed(
    mut v_x_3263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3264_ = l_Lake_PackageEntrySrc_ctorIdx(v_x_3263_);
    crate::leanh::lean_dec_ref(v_x_3263_);
    return v_res_3264_;
}
pub unsafe fn l_Lake_PackageEntrySrc_ctorElim___redArg(
    mut v_t_3265_: *mut crate::leanh::LeanObject,
    mut v_k_3266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_3265_) == 0 {
        let mut v_dir_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_dir_3267_ = crate::leanh::lean_ctor_get(v_t_3265_, 0);
        crate::leanh::lean_inc_ref(v_dir_3267_);
        crate::leanh::lean_dec_ref_known(v_t_3265_, 1);
        v___x_3268_ = crate::leanh::lean_apply_1(v_k_3266_, v_dir_3267_);
        return v___x_3268_;
    } else {
        let mut v_url_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rev_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_inputRev_x3f_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_subDir_x3f_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_url_3269_ = crate::leanh::lean_ctor_get(v_t_3265_, 0);
        crate::leanh::lean_inc_ref(v_url_3269_);
        v_rev_3270_ = crate::leanh::lean_ctor_get(v_t_3265_, 1);
        crate::leanh::lean_inc_ref(v_rev_3270_);
        v_inputRev_x3f_3271_ = crate::leanh::lean_ctor_get(v_t_3265_, 2);
        crate::leanh::lean_inc(v_inputRev_x3f_3271_);
        v_subDir_x3f_3272_ = crate::leanh::lean_ctor_get(v_t_3265_, 3);
        crate::leanh::lean_inc(v_subDir_x3f_3272_);
        crate::leanh::lean_dec_ref_known(v_t_3265_, 4);
        v___x_3273_ = crate::leanh::lean_apply_4(
            v_k_3266_,
            v_url_3269_,
            v_rev_3270_,
            v_inputRev_x3f_3271_,
            v_subDir_x3f_3272_,
        );
        return v___x_3273_;
    }
}
pub unsafe fn l_Lake_PackageEntrySrc_ctorElim(
    mut v_motive_3274_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3275_: *mut crate::leanh::LeanObject,
    mut v_t_3276_: *mut crate::leanh::LeanObject,
    mut v_h_3277_: *mut crate::leanh::LeanObject,
    mut v_k_3278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3279_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_3276_, v_k_3278_);
    return v___x_3279_;
}
pub unsafe fn l_Lake_PackageEntrySrc_ctorElim___boxed(
    mut v_motive_3280_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3281_: *mut crate::leanh::LeanObject,
    mut v_t_3282_: *mut crate::leanh::LeanObject,
    mut v_h_3283_: *mut crate::leanh::LeanObject,
    mut v_k_3284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3285_ = l_Lake_PackageEntrySrc_ctorElim(
        v_motive_3280_,
        v_ctorIdx_3281_,
        v_t_3282_,
        v_h_3283_,
        v_k_3284_,
    );
    crate::leanh::lean_dec(v_ctorIdx_3281_);
    return v_res_3285_;
}
pub unsafe fn l_Lake_PackageEntrySrc_path_elim___redArg(
    mut v_t_3286_: *mut crate::leanh::LeanObject,
    mut v_path_3287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3288_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_3286_, v_path_3287_);
    return v___x_3288_;
}
pub unsafe fn l_Lake_PackageEntrySrc_path_elim(
    mut v_motive_3289_: *mut crate::leanh::LeanObject,
    mut v_t_3290_: *mut crate::leanh::LeanObject,
    mut v_h_3291_: *mut crate::leanh::LeanObject,
    mut v_path_3292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3293_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_3290_, v_path_3292_);
    return v___x_3293_;
}
pub unsafe fn l_Lake_PackageEntrySrc_git_elim___redArg(
    mut v_t_3294_: *mut crate::leanh::LeanObject,
    mut v_git_3295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3296_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_3294_, v_git_3295_);
    return v___x_3296_;
}
pub unsafe fn l_Lake_PackageEntrySrc_git_elim(
    mut v_motive_3297_: *mut crate::leanh::LeanObject,
    mut v_t_3298_: *mut crate::leanh::LeanObject,
    mut v_h_3299_: *mut crate::leanh::LeanObject,
    mut v_git_3300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3301_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_3298_, v_git_3300_);
    return v___x_3301_;
}
pub unsafe fn _init_l_Lake_instInhabitedPackageEntry_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: u8 = 0;
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3306_ = l_Lake_instInhabitedPackageEntrySrc_default;
    v___x_3307_ = crate::leanh::lean_box(0);
    v___x_3308_ = l_Lake_defaultConfigFile;
    v___x_3309_ = 0;
    v___x_3310_ = l_Lake_Manifest_version___closed__1;
    v___x_3311_ = crate::leanh::lean_box(0);
    v___x_3312_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3312_, 0, v___x_3311_);
    crate::leanh::lean_ctor_set(v___x_3312_, 1, v___x_3310_);
    crate::leanh::lean_ctor_set(v___x_3312_, 2, v___x_3308_);
    crate::leanh::lean_ctor_set(v___x_3312_, 3, v___x_3307_);
    crate::leanh::lean_ctor_set(v___x_3312_, 4, v___x_3306_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3312_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
        v___x_3309_,
    );
    return v___x_3312_;
}
pub unsafe fn _init_l_Lake_instInhabitedPackageEntry_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3313_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPackageEntry_default___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPackageEntry_default___closed__0_once),
        _init_l_Lake_instInhabitedPackageEntry_default___closed__0,
    );
    return v___x_3313_;
}
pub unsafe fn _init_l_Lake_instInhabitedPackageEntry() -> *mut crate::leanh::LeanObject {
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3314_ = l_Lake_instInhabitedPackageEntry_default;
    return v___x_3314_;
}
pub unsafe fn l_Lake_PackageEntry_prettyName(
    mut v_entry_3315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: u8 = 0;
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_3316_ = crate::leanh::lean_ctor_get(v_entry_3315_, 0);
    crate::leanh::lean_inc(v_name_3316_);
    crate::leanh::lean_dec_ref(v_entry_3315_);
    v___x_3317_ = 0;
    v___x_3318_ = l_Lean_Name_toString(v_name_3316_, v___x_3317_);
    return v___x_3318_;
}
pub unsafe fn l_Lake_PackageEntry_toJson(
    mut v_entry_3335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scope_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inherited_3338_: u8 = 0;
    let mut v_configFile_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_manifestFile_x3f_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_src_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: u8 = 0;
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fields_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3369_: u8 = 0;
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3381_: u8 = 0;
    let mut v_url_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rev_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inputRev_x3f_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subDir_x3f_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_3336_ = crate::leanh::lean_ctor_get(v_entry_3335_, 0);
                crate::leanh::lean_inc(v_name_3336_);
                v_scope_3337_ = crate::leanh::lean_ctor_get(v_entry_3335_, 1);
                crate::leanh::lean_inc_ref(v_scope_3337_);
                v_inherited_3338_ = crate::leanh::lean_ctor_get_uint8(
                    v_entry_3335_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                );
                v_configFile_3339_ = crate::leanh::lean_ctor_get(v_entry_3335_, 2);
                crate::leanh::lean_inc_ref(v_configFile_3339_);
                v_manifestFile_x3f_3340_ = crate::leanh::lean_ctor_get(v_entry_3335_, 3);
                crate::leanh::lean_inc(v_manifestFile_x3f_3340_);
                v_src_3341_ = crate::leanh::lean_ctor_get(v_entry_3335_, 4);
                crate::leanh::lean_inc_ref(v_src_3341_);
                crate::leanh::lean_dec_ref(v_entry_3335_);
                v___x_3342_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6;
                v___x_3343_ = 1;
                v___x_3344_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_name_3336_,
                    v___x_3343_,
                );
                v___x_3345_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3345_, 0, v___x_3344_);
                v___x_3346_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3346_, 0, v___x_3342_);
                crate::leanh::lean_ctor_set(v___x_3346_, 1, v___x_3345_);
                v___x_3347_ = l_Lake_PackageEntry_toJson___closed__0;
                v___x_3348_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3348_, 0, v_scope_3337_);
                v___x_3349_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3349_, 0, v___x_3347_);
                crate::leanh::lean_ctor_set(v___x_3349_, 1, v___x_3348_);
                v___x_3350_ = l_Lake_PackageEntry_toJson___closed__1;
                v___x_3351_ = l_Lake_mkRelPathString(v_configFile_3339_);
                v___x_3352_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3352_, 0, v___x_3351_);
                v___x_3353_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3353_, 0, v___x_3350_);
                crate::leanh::lean_ctor_set(v___x_3353_, 1, v___x_3352_);
                v___x_3354_ = l_Lake_PackageEntry_toJson___closed__2;
                v___x_3355_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_manifestFile_x3f_3340_);
                v___x_3356_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3356_, 0, v___x_3354_);
                crate::leanh::lean_ctor_set(v___x_3356_, 1, v___x_3355_);
                v___x_3357_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10;
                v___x_3358_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_3358_, 0 as u32, v_inherited_3338_);
                v___x_3359_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3359_, 0, v___x_3357_);
                crate::leanh::lean_ctor_set(v___x_3359_, 1, v___x_3358_);
                v___x_3360_ = crate::leanh::lean_box(0);
                v___x_3361_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3361_, 0, v___x_3359_);
                crate::leanh::lean_ctor_set(v___x_3361_, 1, v___x_3360_);
                v___x_3362_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3362_, 0, v___x_3356_);
                crate::leanh::lean_ctor_set(v___x_3362_, 1, v___x_3361_);
                v___x_3363_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3363_, 0, v___x_3353_);
                crate::leanh::lean_ctor_set(v___x_3363_, 1, v___x_3362_);
                v___x_3364_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3364_, 0, v___x_3349_);
                crate::leanh::lean_ctor_set(v___x_3364_, 1, v___x_3363_);
                v_fields_3365_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_fields_3365_, 0, v___x_3346_);
                crate::leanh::lean_ctor_set(v_fields_3365_, 1, v___x_3364_);
                if crate::leanh::lean_obj_tag(v_src_3341_) == 0 {
                    v_dir_3366_ = crate::leanh::lean_ctor_get(v_src_3341_, 0);
                    v_isSharedCheck_3381_ = (!crate::leanh::lean_is_exclusive(v_src_3341_)) as u8;
                    if v_isSharedCheck_3381_ == 0 {
                        v___x_3368_ = v_src_3341_;
                        v_isShared_3369_ = v_isSharedCheck_3381_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_dir_3366_);
                        crate::leanh::lean_dec(v_src_3341_);
                        v___x_3368_ = crate::leanh::lean_box(0);
                        v_isShared_3369_ = v_isSharedCheck_3381_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_url_3382_ = crate::leanh::lean_ctor_get(v_src_3341_, 0);
                    crate::leanh::lean_inc_ref(v_url_3382_);
                    v_rev_3383_ = crate::leanh::lean_ctor_get(v_src_3341_, 1);
                    crate::leanh::lean_inc_ref(v_rev_3383_);
                    v_inputRev_x3f_3384_ = crate::leanh::lean_ctor_get(v_src_3341_, 2);
                    crate::leanh::lean_inc(v_inputRev_x3f_3384_);
                    v_subDir_x3f_3385_ = crate::leanh::lean_ctor_get(v_src_3341_, 3);
                    crate::leanh::lean_inc(v_subDir_x3f_3385_);
                    crate::leanh::lean_dec_ref_known(v_src_3341_, 4);
                    v___x_3386_ = l_Lake_PackageEntry_toJson___closed__7;
                    v___x_3387_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12;
                    v___x_3388_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3388_, 0, v_url_3382_);
                    v___x_3389_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3389_, 0, v___x_3387_);
                    crate::leanh::lean_ctor_set(v___x_3389_, 1, v___x_3388_);
                    v___x_3390_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14;
                    v___x_3391_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3391_, 0, v_rev_3383_);
                    v___x_3392_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3392_, 0, v___x_3390_);
                    crate::leanh::lean_ctor_set(v___x_3392_, 1, v___x_3391_);
                    v___x_3393_ = l_Lake_PackageEntry_toJson___closed__8;
                    v___x_3394_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__1(v_inputRev_x3f_3384_);
                    v___x_3395_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3395_, 0, v___x_3393_);
                    crate::leanh::lean_ctor_set(v___x_3395_, 1, v___x_3394_);
                    v___x_3396_ = l_Lake_PackageEntry_toJson___closed__9;
                    v___x_3397_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_subDir_x3f_3385_);
                    v___x_3398_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3398_, 0, v___x_3396_);
                    crate::leanh::lean_ctor_set(v___x_3398_, 1, v___x_3397_);
                    v___x_3399_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3399_, 0, v___x_3398_);
                    crate::leanh::lean_ctor_set(v___x_3399_, 1, v___x_3360_);
                    v___x_3400_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3400_, 0, v___x_3395_);
                    crate::leanh::lean_ctor_set(v___x_3400_, 1, v___x_3399_);
                    v___x_3401_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3401_, 0, v___x_3392_);
                    crate::leanh::lean_ctor_set(v___x_3401_, 1, v___x_3400_);
                    v___x_3402_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3402_, 0, v___x_3389_);
                    crate::leanh::lean_ctor_set(v___x_3402_, 1, v___x_3401_);
                    v___x_3403_ = l_List_appendTR___redArg(v_fields_3365_, v___x_3402_);
                    v___x_3404_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3404_, 0, v___x_3386_);
                    crate::leanh::lean_ctor_set(v___x_3404_, 1, v___x_3403_);
                    v___x_3405_ = l_Lean_Json_mkObj(v___x_3404_);
                    crate::leanh::lean_dec_ref_known(v___x_3404_, 2);
                    return v___x_3405_;
                }
            }
            1 => {
                v___x_3370_ = l_Lake_PackageEntry_toJson___closed__5;
                v___x_3371_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22;
                v___x_3372_ = l_Lake_mkRelPathString(v_dir_3366_);
                if v_isShared_3369_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3368_, 3);
                    crate::leanh::lean_ctor_set(v___x_3368_, 0, v___x_3372_);
                    v___x_3374_ = v___x_3368_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3380_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3372_);
                    v___x_3374_ = v_reuseFailAlloc_3380_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3375_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3375_, 0, v___x_3371_);
                crate::leanh::lean_ctor_set(v___x_3375_, 1, v___x_3374_);
                v___x_3376_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3376_, 0, v___x_3375_);
                crate::leanh::lean_ctor_set(v___x_3376_, 1, v___x_3360_);
                v___x_3377_ = l_List_appendTR___redArg(v_fields_3365_, v___x_3376_);
                v___x_3378_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3378_, 0, v___x_3370_);
                crate::leanh::lean_ctor_set(v___x_3378_, 1, v___x_3377_);
                v___x_3379_ = l_Lean_Json_mkObj(v___x_3378_);
                crate::leanh::lean_dec_ref_known(v___x_3378_, 2);
                return v___x_3379_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_PackageEntry_fromJson_x3f___lam__0(
    mut v_x_3409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3410_ = l_Lake_PackageEntry_fromJson_x3f___lam__0___closed__0;
    v___x_3411_ = lean_string_append(v___x_3410_, v_x_3409_);
    return v___x_3411_;
}
pub unsafe fn l_Lake_PackageEntry_fromJson_x3f___lam__0___boxed(
    mut v_x_3412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3413_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_x_3412_);
    crate::leanh::lean_dec_ref(v_x_3412_);
    return v_res_3413_;
}
pub unsafe fn l_Lake_PackageEntry_fromJson_x3f(
    mut v_json_3434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3443_: u8 = 0;
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3448_: u8 = 0;
    let mut v_a_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3452_: u8 = 0;
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3456_: u8 = 0;
    let mut v_a_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3460_: u8 = 0;
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3467_: u8 = 0;
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3476_: u8 = 0;
    let mut v_a_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: u8 = 0;
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3492_: u8 = 0;
    let mut v___y_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3506_: u8 = 0;
    let mut v___y_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3516_: u8 = 0;
    let mut v___y_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3533_: u8 = 0;
    let mut v___y_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: u8 = 0;
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: u8 = 0;
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3585_: u8 = 0;
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3589_: u8 = 0;
    let mut v___y_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3593_: u8 = 0;
    let mut v___y_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3598_: u8 = 0;
    let mut v___y_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3613_: u8 = 0;
    let mut v___y_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: u8 = 0;
    let mut v_val_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: u8 = 0;
    let mut v_val_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: u8 = 0;
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3660_: u8 = 0;
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3666_: u8 = 0;
    let mut v_a_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3670_: u8 = 0;
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3674_: u8 = 0;
    let mut v_a_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3677_: u8 = 0;
    let mut v_isSharedCheck_3678_: u8 = 0;
    let mut v_isSharedCheck_3679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3439_ = l_Lean_Json_getObj_x3f(v_json_3434_);
                if crate::leanh::lean_obj_tag(v___x_3439_) == 0 {
                    v_a_3440_ = crate::leanh::lean_ctor_get(v___x_3439_, 0);
                    v_isSharedCheck_3448_ = (!crate::leanh::lean_is_exclusive(v___x_3439_)) as u8;
                    if v_isSharedCheck_3448_ == 0 {
                        v___x_3442_ = v___x_3439_;
                        v_isShared_3443_ = v_isSharedCheck_3448_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3440_);
                        crate::leanh::lean_dec(v___x_3439_);
                        v___x_3442_ = crate::leanh::lean_box(0);
                        v_isShared_3443_ = v_isSharedCheck_3448_;
                        state = 2;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_3439_) == 0 {
                        v_a_3449_ = crate::leanh::lean_ctor_get(v___x_3439_, 0);
                        v_isSharedCheck_3456_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3439_)) as u8;
                        if v_isSharedCheck_3456_ == 0 {
                            v___x_3451_ = v___x_3439_;
                            v_isShared_3452_ = v_isSharedCheck_3456_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3449_);
                            crate::leanh::lean_dec(v___x_3439_);
                            v___x_3451_ = crate::leanh::lean_box(0);
                            v_isShared_3452_ = v_isSharedCheck_3456_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_3457_ = crate::leanh::lean_ctor_get(v___x_3439_, 0);
                        v_isSharedCheck_3679_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3439_)) as u8;
                        if v_isSharedCheck_3679_ == 0 {
                            v___x_3459_ = v___x_3439_;
                            v_isShared_3460_ = v_isSharedCheck_3679_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3457_);
                            crate::leanh::lean_dec(v___x_3439_);
                            v___x_3459_ = crate::leanh::lean_box(0);
                            v_isShared_3460_ = v_isSharedCheck_3679_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3437_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_a_3436_);
                crate::leanh::lean_dec_ref(v_a_3436_);
                v___x_3438_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3438_, 0, v___x_3437_);
                return v___x_3438_;
            }
            2 => {
                v___x_3444_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_a_3440_);
                crate::leanh::lean_dec(v_a_3440_);
                if v_isShared_3443_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3442_, 0, v___x_3444_);
                    v___x_3446_ = v___x_3442_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3447_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3444_);
                    v___x_3446_ = v_reuseFailAlloc_3447_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3446_;
            }
            4 => {
                if v_isShared_3452_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3451_, 0);
                    v___x_3454_ = v___x_3451_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3455_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
                    v___x_3454_ = v_reuseFailAlloc_3455_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3454_;
            }
            6 => {
                v___x_3461_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6;
                v___x_3462_ = l_Lake_JsonObject_getJson_x3f(v_a_3457_, v___x_3461_);
                if crate::leanh::lean_obj_tag(v___x_3462_) == 0 {
                    crate::leanh::lean_del_object(v___x_3459_);
                    crate::leanh::lean_dec(v_a_3457_);
                    v___x_3463_ = l_Lake_PackageEntry_fromJson_x3f___closed__0;
                    v_a_3436_ = v___x_3463_;
                    state = 1;
                    continue;
                } else {
                    v_val_3464_ = crate::leanh::lean_ctor_get(v___x_3462_, 0);
                    v_isSharedCheck_3678_ = (!crate::leanh::lean_is_exclusive(v___x_3462_)) as u8;
                    if v_isSharedCheck_3678_ == 0 {
                        v___x_3466_ = v___x_3462_;
                        v_isShared_3467_ = v_isSharedCheck_3678_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3464_);
                        crate::leanh::lean_dec(v___x_3462_);
                        v___x_3466_ = crate::leanh::lean_box(0);
                        v_isShared_3467_ = v_isSharedCheck_3678_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                v___x_3468_ = l_Lean_Name_fromJson_x3f(v_val_3464_);
                if crate::leanh::lean_obj_tag(v___x_3468_) == 0 {
                    crate::leanh::lean_del_object(v___x_3466_);
                    crate::leanh::lean_del_object(v___x_3459_);
                    crate::leanh::lean_dec(v_a_3457_);
                    v_a_3469_ = crate::leanh::lean_ctor_get(v___x_3468_, 0);
                    crate::leanh::lean_inc(v_a_3469_);
                    crate::leanh::lean_dec_ref_known(v___x_3468_, 1);
                    v___x_3470_ = l_Lake_PackageEntry_fromJson_x3f___closed__1;
                    v___x_3471_ = lean_string_append(v___x_3470_, v_a_3469_);
                    crate::leanh::lean_dec(v_a_3469_);
                    v_a_3436_ = v___x_3471_;
                    state = 1;
                    continue;
                } else {
                    if crate::leanh::lean_obj_tag(v___x_3468_) == 0 {
                        crate::leanh::lean_del_object(v___x_3466_);
                        crate::leanh::lean_del_object(v___x_3459_);
                        crate::leanh::lean_dec(v_a_3457_);
                        v_a_3472_ = crate::leanh::lean_ctor_get(v___x_3468_, 0);
                        crate::leanh::lean_inc(v_a_3472_);
                        crate::leanh::lean_dec_ref_known(v___x_3468_, 1);
                        v_a_3436_ = v_a_3472_;
                        state = 1;
                        continue;
                    } else {
                        v_a_3473_ = crate::leanh::lean_ctor_get(v___x_3468_, 0);
                        v_isSharedCheck_3677_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3468_)) as u8;
                        if v_isSharedCheck_3677_ == 0 {
                            v___x_3475_ = v___x_3468_;
                            v_isShared_3476_ = v_isSharedCheck_3677_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3473_);
                            crate::leanh::lean_dec(v___x_3468_);
                            v___x_3475_ = crate::leanh::lean_box(0);
                            v_isShared_3476_ = v_isSharedCheck_3677_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            8 => {
                v___x_3653_ = l_Lake_PackageEntry_toJson___closed__0;
                v___x_3654_ = l_Lake_JsonObject_getJson_x3f(v_a_3457_, v___x_3653_);
                if crate::leanh::lean_obj_tag(v___x_3654_) == 0 {
                    state = 23;
                    continue;
                } else {
                    v_val_3655_ = crate::leanh::lean_ctor_get(v___x_3654_, 0);
                    crate::leanh::lean_inc(v_val_3655_);
                    crate::leanh::lean_dec_ref_known(v___x_3654_, 1);
                    v___x_3656_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(v_val_3655_);
                    if crate::leanh::lean_obj_tag(v___x_3656_) == 0 {
                        crate::leanh::lean_del_object(v___x_3475_);
                        crate::leanh::lean_dec(v_a_3473_);
                        crate::leanh::lean_del_object(v___x_3466_);
                        crate::leanh::lean_del_object(v___x_3459_);
                        crate::leanh::lean_dec(v_a_3457_);
                        v_a_3657_ = crate::leanh::lean_ctor_get(v___x_3656_, 0);
                        v_isSharedCheck_3666_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3656_)) as u8;
                        if v_isSharedCheck_3666_ == 0 {
                            v___x_3659_ = v___x_3656_;
                            v_isShared_3660_ = v_isSharedCheck_3666_;
                            state = 24;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3657_);
                            crate::leanh::lean_dec(v___x_3656_);
                            v___x_3659_ = crate::leanh::lean_box(0);
                            v_isShared_3660_ = v_isSharedCheck_3666_;
                            state = 24;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_3656_) == 0 {
                            crate::leanh::lean_del_object(v___x_3475_);
                            crate::leanh::lean_dec(v_a_3473_);
                            crate::leanh::lean_del_object(v___x_3466_);
                            crate::leanh::lean_del_object(v___x_3459_);
                            crate::leanh::lean_dec(v_a_3457_);
                            v_a_3667_ = crate::leanh::lean_ctor_get(v___x_3656_, 0);
                            v_isSharedCheck_3674_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3656_)) as u8;
                            if v_isSharedCheck_3674_ == 0 {
                                v___x_3669_ = v___x_3656_;
                                v_isShared_3670_ = v_isSharedCheck_3674_;
                                state = 26;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3667_);
                                crate::leanh::lean_dec(v___x_3656_);
                                v___x_3669_ = crate::leanh::lean_box(0);
                                v_isShared_3670_ = v_isSharedCheck_3674_;
                                state = 26;
                                continue;
                            }
                        } else {
                            v_a_3675_ = crate::leanh::lean_ctor_get(v___x_3656_, 0);
                            crate::leanh::lean_inc(v_a_3675_);
                            crate::leanh::lean_dec_ref_known(v___x_3656_, 1);
                            if crate::leanh::lean_obj_tag(v_a_3675_) == 0 {
                                state = 23;
                                continue;
                            } else {
                                v_val_3676_ = crate::leanh::lean_ctor_get(v_a_3675_, 0);
                                crate::leanh::lean_inc(v_val_3676_);
                                crate::leanh::lean_dec_ref_known(v_a_3675_, 1);
                                v_a_3617_ = v_val_3676_;
                                state = 22;
                                continue;
                            }
                        }
                    }
                }
            }
            9 => {
                v___x_3479_ = l_Lake_PackageEntry_fromJson_x3f___closed__2;
                v___x_3480_ = 1;
                v___x_3481_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_a_3473_,
                    v___x_3480_,
                );
                v___x_3482_ = lean_string_append(v___x_3479_, v___x_3481_);
                crate::leanh::lean_dec_ref(v___x_3481_);
                v___x_3483_ = l_Lake_PackageEntry_fromJson_x3f___closed__3;
                v___x_3484_ = lean_string_append(v___x_3482_, v___x_3483_);
                v___x_3485_ = lean_string_append(v___x_3484_, v_a_3478_);
                crate::leanh::lean_dec_ref(v_a_3478_);
                if v_isShared_3476_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3475_, 0);
                    crate::leanh::lean_ctor_set(v___x_3475_, 0, v___x_3485_);
                    v___x_3487_ = v___x_3475_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3488_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3485_);
                    v___x_3487_ = v_reuseFailAlloc_3488_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3487_;
            }
            11 => {
                if v_isShared_3467_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3466_, 0, v___y_3493_);
                    v___x_3496_ = v___x_3466_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3501_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___y_3493_);
                    v___x_3496_ = v_reuseFailAlloc_3501_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_3497_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3497_, 0, v_a_3473_);
                crate::leanh::lean_ctor_set(v___x_3497_, 1, v___y_3491_);
                crate::leanh::lean_ctor_set(v___x_3497_, 2, v___y_3490_);
                crate::leanh::lean_ctor_set(v___x_3497_, 3, v___x_3496_);
                crate::leanh::lean_ctor_set(v___x_3497_, 4, v_a_3494_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3497_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_3492_,
                );
                if v_isShared_3460_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3459_, 0, v___x_3497_);
                    v___x_3499_ = v___x_3459_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3500_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3500_, 0, v___x_3497_);
                    v___x_3499_ = v_reuseFailAlloc_3500_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3499_;
            }
            14 => {
                v___x_3511_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3511_, 0, v___y_3508_);
                crate::leanh::lean_ctor_set(v___x_3511_, 1, v___y_3505_);
                crate::leanh::lean_ctor_set(v___x_3511_, 2, v___y_3509_);
                crate::leanh::lean_ctor_set(v___x_3511_, 3, v_a_3510_);
                v___y_3490_ = v___y_3503_;
                v___y_3491_ = v___y_3504_;
                v___y_3492_ = v___y_3506_;
                v___y_3493_ = v___y_3507_;
                v_a_3494_ = v___x_3511_;
                state = 11;
                continue;
            }
            15 => {
                v___x_3520_ = l_Lake_PackageEntry_toJson___closed__9;
                v___x_3521_ = l_Lake_JsonObject_getJson_x3f(v_a_3457_, v___x_3520_);
                crate::leanh::lean_dec(v_a_3457_);
                if crate::leanh::lean_obj_tag(v___x_3521_) == 0 {
                    crate::leanh::lean_del_object(v___x_3475_);
                    v___x_3522_ = crate::leanh::lean_box(0);
                    v___y_3503_ = v___y_3513_;
                    v___y_3504_ = v___y_3514_;
                    v___y_3505_ = v___y_3515_;
                    v___y_3506_ = v___y_3516_;
                    v___y_3507_ = v___y_3517_;
                    v___y_3508_ = v___y_3518_;
                    v___y_3509_ = v_a_3519_;
                    v_a_3510_ = v___x_3522_;
                    state = 14;
                    continue;
                } else {
                    v_val_3523_ = crate::leanh::lean_ctor_get(v___x_3521_, 0);
                    crate::leanh::lean_inc(v_val_3523_);
                    crate::leanh::lean_dec_ref_known(v___x_3521_, 1);
                    v___x_3524_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_3523_);
                    if crate::leanh::lean_obj_tag(v___x_3524_) == 0 {
                        crate::leanh::lean_dec(v_a_3519_);
                        crate::leanh::lean_dec_ref(v___y_3518_);
                        crate::leanh::lean_dec_ref(v___y_3517_);
                        crate::leanh::lean_dec_ref(v___y_3515_);
                        crate::leanh::lean_dec_ref(v___y_3514_);
                        crate::leanh::lean_dec_ref(v___y_3513_);
                        crate::leanh::lean_del_object(v___x_3466_);
                        crate::leanh::lean_del_object(v___x_3459_);
                        v_a_3525_ = crate::leanh::lean_ctor_get(v___x_3524_, 0);
                        crate::leanh::lean_inc(v_a_3525_);
                        crate::leanh::lean_dec_ref_known(v___x_3524_, 1);
                        v___x_3526_ = l_Lake_PackageEntry_fromJson_x3f___closed__4;
                        v___x_3527_ = lean_string_append(v___x_3526_, v_a_3525_);
                        crate::leanh::lean_dec(v_a_3525_);
                        v_a_3478_ = v___x_3527_;
                        state = 9;
                        continue;
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_3524_) == 0 {
                            crate::leanh::lean_dec(v_a_3519_);
                            crate::leanh::lean_dec_ref(v___y_3518_);
                            crate::leanh::lean_dec_ref(v___y_3517_);
                            crate::leanh::lean_dec_ref(v___y_3515_);
                            crate::leanh::lean_dec_ref(v___y_3514_);
                            crate::leanh::lean_dec_ref(v___y_3513_);
                            crate::leanh::lean_del_object(v___x_3466_);
                            crate::leanh::lean_del_object(v___x_3459_);
                            v_a_3528_ = crate::leanh::lean_ctor_get(v___x_3524_, 0);
                            crate::leanh::lean_inc(v_a_3528_);
                            crate::leanh::lean_dec_ref_known(v___x_3524_, 1);
                            v_a_3478_ = v_a_3528_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_3475_);
                            v_a_3529_ = crate::leanh::lean_ctor_get(v___x_3524_, 0);
                            crate::leanh::lean_inc(v_a_3529_);
                            crate::leanh::lean_dec_ref_known(v___x_3524_, 1);
                            v___y_3503_ = v___y_3513_;
                            v___y_3504_ = v___y_3514_;
                            v___y_3505_ = v___y_3515_;
                            v___y_3506_ = v___y_3516_;
                            v___y_3507_ = v___y_3517_;
                            v___y_3508_ = v___y_3518_;
                            v___y_3509_ = v_a_3519_;
                            v_a_3510_ = v_a_3529_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            16 => {
                v___x_3536_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2;
                v___x_3537_ = lean_string_dec_eq(v___y_3534_, v___x_3536_);
                if v___x_3537_ == 0 {
                    v___x_3538_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3;
                    v___x_3539_ = lean_string_dec_eq(v___y_3534_, v___x_3538_);
                    if v___x_3539_ == 0 {
                        crate::leanh::lean_dec_ref(v_a_3535_);
                        crate::leanh::lean_dec_ref(v___y_3532_);
                        crate::leanh::lean_dec_ref(v___y_3531_);
                        crate::leanh::lean_del_object(v___x_3466_);
                        crate::leanh::lean_del_object(v___x_3459_);
                        crate::leanh::lean_dec(v_a_3457_);
                        v___x_3540_ = l_Lake_PackageEntry_fromJson_x3f___closed__5;
                        v___x_3541_ = lean_string_append(v___x_3540_, v___y_3534_);
                        crate::leanh::lean_dec_ref(v___y_3534_);
                        v___x_3542_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2;
                        v___x_3543_ = lean_string_append(v___x_3541_, v___x_3542_);
                        v_a_3478_ = v___x_3543_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_3534_);
                        v___x_3544_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12;
                        v___x_3545_ = l_Lake_JsonObject_getJson_x3f(v_a_3457_, v___x_3544_);
                        if crate::leanh::lean_obj_tag(v___x_3545_) == 0 {
                            crate::leanh::lean_dec_ref(v_a_3535_);
                            crate::leanh::lean_dec_ref(v___y_3532_);
                            crate::leanh::lean_dec_ref(v___y_3531_);
                            crate::leanh::lean_del_object(v___x_3466_);
                            crate::leanh::lean_del_object(v___x_3459_);
                            crate::leanh::lean_dec(v_a_3457_);
                            v___x_3546_ = l_Lake_PackageEntry_fromJson_x3f___closed__6;
                            v_a_3478_ = v___x_3546_;
                            state = 9;
                            continue;
                        } else {
                            v_val_3547_ = crate::leanh::lean_ctor_get(v___x_3545_, 0);
                            crate::leanh::lean_inc(v_val_3547_);
                            crate::leanh::lean_dec_ref_known(v___x_3545_, 1);
                            v___x_3548_ = l_Lean_Json_getStr_x3f(v_val_3547_);
                            if crate::leanh::lean_obj_tag(v___x_3548_) == 0 {
                                crate::leanh::lean_dec_ref(v_a_3535_);
                                crate::leanh::lean_dec_ref(v___y_3532_);
                                crate::leanh::lean_dec_ref(v___y_3531_);
                                crate::leanh::lean_del_object(v___x_3466_);
                                crate::leanh::lean_del_object(v___x_3459_);
                                crate::leanh::lean_dec(v_a_3457_);
                                v_a_3549_ = crate::leanh::lean_ctor_get(v___x_3548_, 0);
                                crate::leanh::lean_inc(v_a_3549_);
                                crate::leanh::lean_dec_ref_known(v___x_3548_, 1);
                                v___x_3550_ = l_Lake_PackageEntry_fromJson_x3f___closed__7;
                                v___x_3551_ = lean_string_append(v___x_3550_, v_a_3549_);
                                crate::leanh::lean_dec(v_a_3549_);
                                v_a_3478_ = v___x_3551_;
                                state = 9;
                                continue;
                            } else {
                                if crate::leanh::lean_obj_tag(v___x_3548_) == 0 {
                                    crate::leanh::lean_dec_ref(v_a_3535_);
                                    crate::leanh::lean_dec_ref(v___y_3532_);
                                    crate::leanh::lean_dec_ref(v___y_3531_);
                                    crate::leanh::lean_del_object(v___x_3466_);
                                    crate::leanh::lean_del_object(v___x_3459_);
                                    crate::leanh::lean_dec(v_a_3457_);
                                    v_a_3552_ = crate::leanh::lean_ctor_get(v___x_3548_, 0);
                                    crate::leanh::lean_inc(v_a_3552_);
                                    crate::leanh::lean_dec_ref_known(v___x_3548_, 1);
                                    v_a_3478_ = v_a_3552_;
                                    state = 9;
                                    continue;
                                } else {
                                    v_a_3553_ = crate::leanh::lean_ctor_get(v___x_3548_, 0);
                                    crate::leanh::lean_inc(v_a_3553_);
                                    crate::leanh::lean_dec_ref_known(v___x_3548_, 1);
                                    v___x_3554_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14;
                                    v___x_3555_ =
                                        l_Lake_JsonObject_getJson_x3f(v_a_3457_, v___x_3554_);
                                    if crate::leanh::lean_obj_tag(v___x_3555_) == 0 {
                                        crate::leanh::lean_dec(v_a_3553_);
                                        crate::leanh::lean_dec_ref(v_a_3535_);
                                        crate::leanh::lean_dec_ref(v___y_3532_);
                                        crate::leanh::lean_dec_ref(v___y_3531_);
                                        crate::leanh::lean_del_object(v___x_3466_);
                                        crate::leanh::lean_del_object(v___x_3459_);
                                        crate::leanh::lean_dec(v_a_3457_);
                                        v___x_3556_ = l_Lake_PackageEntry_fromJson_x3f___closed__8;
                                        v_a_3478_ = v___x_3556_;
                                        state = 9;
                                        continue;
                                    } else {
                                        v_val_3557_ = crate::leanh::lean_ctor_get(v___x_3555_, 0);
                                        crate::leanh::lean_inc(v_val_3557_);
                                        crate::leanh::lean_dec_ref_known(v___x_3555_, 1);
                                        v___x_3558_ = l_Lean_Json_getStr_x3f(v_val_3557_);
                                        if crate::leanh::lean_obj_tag(v___x_3558_) == 0 {
                                            crate::leanh::lean_dec(v_a_3553_);
                                            crate::leanh::lean_dec_ref(v_a_3535_);
                                            crate::leanh::lean_dec_ref(v___y_3532_);
                                            crate::leanh::lean_dec_ref(v___y_3531_);
                                            crate::leanh::lean_del_object(v___x_3466_);
                                            crate::leanh::lean_del_object(v___x_3459_);
                                            crate::leanh::lean_dec(v_a_3457_);
                                            v_a_3559_ = crate::leanh::lean_ctor_get(v___x_3558_, 0);
                                            crate::leanh::lean_inc(v_a_3559_);
                                            crate::leanh::lean_dec_ref_known(v___x_3558_, 1);
                                            v___x_3560_ =
                                                l_Lake_PackageEntry_fromJson_x3f___closed__9;
                                            v___x_3561_ =
                                                lean_string_append(v___x_3560_, v_a_3559_);
                                            crate::leanh::lean_dec(v_a_3559_);
                                            v_a_3478_ = v___x_3561_;
                                            state = 9;
                                            continue;
                                        } else {
                                            if crate::leanh::lean_obj_tag(v___x_3558_) == 0 {
                                                crate::leanh::lean_dec(v_a_3553_);
                                                crate::leanh::lean_dec_ref(v_a_3535_);
                                                crate::leanh::lean_dec_ref(v___y_3532_);
                                                crate::leanh::lean_dec_ref(v___y_3531_);
                                                crate::leanh::lean_del_object(v___x_3466_);
                                                crate::leanh::lean_del_object(v___x_3459_);
                                                crate::leanh::lean_dec(v_a_3457_);
                                                v_a_3562_ =
                                                    crate::leanh::lean_ctor_get(v___x_3558_, 0);
                                                crate::leanh::lean_inc(v_a_3562_);
                                                crate::leanh::lean_dec_ref_known(v___x_3558_, 1);
                                                v_a_3478_ = v_a_3562_;
                                                state = 9;
                                                continue;
                                            } else {
                                                v_a_3563_ =
                                                    crate::leanh::lean_ctor_get(v___x_3558_, 0);
                                                crate::leanh::lean_inc(v_a_3563_);
                                                crate::leanh::lean_dec_ref_known(v___x_3558_, 1);
                                                v___x_3564_ =
                                                    l_Lake_PackageEntry_toJson___closed__8;
                                                v___x_3565_ = l_Lake_JsonObject_getJson_x3f(
                                                    v_a_3457_,
                                                    v___x_3564_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_3565_) == 0 {
                                                    v___x_3566_ = crate::leanh::lean_box(0);
                                                    v___y_3513_ = v___y_3531_;
                                                    v___y_3514_ = v___y_3532_;
                                                    v___y_3515_ = v_a_3563_;
                                                    v___y_3516_ = v___y_3533_;
                                                    v___y_3517_ = v_a_3535_;
                                                    v___y_3518_ = v_a_3553_;
                                                    v_a_3519_ = v___x_3566_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    v_val_3567_ =
                                                        crate::leanh::lean_ctor_get(v___x_3565_, 0);
                                                    crate::leanh::lean_inc(v_val_3567_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_3565_,
                                                        1,
                                                    );
                                                    v___x_3568_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(v_val_3567_);
                                                    if crate::leanh::lean_obj_tag(v___x_3568_) == 0
                                                    {
                                                        crate::leanh::lean_dec(v_a_3563_);
                                                        crate::leanh::lean_dec(v_a_3553_);
                                                        crate::leanh::lean_dec_ref(v_a_3535_);
                                                        crate::leanh::lean_dec_ref(v___y_3532_);
                                                        crate::leanh::lean_dec_ref(v___y_3531_);
                                                        crate::leanh::lean_del_object(v___x_3466_);
                                                        crate::leanh::lean_del_object(v___x_3459_);
                                                        crate::leanh::lean_dec(v_a_3457_);
                                                        v_a_3569_ = crate::leanh::lean_ctor_get(
                                                            v___x_3568_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_3569_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_3568_,
                                                            1,
                                                        );
                                                        v___x_3570_ = l_Lake_PackageEntry_fromJson_x3f___closed__10;
                                                        v___x_3571_ = lean_string_append(
                                                            v___x_3570_,
                                                            v_a_3569_,
                                                        );
                                                        crate::leanh::lean_dec(v_a_3569_);
                                                        v_a_3478_ = v___x_3571_;
                                                        state = 9;
                                                        continue;
                                                    } else {
                                                        if crate::leanh::lean_obj_tag(v___x_3568_)
                                                            == 0
                                                        {
                                                            crate::leanh::lean_dec(v_a_3563_);
                                                            crate::leanh::lean_dec(v_a_3553_);
                                                            crate::leanh::lean_dec_ref(v_a_3535_);
                                                            crate::leanh::lean_dec_ref(v___y_3532_);
                                                            crate::leanh::lean_dec_ref(v___y_3531_);
                                                            crate::leanh::lean_del_object(
                                                                v___x_3466_,
                                                            );
                                                            crate::leanh::lean_del_object(
                                                                v___x_3459_,
                                                            );
                                                            crate::leanh::lean_dec(v_a_3457_);
                                                            v_a_3572_ = crate::leanh::lean_ctor_get(
                                                                v___x_3568_,
                                                                0,
                                                            );
                                                            crate::leanh::lean_inc(v_a_3572_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_3568_,
                                                                1,
                                                            );
                                                            v_a_3478_ = v_a_3572_;
                                                            state = 9;
                                                            continue;
                                                        } else {
                                                            v_a_3573_ = crate::leanh::lean_ctor_get(
                                                                v___x_3568_,
                                                                0,
                                                            );
                                                            crate::leanh::lean_inc(v_a_3573_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_3568_,
                                                                1,
                                                            );
                                                            v___y_3513_ = v___y_3531_;
                                                            v___y_3514_ = v___y_3532_;
                                                            v___y_3515_ = v_a_3563_;
                                                            v___y_3516_ = v___y_3533_;
                                                            v___y_3517_ = v_a_3535_;
                                                            v___y_3518_ = v_a_3553_;
                                                            v_a_3519_ = v_a_3573_;
                                                            state = 15;
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
                } else {
                    crate::leanh::lean_dec_ref(v___y_3534_);
                    v___x_3574_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22;
                    v___x_3575_ = l_Lake_JsonObject_getJson_x3f(v_a_3457_, v___x_3574_);
                    crate::leanh::lean_dec(v_a_3457_);
                    if crate::leanh::lean_obj_tag(v___x_3575_) == 0 {
                        crate::leanh::lean_dec_ref(v_a_3535_);
                        crate::leanh::lean_dec_ref(v___y_3532_);
                        crate::leanh::lean_dec_ref(v___y_3531_);
                        crate::leanh::lean_del_object(v___x_3466_);
                        crate::leanh::lean_del_object(v___x_3459_);
                        v___x_3576_ = l_Lake_PackageEntry_fromJson_x3f___closed__11;
                        v_a_3478_ = v___x_3576_;
                        state = 9;
                        continue;
                    } else {
                        v_val_3577_ = crate::leanh::lean_ctor_get(v___x_3575_, 0);
                        crate::leanh::lean_inc(v_val_3577_);
                        crate::leanh::lean_dec_ref_known(v___x_3575_, 1);
                        v___x_3578_ = l_Lean_Json_getStr_x3f(v_val_3577_);
                        if crate::leanh::lean_obj_tag(v___x_3578_) == 0 {
                            crate::leanh::lean_dec_ref(v_a_3535_);
                            crate::leanh::lean_dec_ref(v___y_3532_);
                            crate::leanh::lean_dec_ref(v___y_3531_);
                            crate::leanh::lean_del_object(v___x_3466_);
                            crate::leanh::lean_del_object(v___x_3459_);
                            v_a_3579_ = crate::leanh::lean_ctor_get(v___x_3578_, 0);
                            crate::leanh::lean_inc(v_a_3579_);
                            crate::leanh::lean_dec_ref_known(v___x_3578_, 1);
                            v___x_3580_ = l_Lake_PackageEntry_fromJson_x3f___closed__12;
                            v___x_3581_ = lean_string_append(v___x_3580_, v_a_3579_);
                            crate::leanh::lean_dec(v_a_3579_);
                            v_a_3478_ = v___x_3581_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_3475_);
                            v_a_3582_ = crate::leanh::lean_ctor_get(v___x_3578_, 0);
                            v_isSharedCheck_3589_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3578_)) as u8;
                            if v_isSharedCheck_3589_ == 0 {
                                v___x_3584_ = v___x_3578_;
                                v_isShared_3585_ = v_isSharedCheck_3589_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3582_);
                                crate::leanh::lean_dec(v___x_3578_);
                                v___x_3584_ = crate::leanh::lean_box(0);
                                v_isShared_3585_ = v_isSharedCheck_3589_;
                                state = 17;
                                continue;
                            }
                        }
                    }
                }
            }
            17 => {
                if v_isShared_3585_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3584_, 0);
                    v___x_3587_ = v___x_3584_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3588_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3582_);
                    v___x_3587_ = v_reuseFailAlloc_3588_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___y_3490_ = v___y_3531_;
                v___y_3491_ = v___y_3532_;
                v___y_3492_ = v___y_3533_;
                v___y_3493_ = v_a_3535_;
                v_a_3494_ = v___x_3587_;
                state = 11;
                continue;
            }
            19 => {
                v___x_3595_ = l_Lake_defaultManifestFile;
                v___y_3531_ = v___y_3591_;
                v___y_3532_ = v___y_3592_;
                v___y_3533_ = v___y_3593_;
                v___y_3534_ = v___y_3594_;
                v_a_3535_ = v___x_3595_;
                state = 16;
                continue;
            }
            20 => {
                v___x_3601_ = l_Lake_PackageEntry_toJson___closed__2;
                v___x_3602_ = l_Lake_JsonObject_getJson_x3f(v_a_3457_, v___x_3601_);
                if crate::leanh::lean_obj_tag(v___x_3602_) == 0 {
                    v___y_3591_ = v_a_3600_;
                    v___y_3592_ = v___y_3597_;
                    v___y_3593_ = v___y_3598_;
                    v___y_3594_ = v___y_3599_;
                    state = 19;
                    continue;
                } else {
                    v_val_3603_ = crate::leanh::lean_ctor_get(v___x_3602_, 0);
                    crate::leanh::lean_inc(v_val_3603_);
                    crate::leanh::lean_dec_ref_known(v___x_3602_, 1);
                    v___x_3604_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_3603_);
                    if crate::leanh::lean_obj_tag(v___x_3604_) == 0 {
                        crate::leanh::lean_dec_ref(v_a_3600_);
                        crate::leanh::lean_dec_ref(v___y_3599_);
                        crate::leanh::lean_dec_ref(v___y_3597_);
                        crate::leanh::lean_del_object(v___x_3466_);
                        crate::leanh::lean_del_object(v___x_3459_);
                        crate::leanh::lean_dec(v_a_3457_);
                        v_a_3605_ = crate::leanh::lean_ctor_get(v___x_3604_, 0);
                        crate::leanh::lean_inc(v_a_3605_);
                        crate::leanh::lean_dec_ref_known(v___x_3604_, 1);
                        v___x_3606_ = l_Lake_PackageEntry_fromJson_x3f___closed__13;
                        v___x_3607_ = lean_string_append(v___x_3606_, v_a_3605_);
                        crate::leanh::lean_dec(v_a_3605_);
                        v_a_3478_ = v___x_3607_;
                        state = 9;
                        continue;
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_3604_) == 0 {
                            crate::leanh::lean_dec_ref(v_a_3600_);
                            crate::leanh::lean_dec_ref(v___y_3599_);
                            crate::leanh::lean_dec_ref(v___y_3597_);
                            crate::leanh::lean_del_object(v___x_3466_);
                            crate::leanh::lean_del_object(v___x_3459_);
                            crate::leanh::lean_dec(v_a_3457_);
                            v_a_3608_ = crate::leanh::lean_ctor_get(v___x_3604_, 0);
                            crate::leanh::lean_inc(v_a_3608_);
                            crate::leanh::lean_dec_ref_known(v___x_3604_, 1);
                            v_a_3478_ = v_a_3608_;
                            state = 9;
                            continue;
                        } else {
                            v_a_3609_ = crate::leanh::lean_ctor_get(v___x_3604_, 0);
                            crate::leanh::lean_inc(v_a_3609_);
                            crate::leanh::lean_dec_ref_known(v___x_3604_, 1);
                            if crate::leanh::lean_obj_tag(v_a_3609_) == 0 {
                                v___y_3591_ = v_a_3600_;
                                v___y_3592_ = v___y_3597_;
                                v___y_3593_ = v___y_3598_;
                                v___y_3594_ = v___y_3599_;
                                state = 19;
                                continue;
                            } else {
                                v_val_3610_ = crate::leanh::lean_ctor_get(v_a_3609_, 0);
                                crate::leanh::lean_inc(v_val_3610_);
                                crate::leanh::lean_dec_ref_known(v_a_3609_, 1);
                                v___y_3531_ = v_a_3600_;
                                v___y_3532_ = v___y_3597_;
                                v___y_3533_ = v___y_3598_;
                                v___y_3534_ = v___y_3599_;
                                v_a_3535_ = v_val_3610_;
                                state = 16;
                                continue;
                            }
                        }
                    }
                }
            }
            21 => {
                v___x_3615_ = l_Lake_defaultConfigFile;
                v___y_3597_ = v___y_3612_;
                v___y_3598_ = v___y_3613_;
                v___y_3599_ = v___y_3614_;
                v_a_3600_ = v___x_3615_;
                state = 20;
                continue;
            }
            22 => {
                v___x_3618_ = l_Lake_PackageEntry_toJson___closed__3;
                v___x_3619_ = l_Lake_JsonObject_getJson_x3f(v_a_3457_, v___x_3618_);
                if crate::leanh::lean_obj_tag(v___x_3619_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_3617_);
                    crate::leanh::lean_del_object(v___x_3466_);
                    crate::leanh::lean_del_object(v___x_3459_);
                    crate::leanh::lean_dec(v_a_3457_);
                    v___x_3620_ = l_Lake_PackageEntry_fromJson_x3f___closed__14;
                    v_a_3478_ = v___x_3620_;
                    state = 9;
                    continue;
                } else {
                    v_val_3621_ = crate::leanh::lean_ctor_get(v___x_3619_, 0);
                    crate::leanh::lean_inc(v_val_3621_);
                    crate::leanh::lean_dec_ref_known(v___x_3619_, 1);
                    v___x_3622_ = l_Lean_Json_getStr_x3f(v_val_3621_);
                    if crate::leanh::lean_obj_tag(v___x_3622_) == 0 {
                        crate::leanh::lean_dec_ref(v_a_3617_);
                        crate::leanh::lean_del_object(v___x_3466_);
                        crate::leanh::lean_del_object(v___x_3459_);
                        crate::leanh::lean_dec(v_a_3457_);
                        v_a_3623_ = crate::leanh::lean_ctor_get(v___x_3622_, 0);
                        crate::leanh::lean_inc(v_a_3623_);
                        crate::leanh::lean_dec_ref_known(v___x_3622_, 1);
                        v___x_3624_ = l_Lake_PackageEntry_fromJson_x3f___closed__15;
                        v___x_3625_ = lean_string_append(v___x_3624_, v_a_3623_);
                        crate::leanh::lean_dec(v_a_3623_);
                        v_a_3478_ = v___x_3625_;
                        state = 9;
                        continue;
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_3622_) == 0 {
                            crate::leanh::lean_dec_ref(v_a_3617_);
                            crate::leanh::lean_del_object(v___x_3466_);
                            crate::leanh::lean_del_object(v___x_3459_);
                            crate::leanh::lean_dec(v_a_3457_);
                            v_a_3626_ = crate::leanh::lean_ctor_get(v___x_3622_, 0);
                            crate::leanh::lean_inc(v_a_3626_);
                            crate::leanh::lean_dec_ref_known(v___x_3622_, 1);
                            v_a_3478_ = v_a_3626_;
                            state = 9;
                            continue;
                        } else {
                            v_a_3627_ = crate::leanh::lean_ctor_get(v___x_3622_, 0);
                            crate::leanh::lean_inc(v_a_3627_);
                            crate::leanh::lean_dec_ref_known(v___x_3622_, 1);
                            v___x_3628_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10;
                            v___x_3629_ = l_Lake_JsonObject_getJson_x3f(v_a_3457_, v___x_3628_);
                            if crate::leanh::lean_obj_tag(v___x_3629_) == 0 {
                                crate::leanh::lean_dec(v_a_3627_);
                                crate::leanh::lean_dec_ref(v_a_3617_);
                                crate::leanh::lean_del_object(v___x_3466_);
                                crate::leanh::lean_del_object(v___x_3459_);
                                crate::leanh::lean_dec(v_a_3457_);
                                v___x_3630_ = l_Lake_PackageEntry_fromJson_x3f___closed__16;
                                v_a_3478_ = v___x_3630_;
                                state = 9;
                                continue;
                            } else {
                                v_val_3631_ = crate::leanh::lean_ctor_get(v___x_3629_, 0);
                                crate::leanh::lean_inc(v_val_3631_);
                                crate::leanh::lean_dec_ref_known(v___x_3629_, 1);
                                v___x_3632_ = l_Lean_Json_getBool_x3f(v_val_3631_);
                                crate::leanh::lean_dec(v_val_3631_);
                                if crate::leanh::lean_obj_tag(v___x_3632_) == 0 {
                                    crate::leanh::lean_dec(v_a_3627_);
                                    crate::leanh::lean_dec_ref(v_a_3617_);
                                    crate::leanh::lean_del_object(v___x_3466_);
                                    crate::leanh::lean_del_object(v___x_3459_);
                                    crate::leanh::lean_dec(v_a_3457_);
                                    v_a_3633_ = crate::leanh::lean_ctor_get(v___x_3632_, 0);
                                    crate::leanh::lean_inc(v_a_3633_);
                                    crate::leanh::lean_dec_ref_known(v___x_3632_, 1);
                                    v___x_3634_ = l_Lake_PackageEntry_fromJson_x3f___closed__17;
                                    v___x_3635_ = lean_string_append(v___x_3634_, v_a_3633_);
                                    crate::leanh::lean_dec(v_a_3633_);
                                    v_a_3478_ = v___x_3635_;
                                    state = 9;
                                    continue;
                                } else {
                                    if crate::leanh::lean_obj_tag(v___x_3632_) == 0 {
                                        crate::leanh::lean_dec(v_a_3627_);
                                        crate::leanh::lean_dec_ref(v_a_3617_);
                                        crate::leanh::lean_del_object(v___x_3466_);
                                        crate::leanh::lean_del_object(v___x_3459_);
                                        crate::leanh::lean_dec(v_a_3457_);
                                        v_a_3636_ = crate::leanh::lean_ctor_get(v___x_3632_, 0);
                                        crate::leanh::lean_inc(v_a_3636_);
                                        crate::leanh::lean_dec_ref_known(v___x_3632_, 1);
                                        v_a_3478_ = v_a_3636_;
                                        state = 9;
                                        continue;
                                    } else {
                                        v_a_3637_ = crate::leanh::lean_ctor_get(v___x_3632_, 0);
                                        crate::leanh::lean_inc(v_a_3637_);
                                        crate::leanh::lean_dec_ref_known(v___x_3632_, 1);
                                        v___x_3638_ = l_Lake_PackageEntry_toJson___closed__1;
                                        v___x_3639_ =
                                            l_Lake_JsonObject_getJson_x3f(v_a_3457_, v___x_3638_);
                                        if crate::leanh::lean_obj_tag(v___x_3639_) == 0 {
                                            v___x_3640_ =
                                                (crate::leanh::lean_unbox(v_a_3637_) as u8);
                                            crate::leanh::lean_dec(v_a_3637_);
                                            v___y_3612_ = v_a_3617_;
                                            v___y_3613_ = v___x_3640_;
                                            v___y_3614_ = v_a_3627_;
                                            state = 21;
                                            continue;
                                        } else {
                                            v_val_3641_ =
                                                crate::leanh::lean_ctor_get(v___x_3639_, 0);
                                            crate::leanh::lean_inc(v_val_3641_);
                                            crate::leanh::lean_dec_ref_known(v___x_3639_, 1);
                                            v___x_3642_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_3641_);
                                            if crate::leanh::lean_obj_tag(v___x_3642_) == 0 {
                                                crate::leanh::lean_dec(v_a_3637_);
                                                crate::leanh::lean_dec(v_a_3627_);
                                                crate::leanh::lean_dec_ref(v_a_3617_);
                                                crate::leanh::lean_del_object(v___x_3466_);
                                                crate::leanh::lean_del_object(v___x_3459_);
                                                crate::leanh::lean_dec(v_a_3457_);
                                                v_a_3643_ =
                                                    crate::leanh::lean_ctor_get(v___x_3642_, 0);
                                                crate::leanh::lean_inc(v_a_3643_);
                                                crate::leanh::lean_dec_ref_known(v___x_3642_, 1);
                                                v___x_3644_ =
                                                    l_Lake_PackageEntry_fromJson_x3f___closed__18;
                                                v___x_3645_ =
                                                    lean_string_append(v___x_3644_, v_a_3643_);
                                                crate::leanh::lean_dec(v_a_3643_);
                                                v_a_3478_ = v___x_3645_;
                                                state = 9;
                                                continue;
                                            } else {
                                                if crate::leanh::lean_obj_tag(v___x_3642_) == 0 {
                                                    crate::leanh::lean_dec(v_a_3637_);
                                                    crate::leanh::lean_dec(v_a_3627_);
                                                    crate::leanh::lean_dec_ref(v_a_3617_);
                                                    crate::leanh::lean_del_object(v___x_3466_);
                                                    crate::leanh::lean_del_object(v___x_3459_);
                                                    crate::leanh::lean_dec(v_a_3457_);
                                                    v_a_3646_ =
                                                        crate::leanh::lean_ctor_get(v___x_3642_, 0);
                                                    crate::leanh::lean_inc(v_a_3646_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_3642_,
                                                        1,
                                                    );
                                                    v_a_3478_ = v_a_3646_;
                                                    state = 9;
                                                    continue;
                                                } else {
                                                    v_a_3647_ =
                                                        crate::leanh::lean_ctor_get(v___x_3642_, 0);
                                                    crate::leanh::lean_inc(v_a_3647_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_3642_,
                                                        1,
                                                    );
                                                    if crate::leanh::lean_obj_tag(v_a_3647_) == 0 {
                                                        v___x_3648_ =
                                                            (crate::leanh::lean_unbox(v_a_3637_)
                                                                as u8);
                                                        crate::leanh::lean_dec(v_a_3637_);
                                                        v___y_3612_ = v_a_3617_;
                                                        v___y_3613_ = v___x_3648_;
                                                        v___y_3614_ = v_a_3627_;
                                                        state = 21;
                                                        continue;
                                                    } else {
                                                        v_val_3649_ = crate::leanh::lean_ctor_get(
                                                            v_a_3647_, 0,
                                                        );
                                                        crate::leanh::lean_inc(v_val_3649_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_a_3647_, 1,
                                                        );
                                                        v___x_3650_ =
                                                            (crate::leanh::lean_unbox(v_a_3637_)
                                                                as u8);
                                                        crate::leanh::lean_dec(v_a_3637_);
                                                        v___y_3597_ = v_a_3617_;
                                                        v___y_3598_ = v___x_3650_;
                                                        v___y_3599_ = v_a_3627_;
                                                        v_a_3600_ = v_val_3649_;
                                                        state = 20;
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
            }
            23 => {
                v___x_3652_ = l_Lake_Manifest_version___closed__1;
                v_a_3617_ = v___x_3652_;
                state = 22;
                continue;
            }
            24 => {
                v___x_3661_ = l_Lake_PackageEntry_fromJson_x3f___closed__19;
                v___x_3662_ = lean_string_append(v___x_3661_, v_a_3657_);
                crate::leanh::lean_dec(v_a_3657_);
                if v_isShared_3660_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3659_, 0, v___x_3662_);
                    v___x_3664_ = v___x_3659_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3665_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3662_);
                    v___x_3664_ = v_reuseFailAlloc_3665_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3664_;
            }
            26 => {
                if v_isShared_3670_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3669_, 0);
                    v___x_3672_ = v___x_3669_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3673_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3667_);
                    v___x_3672_ = v_reuseFailAlloc_3673_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_3672_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_PackageEntry_setInherited(
    mut v_entry_3682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scope_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_configFile_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_manifestFile_x3f_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_src_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3690_: u8 = 0;
    let mut v___x_3691_: u8 = 0;
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3695_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_3683_ = crate::leanh::lean_ctor_get(v_entry_3682_, 0);
                v_scope_3684_ = crate::leanh::lean_ctor_get(v_entry_3682_, 1);
                v_configFile_3685_ = crate::leanh::lean_ctor_get(v_entry_3682_, 2);
                v_manifestFile_x3f_3686_ = crate::leanh::lean_ctor_get(v_entry_3682_, 3);
                v_src_3687_ = crate::leanh::lean_ctor_get(v_entry_3682_, 4);
                v_isSharedCheck_3695_ = (!crate::leanh::lean_is_exclusive(v_entry_3682_)) as u8;
                if v_isSharedCheck_3695_ == 0 {
                    v___x_3689_ = v_entry_3682_;
                    v_isShared_3690_ = v_isSharedCheck_3695_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_src_3687_);
                    crate::leanh::lean_inc(v_manifestFile_x3f_3686_);
                    crate::leanh::lean_inc(v_configFile_3685_);
                    crate::leanh::lean_inc(v_scope_3684_);
                    crate::leanh::lean_inc(v_name_3683_);
                    crate::leanh::lean_dec(v_entry_3682_);
                    v___x_3689_ = crate::leanh::lean_box(0);
                    v_isShared_3690_ = v_isSharedCheck_3695_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3691_ = 1;
                if v_isShared_3690_ == 0 {
                    v___x_3693_ = v___x_3689_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3694_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_name_3683_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3694_, 1, v_scope_3684_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3694_, 2, v_configFile_3685_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3694_,
                        3,
                        v_manifestFile_x3f_3686_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3694_, 4, v_src_3687_);
                    v___x_3693_ = v_reuseFailAlloc_3694_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3693_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___x_3691_,
                );
                return v___x_3693_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_PackageEntry_setConfigFile(
    mut v_path_3696_: *mut crate::leanh::LeanObject,
    mut v_entry_3697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scope_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inherited_3700_: u8 = 0;
    let mut v_manifestFile_x3f_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_src_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3705_: u8 = 0;
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3709_: u8 = 0;
    let mut v_unused_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_3698_ = crate::leanh::lean_ctor_get(v_entry_3697_, 0);
                v_scope_3699_ = crate::leanh::lean_ctor_get(v_entry_3697_, 1);
                v_inherited_3700_ = crate::leanh::lean_ctor_get_uint8(
                    v_entry_3697_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                );
                v_manifestFile_x3f_3701_ = crate::leanh::lean_ctor_get(v_entry_3697_, 3);
                v_src_3702_ = crate::leanh::lean_ctor_get(v_entry_3697_, 4);
                v_isSharedCheck_3709_ = (!crate::leanh::lean_is_exclusive(v_entry_3697_)) as u8;
                if v_isSharedCheck_3709_ == 0 {
                    v_unused_3710_ = crate::leanh::lean_ctor_get(v_entry_3697_, 2);
                    crate::leanh::lean_dec(v_unused_3710_);
                    v___x_3704_ = v_entry_3697_;
                    v_isShared_3705_ = v_isSharedCheck_3709_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_src_3702_);
                    crate::leanh::lean_inc(v_manifestFile_x3f_3701_);
                    crate::leanh::lean_inc(v_scope_3699_);
                    crate::leanh::lean_inc(v_name_3698_);
                    crate::leanh::lean_dec(v_entry_3697_);
                    v___x_3704_ = crate::leanh::lean_box(0);
                    v_isShared_3705_ = v_isSharedCheck_3709_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3705_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3704_, 2, v_path_3696_);
                    v___x_3707_ = v___x_3704_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3708_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_name_3698_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3708_, 1, v_scope_3699_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3708_, 2, v_path_3696_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3708_,
                        3,
                        v_manifestFile_x3f_3701_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3708_, 4, v_src_3702_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3708_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                        v_inherited_3700_,
                    );
                    v___x_3707_ = v_reuseFailAlloc_3708_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3707_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_PackageEntry_setManifestFile(
    mut v_path_x3f_3711_: *mut crate::leanh::LeanObject,
    mut v_entry_3712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scope_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inherited_3715_: u8 = 0;
    let mut v_configFile_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_src_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3720_: u8 = 0;
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3724_: u8 = 0;
    let mut v_unused_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_3713_ = crate::leanh::lean_ctor_get(v_entry_3712_, 0);
                v_scope_3714_ = crate::leanh::lean_ctor_get(v_entry_3712_, 1);
                v_inherited_3715_ = crate::leanh::lean_ctor_get_uint8(
                    v_entry_3712_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                );
                v_configFile_3716_ = crate::leanh::lean_ctor_get(v_entry_3712_, 2);
                v_src_3717_ = crate::leanh::lean_ctor_get(v_entry_3712_, 4);
                v_isSharedCheck_3724_ = (!crate::leanh::lean_is_exclusive(v_entry_3712_)) as u8;
                if v_isSharedCheck_3724_ == 0 {
                    v_unused_3725_ = crate::leanh::lean_ctor_get(v_entry_3712_, 3);
                    crate::leanh::lean_dec(v_unused_3725_);
                    v___x_3719_ = v_entry_3712_;
                    v_isShared_3720_ = v_isSharedCheck_3724_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_src_3717_);
                    crate::leanh::lean_inc(v_configFile_3716_);
                    crate::leanh::lean_inc(v_scope_3714_);
                    crate::leanh::lean_inc(v_name_3713_);
                    crate::leanh::lean_dec(v_entry_3712_);
                    v___x_3719_ = crate::leanh::lean_box(0);
                    v_isShared_3720_ = v_isSharedCheck_3724_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3720_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3719_, 3, v_path_x3f_3711_);
                    v___x_3722_ = v___x_3719_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3723_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_name_3713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3723_, 1, v_scope_3714_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3723_, 2, v_configFile_3716_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3723_, 3, v_path_x3f_3711_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3723_, 4, v_src_3717_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3723_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                        v_inherited_3715_,
                    );
                    v___x_3722_ = v_reuseFailAlloc_3723_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3722_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_PackageEntry_inDirectory(
    mut v_pkgDir_3726_: *mut crate::leanh::LeanObject,
    mut v_entry_3727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_src_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scope_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inherited_3731_: u8 = 0;
    let mut v_configFile_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_manifestFile_x3f_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3736_: u8 = 0;
    let mut v_dir_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3740_: u8 = 0;
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3748_: u8 = 0;
    let mut v_isSharedCheck_3749_: u8 = 0;
    let mut v_unused_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_src_3728_ = crate::leanh::lean_ctor_get(v_entry_3727_, 4);
                crate::leanh::lean_inc_ref(v_src_3728_);
                if crate::leanh::lean_obj_tag(v_src_3728_) == 0 {
                    v_name_3729_ = crate::leanh::lean_ctor_get(v_entry_3727_, 0);
                    v_scope_3730_ = crate::leanh::lean_ctor_get(v_entry_3727_, 1);
                    v_inherited_3731_ = crate::leanh::lean_ctor_get_uint8(
                        v_entry_3727_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    );
                    v_configFile_3732_ = crate::leanh::lean_ctor_get(v_entry_3727_, 2);
                    v_manifestFile_x3f_3733_ = crate::leanh::lean_ctor_get(v_entry_3727_, 3);
                    v_isSharedCheck_3749_ = (!crate::leanh::lean_is_exclusive(v_entry_3727_)) as u8;
                    if v_isSharedCheck_3749_ == 0 {
                        v_unused_3750_ = crate::leanh::lean_ctor_get(v_entry_3727_, 4);
                        crate::leanh::lean_dec(v_unused_3750_);
                        v___x_3735_ = v_entry_3727_;
                        v_isShared_3736_ = v_isSharedCheck_3749_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_manifestFile_x3f_3733_);
                        crate::leanh::lean_inc(v_configFile_3732_);
                        crate::leanh::lean_inc(v_scope_3730_);
                        crate::leanh::lean_inc(v_name_3729_);
                        crate::leanh::lean_dec(v_entry_3727_);
                        v___x_3735_ = crate::leanh::lean_box(0);
                        v_isShared_3736_ = v_isSharedCheck_3749_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_src_3728_);
                    crate::leanh::lean_dec_ref(v_pkgDir_3726_);
                    return v_entry_3727_;
                }
            }
            1 => {
                v_dir_3737_ = crate::leanh::lean_ctor_get(v_src_3728_, 0);
                v_isSharedCheck_3748_ = (!crate::leanh::lean_is_exclusive(v_src_3728_)) as u8;
                if v_isSharedCheck_3748_ == 0 {
                    v___x_3739_ = v_src_3728_;
                    v_isShared_3740_ = v_isSharedCheck_3748_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dir_3737_);
                    crate::leanh::lean_dec(v_src_3728_);
                    v___x_3739_ = crate::leanh::lean_box(0);
                    v_isShared_3740_ = v_isSharedCheck_3748_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3741_ = l_Lake_joinRelative(v_pkgDir_3726_, v_dir_3737_);
                if v_isShared_3740_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3739_, 0, v___x_3741_);
                    v___x_3743_ = v___x_3739_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3747_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3741_);
                    v___x_3743_ = v_reuseFailAlloc_3747_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3736_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3735_, 4, v___x_3743_);
                    v___x_3745_ = v___x_3735_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3746_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_name_3729_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3746_, 1, v_scope_3730_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3746_, 2, v_configFile_3732_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3746_,
                        3,
                        v_manifestFile_x3f_3733_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3746_, 4, v___x_3743_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3746_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                        v_inherited_3731_,
                    );
                    v___x_3745_ = v_reuseFailAlloc_3746_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3745_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(
    mut v_x_3751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3751_) == 0 {
        let mut v_name_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_inherited_3753_: u8 = 0;
        let mut v_dir_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_name_3752_ = crate::leanh::lean_ctor_get(v_x_3751_, 0);
        v_inherited_3753_ = crate::leanh::lean_ctor_get_uint8(
            v_x_3751_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        );
        v_dir_3754_ = crate::leanh::lean_ctor_get(v_x_3751_, 2);
        v___x_3755_ = l_Lake_Manifest_version___closed__1;
        v___x_3756_ = l_Lake_defaultConfigFile;
        v___x_3757_ = crate::leanh::lean_box(0);
        crate::leanh::lean_inc_ref(v_dir_3754_);
        v___x_3758_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3758_, 0, v_dir_3754_);
        crate::leanh::lean_inc(v_name_3752_);
        v___x_3759_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_3759_, 0, v_name_3752_);
        crate::leanh::lean_ctor_set(v___x_3759_, 1, v___x_3755_);
        crate::leanh::lean_ctor_set(v___x_3759_, 2, v___x_3756_);
        crate::leanh::lean_ctor_set(v___x_3759_, 3, v___x_3757_);
        crate::leanh::lean_ctor_set(v___x_3759_, 4, v___x_3758_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_3759_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
            v_inherited_3753_,
        );
        return v___x_3759_;
    } else {
        let mut v_name_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_inherited_3761_: u8 = 0;
        let mut v_url_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rev_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_inputRev_x3f_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_subDir_x3f_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_name_3760_ = crate::leanh::lean_ctor_get(v_x_3751_, 0);
        v_inherited_3761_ = crate::leanh::lean_ctor_get_uint8(
            v_x_3751_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
        );
        v_url_3762_ = crate::leanh::lean_ctor_get(v_x_3751_, 2);
        v_rev_3763_ = crate::leanh::lean_ctor_get(v_x_3751_, 3);
        v_inputRev_x3f_3764_ = crate::leanh::lean_ctor_get(v_x_3751_, 4);
        v_subDir_x3f_3765_ = crate::leanh::lean_ctor_get(v_x_3751_, 5);
        v___x_3766_ = l_Lake_Manifest_version___closed__1;
        v___x_3767_ = l_Lake_defaultConfigFile;
        v___x_3768_ = crate::leanh::lean_box(0);
        crate::leanh::lean_inc(v_subDir_x3f_3765_);
        crate::leanh::lean_inc(v_inputRev_x3f_3764_);
        crate::leanh::lean_inc_ref(v_rev_3763_);
        crate::leanh::lean_inc_ref(v_url_3762_);
        v___x_3769_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3769_, 0, v_url_3762_);
        crate::leanh::lean_ctor_set(v___x_3769_, 1, v_rev_3763_);
        crate::leanh::lean_ctor_set(v___x_3769_, 2, v_inputRev_x3f_3764_);
        crate::leanh::lean_ctor_set(v___x_3769_, 3, v_subDir_x3f_3765_);
        crate::leanh::lean_inc(v_name_3760_);
        v___x_3770_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_3770_, 0, v_name_3760_);
        crate::leanh::lean_ctor_set(v___x_3770_, 1, v___x_3766_);
        crate::leanh::lean_ctor_set(v___x_3770_, 2, v___x_3767_);
        crate::leanh::lean_ctor_set(v___x_3770_, 3, v___x_3768_);
        crate::leanh::lean_ctor_set(v___x_3770_, 4, v___x_3769_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_3770_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
            v_inherited_3761_,
        );
        return v___x_3770_;
    }
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6___boxed(
    mut v_x_3771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3772_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(v_x_3771_);
    crate::leanh::lean_dec_ref(v_x_3771_);
    return v_res_3772_;
}
pub unsafe fn l_Lake_Manifest_addPackage(
    mut v_entry_3773_: *mut crate::leanh::LeanObject,
    mut v_self_3774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeDir_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fixedToolchain_3777_: u8 = 0;
    let mut v_packagesDir_x3f_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packages_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3782_: u8 = 0;
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3787_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_3775_ = crate::leanh::lean_ctor_get(v_self_3774_, 0);
                v_lakeDir_3776_ = crate::leanh::lean_ctor_get(v_self_3774_, 1);
                v_fixedToolchain_3777_ = crate::leanh::lean_ctor_get_uint8(
                    v_self_3774_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                );
                v_packagesDir_x3f_3778_ = crate::leanh::lean_ctor_get(v_self_3774_, 2);
                v_packages_3779_ = crate::leanh::lean_ctor_get(v_self_3774_, 3);
                v_isSharedCheck_3787_ = (!crate::leanh::lean_is_exclusive(v_self_3774_)) as u8;
                if v_isSharedCheck_3787_ == 0 {
                    v___x_3781_ = v_self_3774_;
                    v_isShared_3782_ = v_isSharedCheck_3787_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_packages_3779_);
                    crate::leanh::lean_inc(v_packagesDir_x3f_3778_);
                    crate::leanh::lean_inc(v_lakeDir_3776_);
                    crate::leanh::lean_inc(v_name_3775_);
                    crate::leanh::lean_dec(v_self_3774_);
                    v___x_3781_ = crate::leanh::lean_box(0);
                    v_isShared_3782_ = v_isSharedCheck_3787_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3783_ = lean_array_push(v_packages_3779_, v_entry_3773_);
                if v_isShared_3782_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3781_, 3, v___x_3783_);
                    v___x_3785_ = v___x_3781_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3786_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_name_3775_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3786_, 1, v_lakeDir_3776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3786_, 2, v_packagesDir_x3f_3778_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3786_, 3, v___x_3783_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3786_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v_fixedToolchain_3777_,
                    );
                    v___x_3785_ = v_reuseFailAlloc_3786_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3785_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(
    mut v_sz_3788_: usize,
    mut v_i_3789_: usize,
    mut v_bs_3790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3791_: u8 = 0;
    let mut v_v_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: usize = 0;
    let mut v___x_3797_: usize = 0;
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3791_ = lean_usize_dec_lt(v_i_3789_, v_sz_3788_);
                if v___x_3791_ == 0 {
                    return v_bs_3790_;
                } else {
                    v_v_3792_ = lean_array_uget(v_bs_3790_, v_i_3789_);
                    v___x_3793_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3794_ = lean_array_uset(v_bs_3790_, v_i_3789_, v___x_3793_);
                    v___x_3795_ = l_Lake_PackageEntry_toJson(v_v_3792_);
                    v___x_3796_ = 1usize;
                    v___x_3797_ = lean_usize_add(v_i_3789_, v___x_3796_);
                    v___x_3798_ = lean_array_uset(v_bs_x27_3794_, v_i_3789_, v___x_3795_);
                    v_i_3789_ = v___x_3797_;
                    v_bs_3790_ = v___x_3798_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0___boxed(
    mut v_sz_3800_: *mut crate::leanh::LeanObject,
    mut v_i_3801_: *mut crate::leanh::LeanObject,
    mut v_bs_3802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3803_: usize = 0;
    let mut v_i_boxed_3804_: usize = 0;
    let mut v_res_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3803_ = crate::leanh::lean_unbox_usize(v_sz_3800_);
    crate::leanh::lean_dec(v_sz_3800_);
    v_i_boxed_3804_ = crate::leanh::lean_unbox_usize(v_i_3801_);
    crate::leanh::lean_dec(v_i_3801_);
    v_res_3805_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(v_sz_boxed_3803_, v_i_boxed_3804_, v_bs_3802_);
    return v_res_3805_;
}
pub unsafe fn l_Array_toJson___at___00Lake_Manifest_toJson_spec__0(
    mut v_a_3806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_3807_: usize = 0;
    let mut v___x_3808_: usize = 0;
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_3807_ = lean_array_size(v_a_3806_);
    v___x_3808_ = 0usize;
    v___x_3809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(v_sz_3807_, v___x_3808_, v_a_3806_);
    v___x_3810_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3810_, 0, v___x_3809_);
    return v___x_3810_;
}
pub unsafe fn _init_l_Lake_Manifest_toJson___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3812_ = l_Lake_Manifest_version___closed__2;
    v___x_3813_ = l_Lake_StdVer_toString(v___x_3812_);
    return v___x_3813_;
}
pub unsafe fn _init_l_Lake_Manifest_toJson___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3814_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Manifest_toJson___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Manifest_toJson___closed__1_once),
        _init_l_Lake_Manifest_toJson___closed__1,
    );
    v___x_3815_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3815_, 0, v___x_3814_);
    return v___x_3815_;
}
pub unsafe fn _init_l_Lake_Manifest_toJson___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3816_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Manifest_toJson___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Manifest_toJson___closed__2_once),
        _init_l_Lake_Manifest_toJson___closed__2,
    );
    v___x_3817_ = l_Lake_Manifest_toJson___closed__0;
    v___x_3818_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3818_, 0, v___x_3817_);
    crate::leanh::lean_ctor_set(v___x_3818_, 1, v___x_3816_);
    return v___x_3818_;
}
pub unsafe fn l_Lake_Manifest_toJson(
    mut v_self_3823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeDir_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fixedToolchain_3826_: u8 = 0;
    let mut v_packagesDir_x3f_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packages_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: u8 = 0;
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_3824_ = crate::leanh::lean_ctor_get(v_self_3823_, 0);
    crate::leanh::lean_inc(v_name_3824_);
    v_lakeDir_3825_ = crate::leanh::lean_ctor_get(v_self_3823_, 1);
    crate::leanh::lean_inc_ref(v_lakeDir_3825_);
    v_fixedToolchain_3826_ = crate::leanh::lean_ctor_get_uint8(
        v_self_3823_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
    );
    v_packagesDir_x3f_3827_ = crate::leanh::lean_ctor_get(v_self_3823_, 2);
    crate::leanh::lean_inc(v_packagesDir_x3f_3827_);
    v_packages_3828_ = crate::leanh::lean_ctor_get(v_self_3823_, 3);
    crate::leanh::lean_inc_ref(v_packages_3828_);
    crate::leanh::lean_dec_ref(v_self_3823_);
    v___x_3829_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Manifest_toJson___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Manifest_toJson___closed__3_once),
        _init_l_Lake_Manifest_toJson___closed__3,
    );
    v___x_3830_ = l_Lake_Manifest_toJson___closed__4;
    v___x_3831_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
    crate::leanh::lean_ctor_set_uint8(v___x_3831_, 0 as u32, v_fixedToolchain_3826_);
    v___x_3832_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3832_, 0, v___x_3830_);
    crate::leanh::lean_ctor_set(v___x_3832_, 1, v___x_3831_);
    v___x_3833_ =
        l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6;
    v___x_3834_ = 1;
    v___x_3835_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_name_3824_,
        v___x_3834_,
    );
    v___x_3836_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3836_, 0, v___x_3835_);
    v___x_3837_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3837_, 0, v___x_3833_);
    crate::leanh::lean_ctor_set(v___x_3837_, 1, v___x_3836_);
    v___x_3838_ = l_Lake_Manifest_toJson___closed__5;
    v___x_3839_ = l_Lake_mkRelPathString(v_lakeDir_3825_);
    v___x_3840_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3840_, 0, v___x_3839_);
    v___x_3841_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3841_, 0, v___x_3838_);
    crate::leanh::lean_ctor_set(v___x_3841_, 1, v___x_3840_);
    v___x_3842_ = l_Lake_Manifest_toJson___closed__6;
    v___x_3843_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_packagesDir_x3f_3827_);
    v___x_3844_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3844_, 0, v___x_3842_);
    crate::leanh::lean_ctor_set(v___x_3844_, 1, v___x_3843_);
    v___x_3845_ = l_Lake_Manifest_toJson___closed__7;
    v___x_3846_ = l_Array_toJson___at___00Lake_Manifest_toJson_spec__0(v_packages_3828_);
    v___x_3847_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3847_, 0, v___x_3845_);
    crate::leanh::lean_ctor_set(v___x_3847_, 1, v___x_3846_);
    v___x_3848_ = crate::leanh::lean_box(0);
    v___x_3849_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3849_, 0, v___x_3847_);
    crate::leanh::lean_ctor_set(v___x_3849_, 1, v___x_3848_);
    v___x_3850_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3850_, 0, v___x_3844_);
    crate::leanh::lean_ctor_set(v___x_3850_, 1, v___x_3849_);
    v___x_3851_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3851_, 0, v___x_3841_);
    crate::leanh::lean_ctor_set(v___x_3851_, 1, v___x_3850_);
    v___x_3852_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3852_, 0, v___x_3837_);
    crate::leanh::lean_ctor_set(v___x_3852_, 1, v___x_3851_);
    v___x_3853_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3853_, 0, v___x_3832_);
    crate::leanh::lean_ctor_set(v___x_3853_, 1, v___x_3852_);
    v___x_3854_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3854_, 0, v___x_3829_);
    crate::leanh::lean_ctor_set(v___x_3854_, 1, v___x_3853_);
    v___x_3855_ = l_Lean_Json_mkObj(v___x_3854_);
    crate::leanh::lean_dec_ref_known(v___x_3854_, 2);
    return v___x_3855_;
}
pub unsafe fn _init_l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v_natZero_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_natZero_3866_ = crate::leanh::lean_unsigned_to_nat(0);
    v_intZero_3867_ = lean_nat_to_int(v_natZero_3866_);
    return v_intZero_3867_;
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(
    mut v_obj_3872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ver_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_major_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: u8 = 0;
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: u8 = 0;
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ver_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mantissa_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natZero_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_3915_: u8 = 0;
    let mut v___x_3916_: u8 = 0;
    let mut v_a_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3924_: u8 = 0;
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3928_: u8 = 0;
    let mut v_a_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSemVerCore_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_major_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3932_ = l_Lake_Manifest_toJson___closed__0;
                v___x_3933_ = l_Lake_JsonObject_getJson_x3f(v_obj_3872_, v___x_3932_);
                if crate::leanh::lean_obj_tag(v___x_3933_) == 0 {
                    v___x_3934_ =
                        l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7;
                    v___x_3935_ = l_Lake_JsonObject_getJson_x3f(v_obj_3872_, v___x_3934_);
                    if crate::leanh::lean_obj_tag(v___x_3935_) == 0 {
                        v___x_3936_ =
                            l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__9;
                        return v___x_3936_;
                    } else {
                        v_val_3937_ = crate::leanh::lean_ctor_get(v___x_3935_, 0);
                        crate::leanh::lean_inc(v_val_3937_);
                        crate::leanh::lean_dec_ref_known(v___x_3935_, 1);
                        v_a_3909_ = v_val_3937_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_val_3938_ = crate::leanh::lean_ctor_get(v___x_3933_, 0);
                    crate::leanh::lean_inc(v_val_3938_);
                    crate::leanh::lean_dec_ref_known(v___x_3933_, 1);
                    v_a_3909_ = v_val_3938_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                v___x_3875_ =
                    l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__0;
                v___x_3876_ = l_Lake_SemVerCore_toString(v___y_3874_);
                v___x_3877_ = lean_string_append(v___x_3875_, v___x_3876_);
                crate::leanh::lean_dec_ref(v___x_3876_);
                v___x_3878_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2;
                v___x_3879_ = lean_string_append(v___x_3877_, v___x_3878_);
                v___x_3880_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3880_, 0, v___x_3879_);
                return v___x_3880_;
            }
            2 => {
                v___x_3884_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3885_ = lean_nat_dec_lt(v___x_3884_, v_major_3883_);
                crate::leanh::lean_dec(v_major_3883_);
                if v___x_3885_ == 0 {
                    v___x_3886_ =
                        l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__1;
                    v___x_3887_ = l_Lake_instOrdSemVerCore_ord(v_ver_3882_, v___x_3886_);
                    if v___x_3887_ == 0 {
                        v___y_3874_ = v_ver_3882_;
                        state = 1;
                        continue;
                    } else {
                        if v___x_3885_ == 0 {
                            v___x_3888_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3888_, 0, v_ver_3882_);
                            return v___x_3888_;
                        } else {
                            v___y_3874_ = v_ver_3882_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_3889_ =
                        l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__2;
                    v___x_3890_ = l_Lake_SemVerCore_toString(v_ver_3882_);
                    v___x_3891_ = lean_string_append(v___x_3889_, v___x_3890_);
                    crate::leanh::lean_dec_ref(v___x_3890_);
                    v___x_3892_ =
                        l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__3;
                    v___x_3893_ = lean_string_append(v___x_3891_, v___x_3892_);
                    v___x_3894_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_Manifest_toJson___closed__1),
                        core::ptr::addr_of_mut!(l_Lake_Manifest_toJson___closed__1_once),
                        _init_l_Lake_Manifest_toJson___closed__1,
                    );
                    v___x_3895_ = lean_string_append(v___x_3893_, v___x_3894_);
                    v___x_3896_ =
                        l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4;
                    v___x_3897_ = lean_string_append(v___x_3895_, v___x_3896_);
                    v___x_3898_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3898_, 0, v___x_3897_);
                    return v___x_3898_;
                }
            }
            3 => {
                v___x_3901_ =
                    l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__5;
                v___x_3902_ = crate::leanh::lean_unsigned_to_nat(80);
                v___x_3903_ = l_Lean_Json_pretty(v_ver_3900_, v___x_3902_);
                v___x_3904_ = lean_string_append(v___x_3901_, v___x_3903_);
                crate::leanh::lean_dec_ref(v___x_3903_);
                v___x_3905_ =
                    l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4;
                v___x_3906_ = lean_string_append(v___x_3904_, v___x_3905_);
                v___x_3907_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3907_, 0, v___x_3906_);
                return v___x_3907_;
            }
            4 => match crate::leanh::lean_obj_tag(v_a_3909_) {
                2 => {
                    v_n_3910_ = crate::leanh::lean_ctor_get(v_a_3909_, 0);
                    v_mantissa_3911_ = crate::leanh::lean_ctor_get(v_n_3910_, 0);
                    v_exponent_3912_ = crate::leanh::lean_ctor_get(v_n_3910_, 1);
                    v_natZero_3913_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_intZero_3914_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6_once), _init_l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6);
                    v_isNeg_3915_ = lean_int_dec_lt(v_mantissa_3911_, v_intZero_3914_);
                    if v_isNeg_3915_ == 0 {
                        v___x_3916_ = lean_nat_dec_eq(v_exponent_3912_, v_natZero_3913_);
                        if v___x_3916_ == 0 {
                            v_ver_3900_ = v_a_3909_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_mantissa_3911_);
                            crate::leanh::lean_dec_ref_known(v_a_3909_, 1);
                            v_a_3917_ = lean_nat_abs(v_mantissa_3911_);
                            crate::leanh::lean_dec(v_mantissa_3911_);
                            v___x_3918_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3918_, 0, v_natZero_3913_);
                            crate::leanh::lean_ctor_set(v___x_3918_, 1, v_a_3917_);
                            crate::leanh::lean_ctor_set(v___x_3918_, 2, v_natZero_3913_);
                            v_ver_3882_ = v___x_3918_;
                            v_major_3883_ = v_natZero_3913_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_ver_3900_ = v_a_3909_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v_s_3919_ = crate::leanh::lean_ctor_get(v_a_3909_, 0);
                    crate::leanh::lean_inc_ref(v_s_3919_);
                    crate::leanh::lean_dec_ref_known(v_a_3909_, 1);
                    v___x_3920_ = l_Lake_StdVer_parse(v_s_3919_);
                    if crate::leanh::lean_obj_tag(v___x_3920_) == 0 {
                        v_a_3921_ = crate::leanh::lean_ctor_get(v___x_3920_, 0);
                        v_isSharedCheck_3928_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3920_)) as u8;
                        if v_isSharedCheck_3928_ == 0 {
                            v___x_3923_ = v___x_3920_;
                            v_isShared_3924_ = v_isSharedCheck_3928_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3921_);
                            crate::leanh::lean_dec(v___x_3920_);
                            v___x_3923_ = crate::leanh::lean_box(0);
                            v_isShared_3924_ = v_isSharedCheck_3928_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_3929_ = crate::leanh::lean_ctor_get(v___x_3920_, 0);
                        crate::leanh::lean_inc(v_a_3929_);
                        crate::leanh::lean_dec_ref_known(v___x_3920_, 1);
                        v_toSemVerCore_3930_ = crate::leanh::lean_ctor_get(v_a_3929_, 0);
                        crate::leanh::lean_inc_ref(v_toSemVerCore_3930_);
                        crate::leanh::lean_dec(v_a_3929_);
                        v_major_3931_ = crate::leanh::lean_ctor_get(v_toSemVerCore_3930_, 0);
                        crate::leanh::lean_inc(v_major_3931_);
                        v_ver_3882_ = v_toSemVerCore_3930_;
                        v_major_3883_ = v_major_3931_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v_ver_3900_ = v_a_3909_;
                    state = 3;
                    continue;
                }
            },
            5 => {
                if v_isShared_3924_ == 0 {
                    v___x_3926_ = v___x_3923_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3927_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3921_);
                    v___x_3926_ = v_reuseFailAlloc_3927_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3926_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___boxed(
    mut v_obj_3939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3940_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_obj_3939_);
    crate::leanh::lean_dec(v_obj_3939_);
    return v_res_3940_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(
    mut v_sz_3941_: usize,
    mut v_i_3942_: usize,
    mut v_bs_3943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3944_: u8 = 0;
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3951_: u8 = 0;
    let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3955_: u8 = 0;
    let mut v_a_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: usize = 0;
    let mut v___x_3960_: usize = 0;
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3944_ = lean_usize_dec_lt(v_i_3942_, v_sz_3941_);
                if v___x_3944_ == 0 {
                    v___x_3945_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3945_, 0, v_bs_3943_);
                    return v___x_3945_;
                } else {
                    v_v_3946_ = lean_array_uget_borrowed(v_bs_3943_, v_i_3942_);
                    crate::leanh::lean_inc(v_v_3946_);
                    v___x_3947_ = l_Lake_PackageEntry_fromJson_x3f(v_v_3946_);
                    if crate::leanh::lean_obj_tag(v___x_3947_) == 0 {
                        crate::leanh::lean_dec_ref(v_bs_3943_);
                        v_a_3948_ = crate::leanh::lean_ctor_get(v___x_3947_, 0);
                        v_isSharedCheck_3955_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3947_)) as u8;
                        if v_isSharedCheck_3955_ == 0 {
                            v___x_3950_ = v___x_3947_;
                            v_isShared_3951_ = v_isSharedCheck_3955_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3948_);
                            crate::leanh::lean_dec(v___x_3947_);
                            v___x_3950_ = crate::leanh::lean_box(0);
                            v_isShared_3951_ = v_isSharedCheck_3955_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3956_ = crate::leanh::lean_ctor_get(v___x_3947_, 0);
                        crate::leanh::lean_inc(v_a_3956_);
                        crate::leanh::lean_dec_ref_known(v___x_3947_, 1);
                        v___x_3957_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3958_ = lean_array_uset(v_bs_3943_, v_i_3942_, v___x_3957_);
                        v___x_3959_ = 1usize;
                        v___x_3960_ = lean_usize_add(v_i_3942_, v___x_3959_);
                        v___x_3961_ = lean_array_uset(v_bs_x27_3958_, v_i_3942_, v_a_3956_);
                        v_i_3942_ = v___x_3960_;
                        v_bs_3943_ = v___x_3961_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3951_ == 0 {
                    v___x_3953_ = v___x_3950_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3954_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_a_3948_);
                    v___x_3953_ = v_reuseFailAlloc_3954_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3953_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2___boxed(
    mut v_sz_3963_: *mut crate::leanh::LeanObject,
    mut v_i_3964_: *mut crate::leanh::LeanObject,
    mut v_bs_3965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3966_: usize = 0;
    let mut v_i_boxed_3967_: usize = 0;
    let mut v_res_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3966_ = crate::leanh::lean_unbox_usize(v_sz_3963_);
    crate::leanh::lean_dec(v_sz_3963_);
    v_i_boxed_3967_ = crate::leanh::lean_unbox_usize(v_i_3964_);
    crate::leanh::lean_dec(v_i_3964_);
    v_res_3968_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(v_sz_boxed_3966_, v_i_boxed_3967_, v_bs_3965_);
    return v_res_3968_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1(
    mut v_x_3970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3970_) == 4 {
        let mut v_elems_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3972_: usize = 0;
        let mut v___x_3973_: usize = 0;
        let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_elems_3971_ = crate::leanh::lean_ctor_get(v_x_3970_, 0);
        crate::leanh::lean_inc_ref(v_elems_3971_);
        crate::leanh::lean_dec_ref_known(v_x_3970_, 1);
        v_sz_3972_ = lean_array_size(v_elems_3971_);
        v___x_3973_ = 0usize;
        v___x_3974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(v_sz_3972_, v___x_3973_, v_elems_3971_);
        return v___x_3974_;
    } else {
        let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3975_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1___closed__0;
        v___x_3976_ = crate::leanh::lean_unsigned_to_nat(80);
        v___x_3977_ = l_Lean_Json_pretty(v_x_3970_, v___x_3976_);
        v___x_3978_ = lean_string_append(v___x_3975_, v___x_3977_);
        crate::leanh::lean_dec_ref(v___x_3977_);
        v___x_3979_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2;
        v___x_3980_ = lean_string_append(v___x_3978_, v___x_3979_);
        v___x_3981_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3981_, 0, v___x_3980_);
        return v___x_3981_;
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1(
    mut v_x_3984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3990_: u8 = 0;
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3994_: u8 = 0;
    let mut v_a_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3998_: u8 = 0;
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4003_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3984_) == 0 {
                    v___x_3985_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1___closed__0;
                    return v___x_3985_;
                } else {
                    v___x_3986_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1(v_x_3984_);
                    if crate::leanh::lean_obj_tag(v___x_3986_) == 0 {
                        v_a_3987_ = crate::leanh::lean_ctor_get(v___x_3986_, 0);
                        v_isSharedCheck_3994_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3986_)) as u8;
                        if v_isSharedCheck_3994_ == 0 {
                            v___x_3989_ = v___x_3986_;
                            v_isShared_3990_ = v_isSharedCheck_3994_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3987_);
                            crate::leanh::lean_dec(v___x_3986_);
                            v___x_3989_ = crate::leanh::lean_box(0);
                            v_isShared_3990_ = v_isSharedCheck_3994_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3995_ = crate::leanh::lean_ctor_get(v___x_3986_, 0);
                        v_isSharedCheck_4003_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3986_)) as u8;
                        if v_isSharedCheck_4003_ == 0 {
                            v___x_3997_ = v___x_3986_;
                            v_isShared_3998_ = v_isSharedCheck_4003_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3995_);
                            crate::leanh::lean_dec(v___x_3986_);
                            v___x_3997_ = crate::leanh::lean_box(0);
                            v_isShared_3998_ = v_isSharedCheck_4003_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3990_ == 0 {
                    v___x_3992_ = v___x_3989_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3993_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3987_);
                    v___x_3992_ = v_reuseFailAlloc_3993_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3992_;
            }
            3 => {
                v___x_3999_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3999_, 0, v_a_3995_);
                if v_isShared_3998_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3997_, 0, v___x_3999_);
                    v___x_4001_ = v___x_3997_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4002_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___x_3999_);
                    v___x_4001_ = v_reuseFailAlloc_4002_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4001_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(
    mut v_sz_4004_: usize,
    mut v_i_4005_: usize,
    mut v_bs_4006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4007_: u8 = 0;
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4014_: u8 = 0;
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4018_: u8 = 0;
    let mut v_a_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: usize = 0;
    let mut v___x_4023_: usize = 0;
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4007_ = lean_usize_dec_lt(v_i_4005_, v_sz_4004_);
                if v___x_4007_ == 0 {
                    v___x_4008_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4008_, 0, v_bs_4006_);
                    return v___x_4008_;
                } else {
                    v_v_4009_ = lean_array_uget_borrowed(v_bs_4006_, v_i_4005_);
                    crate::leanh::lean_inc(v_v_4009_);
                    v___x_4010_ =
                        l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson(
                            v_v_4009_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_4010_) == 0 {
                        crate::leanh::lean_dec_ref(v_bs_4006_);
                        v_a_4011_ = crate::leanh::lean_ctor_get(v___x_4010_, 0);
                        v_isSharedCheck_4018_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4010_)) as u8;
                        if v_isSharedCheck_4018_ == 0 {
                            v___x_4013_ = v___x_4010_;
                            v_isShared_4014_ = v_isSharedCheck_4018_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4011_);
                            crate::leanh::lean_dec(v___x_4010_);
                            v___x_4013_ = crate::leanh::lean_box(0);
                            v_isShared_4014_ = v_isSharedCheck_4018_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4019_ = crate::leanh::lean_ctor_get(v___x_4010_, 0);
                        crate::leanh::lean_inc(v_a_4019_);
                        crate::leanh::lean_dec_ref_known(v___x_4010_, 1);
                        v___x_4020_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4021_ = lean_array_uset(v_bs_4006_, v_i_4005_, v___x_4020_);
                        v___x_4022_ = 1usize;
                        v___x_4023_ = lean_usize_add(v_i_4005_, v___x_4022_);
                        v___x_4024_ = lean_array_uset(v_bs_x27_4021_, v_i_4005_, v_a_4019_);
                        v_i_4005_ = v___x_4023_;
                        v_bs_4006_ = v___x_4024_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4014_ == 0 {
                    v___x_4016_ = v___x_4013_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4017_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_a_4011_);
                    v___x_4016_ = v_reuseFailAlloc_4017_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4016_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5___boxed(
    mut v_sz_4026_: *mut crate::leanh::LeanObject,
    mut v_i_4027_: *mut crate::leanh::LeanObject,
    mut v_bs_4028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4029_: usize = 0;
    let mut v_i_boxed_4030_: usize = 0;
    let mut v_res_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4029_ = crate::leanh::lean_unbox_usize(v_sz_4026_);
    crate::leanh::lean_dec(v_sz_4026_);
    v_i_boxed_4030_ = crate::leanh::lean_unbox_usize(v_i_4027_);
    crate::leanh::lean_dec(v_i_4027_);
    v_res_4031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(v_sz_boxed_4029_, v_i_boxed_4030_, v_bs_4028_);
    return v_res_4031_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3(
    mut v_x_4032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4032_) == 4 {
        let mut v_elems_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4034_: usize = 0;
        let mut v___x_4035_: usize = 0;
        let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_elems_4033_ = crate::leanh::lean_ctor_get(v_x_4032_, 0);
        crate::leanh::lean_inc_ref(v_elems_4033_);
        crate::leanh::lean_dec_ref_known(v_x_4032_, 1);
        v_sz_4034_ = lean_array_size(v_elems_4033_);
        v___x_4035_ = 0usize;
        v___x_4036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(v_sz_4034_, v___x_4035_, v_elems_4033_);
        return v___x_4036_;
    } else {
        let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4037_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1___closed__0;
        v___x_4038_ = crate::leanh::lean_unsigned_to_nat(80);
        v___x_4039_ = l_Lean_Json_pretty(v_x_4032_, v___x_4038_);
        v___x_4040_ = lean_string_append(v___x_4037_, v___x_4039_);
        crate::leanh::lean_dec_ref(v___x_4039_);
        v___x_4041_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2;
        v___x_4042_ = lean_string_append(v___x_4040_, v___x_4041_);
        v___x_4043_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4043_, 0, v___x_4042_);
        return v___x_4043_;
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2(
    mut v_x_4046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4052_: u8 = 0;
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4056_: u8 = 0;
    let mut v_a_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4060_: u8 = 0;
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4065_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4046_) == 0 {
                    v___x_4047_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2___closed__0;
                    return v___x_4047_;
                } else {
                    v___x_4048_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3(v_x_4046_);
                    if crate::leanh::lean_obj_tag(v___x_4048_) == 0 {
                        v_a_4049_ = crate::leanh::lean_ctor_get(v___x_4048_, 0);
                        v_isSharedCheck_4056_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4048_)) as u8;
                        if v_isSharedCheck_4056_ == 0 {
                            v___x_4051_ = v___x_4048_;
                            v_isShared_4052_ = v_isSharedCheck_4056_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4049_);
                            crate::leanh::lean_dec(v___x_4048_);
                            v___x_4051_ = crate::leanh::lean_box(0);
                            v_isShared_4052_ = v_isSharedCheck_4056_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4057_ = crate::leanh::lean_ctor_get(v___x_4048_, 0);
                        v_isSharedCheck_4065_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4048_)) as u8;
                        if v_isSharedCheck_4065_ == 0 {
                            v___x_4059_ = v___x_4048_;
                            v_isShared_4060_ = v_isSharedCheck_4065_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4057_);
                            crate::leanh::lean_dec(v___x_4048_);
                            v___x_4059_ = crate::leanh::lean_box(0);
                            v_isShared_4060_ = v_isSharedCheck_4065_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4052_ == 0 {
                    v___x_4054_ = v___x_4051_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4055_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
                    v___x_4054_ = v_reuseFailAlloc_4055_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4054_;
            }
            3 => {
                v___x_4061_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4061_, 0, v_a_4057_);
                if v_isShared_4060_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4059_, 0, v___x_4061_);
                    v___x_4063_ = v___x_4059_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4064_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4061_);
                    v___x_4063_ = v_reuseFailAlloc_4064_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4063_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(
    mut v_sz_4066_: usize,
    mut v_i_4067_: usize,
    mut v_bs_4068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4069_: u8 = 0;
    let mut v_v_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: usize = 0;
    let mut v___x_4075_: usize = 0;
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4069_ = lean_usize_dec_lt(v_i_4067_, v_sz_4066_);
                if v___x_4069_ == 0 {
                    return v_bs_4068_;
                } else {
                    v_v_4070_ = lean_array_uget(v_bs_4068_, v_i_4067_);
                    v___x_4071_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4072_ = lean_array_uset(v_bs_4068_, v_i_4067_, v___x_4071_);
                    v___x_4073_ =
                        l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(v_v_4070_);
                    crate::leanh::lean_dec(v_v_4070_);
                    v___x_4074_ = 1usize;
                    v___x_4075_ = lean_usize_add(v_i_4067_, v___x_4074_);
                    v___x_4076_ = lean_array_uset(v_bs_x27_4072_, v_i_4067_, v___x_4073_);
                    v_i_4067_ = v___x_4075_;
                    v_bs_4068_ = v___x_4076_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0___boxed(
    mut v_sz_4078_: *mut crate::leanh::LeanObject,
    mut v_i_4079_: *mut crate::leanh::LeanObject,
    mut v_bs_4080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4081_: usize = 0;
    let mut v_i_boxed_4082_: usize = 0;
    let mut v_res_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4081_ = crate::leanh::lean_unbox_usize(v_sz_4078_);
    crate::leanh::lean_dec(v_sz_4078_);
    v_i_boxed_4082_ = crate::leanh::lean_unbox_usize(v_i_4079_);
    crate::leanh::lean_dec(v_i_4079_);
    v_res_4083_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(v_sz_boxed_4081_, v_i_boxed_4082_, v_bs_4080_);
    return v_res_4083_;
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(
    mut v_ver_4097_: *mut crate::leanh::LeanObject,
    mut v_obj_4098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4101_: usize = 0;
    let mut v___x_4102_: usize = 0;
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: u8 = 0;
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4118_: u8 = 0;
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4124_: u8 = 0;
    let mut v_a_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4128_: u8 = 0;
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4132_: u8 = 0;
    let mut v_a_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4142_: u8 = 0;
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4148_: u8 = 0;
    let mut v_a_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4152_: u8 = 0;
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4156_: u8 = 0;
    let mut v_a_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4160_: u8 = 0;
    let mut v_val_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4165_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4109_ =
                    l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__4;
                v___x_4110_ = l_Lake_StdVer_compare(v_ver_4097_, v___x_4109_);
                if v___x_4110_ == 0 {
                    v___x_4111_ = l_Lake_Manifest_toJson___closed__7;
                    v___x_4112_ = l_Lake_JsonObject_getJson_x3f(v_obj_4098_, v___x_4111_);
                    if crate::leanh::lean_obj_tag(v___x_4112_) == 0 {
                        state = 2;
                        continue;
                    } else {
                        v_val_4113_ = crate::leanh::lean_ctor_get(v___x_4112_, 0);
                        crate::leanh::lean_inc(v_val_4113_);
                        crate::leanh::lean_dec_ref_known(v___x_4112_, 1);
                        v___x_4114_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2(v_val_4113_);
                        if crate::leanh::lean_obj_tag(v___x_4114_) == 0 {
                            v_a_4115_ = crate::leanh::lean_ctor_get(v___x_4114_, 0);
                            v_isSharedCheck_4124_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4114_)) as u8;
                            if v_isSharedCheck_4124_ == 0 {
                                v___x_4117_ = v___x_4114_;
                                v_isShared_4118_ = v_isSharedCheck_4124_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4115_);
                                crate::leanh::lean_dec(v___x_4114_);
                                v___x_4117_ = crate::leanh::lean_box(0);
                                v_isShared_4118_ = v_isSharedCheck_4124_;
                                state = 4;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_4114_) == 0 {
                                v_a_4125_ = crate::leanh::lean_ctor_get(v___x_4114_, 0);
                                v_isSharedCheck_4132_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4114_)) as u8;
                                if v_isSharedCheck_4132_ == 0 {
                                    v___x_4127_ = v___x_4114_;
                                    v_isShared_4128_ = v_isSharedCheck_4132_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4125_);
                                    crate::leanh::lean_dec(v___x_4114_);
                                    v___x_4127_ = crate::leanh::lean_box(0);
                                    v_isShared_4128_ = v_isSharedCheck_4132_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                v_a_4133_ = crate::leanh::lean_ctor_get(v___x_4114_, 0);
                                crate::leanh::lean_inc(v_a_4133_);
                                crate::leanh::lean_dec_ref_known(v___x_4114_, 1);
                                if crate::leanh::lean_obj_tag(v_a_4133_) == 0 {
                                    state = 2;
                                    continue;
                                } else {
                                    v_val_4134_ = crate::leanh::lean_ctor_get(v_a_4133_, 0);
                                    crate::leanh::lean_inc(v_val_4134_);
                                    crate::leanh::lean_dec_ref_known(v_a_4133_, 1);
                                    v_a_4100_ = v_val_4134_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    v___x_4135_ = l_Lake_Manifest_toJson___closed__7;
                    v___x_4136_ = l_Lake_JsonObject_getJson_x3f(v_obj_4098_, v___x_4135_);
                    if crate::leanh::lean_obj_tag(v___x_4136_) == 0 {
                        state = 3;
                        continue;
                    } else {
                        v_val_4137_ = crate::leanh::lean_ctor_get(v___x_4136_, 0);
                        crate::leanh::lean_inc(v_val_4137_);
                        crate::leanh::lean_dec_ref_known(v___x_4136_, 1);
                        v___x_4138_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1(v_val_4137_);
                        if crate::leanh::lean_obj_tag(v___x_4138_) == 0 {
                            v_a_4139_ = crate::leanh::lean_ctor_get(v___x_4138_, 0);
                            v_isSharedCheck_4148_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4138_)) as u8;
                            if v_isSharedCheck_4148_ == 0 {
                                v___x_4141_ = v___x_4138_;
                                v_isShared_4142_ = v_isSharedCheck_4148_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4139_);
                                crate::leanh::lean_dec(v___x_4138_);
                                v___x_4141_ = crate::leanh::lean_box(0);
                                v_isShared_4142_ = v_isSharedCheck_4148_;
                                state = 8;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_4138_) == 0 {
                                v_a_4149_ = crate::leanh::lean_ctor_get(v___x_4138_, 0);
                                v_isSharedCheck_4156_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4138_)) as u8;
                                if v_isSharedCheck_4156_ == 0 {
                                    v___x_4151_ = v___x_4138_;
                                    v_isShared_4152_ = v_isSharedCheck_4156_;
                                    state = 10;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4149_);
                                    crate::leanh::lean_dec(v___x_4138_);
                                    v___x_4151_ = crate::leanh::lean_box(0);
                                    v_isShared_4152_ = v_isSharedCheck_4156_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                v_a_4157_ = crate::leanh::lean_ctor_get(v___x_4138_, 0);
                                v_isSharedCheck_4165_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4138_)) as u8;
                                if v_isSharedCheck_4165_ == 0 {
                                    v___x_4159_ = v___x_4138_;
                                    v_isShared_4160_ = v_isSharedCheck_4165_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4157_);
                                    crate::leanh::lean_dec(v___x_4138_);
                                    v___x_4159_ = crate::leanh::lean_box(0);
                                    v_isShared_4160_ = v_isSharedCheck_4165_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v_sz_4101_ = lean_array_size(v_a_4100_);
                v___x_4102_ = 0usize;
                v___x_4103_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(v_sz_4101_, v___x_4102_, v_a_4100_);
                v___x_4104_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4104_, 0, v___x_4103_);
                return v___x_4104_;
            }
            2 => {
                v___x_4106_ =
                    l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__0;
                v_a_4100_ = v___x_4106_;
                state = 1;
                continue;
            }
            3 => {
                v___x_4108_ =
                    l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__2;
                return v___x_4108_;
            }
            4 => {
                v___x_4119_ =
                    l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__5;
                v___x_4120_ = lean_string_append(v___x_4119_, v_a_4115_);
                crate::leanh::lean_dec(v_a_4115_);
                if v_isShared_4118_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4117_, 0, v___x_4120_);
                    v___x_4122_ = v___x_4117_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4123_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4123_, 0, v___x_4120_);
                    v___x_4122_ = v_reuseFailAlloc_4123_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4122_;
            }
            6 => {
                if v_isShared_4128_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4127_, 0);
                    v___x_4130_ = v___x_4127_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4131_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_a_4125_);
                    v___x_4130_ = v_reuseFailAlloc_4131_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4130_;
            }
            8 => {
                v___x_4143_ =
                    l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__5;
                v___x_4144_ = lean_string_append(v___x_4143_, v_a_4139_);
                crate::leanh::lean_dec(v_a_4139_);
                if v_isShared_4142_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4141_, 0, v___x_4144_);
                    v___x_4146_ = v___x_4141_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4147_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4147_, 0, v___x_4144_);
                    v___x_4146_ = v_reuseFailAlloc_4147_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4146_;
            }
            10 => {
                if v_isShared_4152_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4151_, 0);
                    v___x_4154_ = v___x_4151_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4155_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
                    v___x_4154_ = v_reuseFailAlloc_4155_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4154_;
            }
            12 => {
                if crate::leanh::lean_obj_tag(v_a_4157_) == 0 {
                    crate::leanh::lean_del_object(v___x_4159_);
                    state = 3;
                    continue;
                } else {
                    v_val_4161_ = crate::leanh::lean_ctor_get(v_a_4157_, 0);
                    crate::leanh::lean_inc(v_val_4161_);
                    crate::leanh::lean_dec_ref_known(v_a_4157_, 1);
                    if v_isShared_4160_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4159_, 0, v_val_4161_);
                        v___x_4163_ = v___x_4159_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_4164_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_val_4161_);
                        v___x_4163_ = v_reuseFailAlloc_4164_;
                        state = 13;
                        continue;
                    }
                }
            }
            13 => {
                return v___x_4163_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___boxed(
    mut v_ver_4166_: *mut crate::leanh::LeanObject,
    mut v_obj_4167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4168_ =
        l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(v_ver_4166_, v_obj_4167_);
    crate::leanh::lean_dec(v_obj_4167_);
    crate::leanh::lean_dec_ref(v_ver_4166_);
    return v_res_4168_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0(
    mut v_x_4171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4177_: u8 = 0;
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4181_: u8 = 0;
    let mut v_a_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4185_: u8 = 0;
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4190_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4171_) == 0 {
                    v___x_4172_ = l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0___closed__0;
                    return v___x_4172_;
                } else {
                    v___x_4173_ = l_Lean_Name_fromJson_x3f(v_x_4171_);
                    if crate::leanh::lean_obj_tag(v___x_4173_) == 0 {
                        v_a_4174_ = crate::leanh::lean_ctor_get(v___x_4173_, 0);
                        v_isSharedCheck_4181_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4173_)) as u8;
                        if v_isSharedCheck_4181_ == 0 {
                            v___x_4176_ = v___x_4173_;
                            v_isShared_4177_ = v_isSharedCheck_4181_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4174_);
                            crate::leanh::lean_dec(v___x_4173_);
                            v___x_4176_ = crate::leanh::lean_box(0);
                            v_isShared_4177_ = v_isSharedCheck_4181_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4182_ = crate::leanh::lean_ctor_get(v___x_4173_, 0);
                        v_isSharedCheck_4190_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4173_)) as u8;
                        if v_isSharedCheck_4190_ == 0 {
                            v___x_4184_ = v___x_4173_;
                            v_isShared_4185_ = v_isSharedCheck_4190_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4182_);
                            crate::leanh::lean_dec(v___x_4173_);
                            v___x_4184_ = crate::leanh::lean_box(0);
                            v_isShared_4185_ = v_isSharedCheck_4190_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4177_ == 0 {
                    v___x_4179_ = v___x_4176_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4180_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_a_4174_);
                    v___x_4179_ = v_reuseFailAlloc_4180_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4179_;
            }
            3 => {
                v___x_4186_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4186_, 0, v_a_4182_);
                if v_isShared_4185_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4184_, 0, v___x_4186_);
                    v___x_4188_ = v___x_4184_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4189_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4189_, 0, v___x_4186_);
                    v___x_4188_ = v_reuseFailAlloc_4189_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4188_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1(
    mut v_x_4193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4199_: u8 = 0;
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4203_: u8 = 0;
    let mut v_a_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4207_: u8 = 0;
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4212_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4193_) == 0 {
                    v___x_4194_ = l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1___closed__0;
                    return v___x_4194_;
                } else {
                    v___x_4195_ = l_Lean_Json_getBool_x3f(v_x_4193_);
                    if crate::leanh::lean_obj_tag(v___x_4195_) == 0 {
                        v_a_4196_ = crate::leanh::lean_ctor_get(v___x_4195_, 0);
                        v_isSharedCheck_4203_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4195_)) as u8;
                        if v_isSharedCheck_4203_ == 0 {
                            v___x_4198_ = v___x_4195_;
                            v_isShared_4199_ = v_isSharedCheck_4203_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4196_);
                            crate::leanh::lean_dec(v___x_4195_);
                            v___x_4198_ = crate::leanh::lean_box(0);
                            v_isShared_4199_ = v_isSharedCheck_4203_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4204_ = crate::leanh::lean_ctor_get(v___x_4195_, 0);
                        v_isSharedCheck_4212_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4195_)) as u8;
                        if v_isSharedCheck_4212_ == 0 {
                            v___x_4206_ = v___x_4195_;
                            v_isShared_4207_ = v_isSharedCheck_4212_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4204_);
                            crate::leanh::lean_dec(v___x_4195_);
                            v___x_4206_ = crate::leanh::lean_box(0);
                            v_isShared_4207_ = v_isSharedCheck_4212_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4199_ == 0 {
                    v___x_4201_ = v___x_4198_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4202_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_a_4196_);
                    v___x_4201_ = v_reuseFailAlloc_4202_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4201_;
            }
            3 => {
                v___x_4208_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4208_, 0, v_a_4204_);
                if v_isShared_4207_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4206_, 0, v___x_4208_);
                    v___x_4210_ = v___x_4206_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4211_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4211_, 0, v___x_4208_);
                    v___x_4210_ = v_reuseFailAlloc_4211_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4210_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1___boxed(
    mut v_x_4213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4214_ = l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1(v_x_4213_);
    crate::leanh::lean_dec(v_x_4213_);
    return v_res_4214_;
}
pub unsafe fn l_Lake_Manifest_fromJson_x3f(
    mut v_json_4218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4223_: u8 = 0;
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4227_: u8 = 0;
    let mut v_a_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4233_: u8 = 0;
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4237_: u8 = 0;
    let mut v_a_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4240_: u8 = 0;
    let mut v___y_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4250_: u8 = 0;
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4254_: u8 = 0;
    let mut v_a_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4258_: u8 = 0;
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4263_: u8 = 0;
    let mut v___y_4265_: u8 = 0;
    let mut v___y_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4276_: u8 = 0;
    let mut v___x_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4282_: u8 = 0;
    let mut v_a_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4286_: u8 = 0;
    let mut v___x_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4290_: u8 = 0;
    let mut v_a_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4293_: u8 = 0;
    let mut v___y_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4297_: u8 = 0;
    let mut v_a_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4306_: u8 = 0;
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4312_: u8 = 0;
    let mut v_a_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4316_: u8 = 0;
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4320_: u8 = 0;
    let mut v_a_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4324_: u8 = 0;
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4327_: u8 = 0;
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4335_: u8 = 0;
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4341_: u8 = 0;
    let mut v_a_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4345_: u8 = 0;
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4349_: u8 = 0;
    let mut v_a_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: u8 = 0;
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4361_: u8 = 0;
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4367_: u8 = 0;
    let mut v_a_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4371_: u8 = 0;
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4375_: u8 = 0;
    let mut v_a_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4219_ = l_Lean_Json_getObj_x3f(v_json_4218_);
                if crate::leanh::lean_obj_tag(v___x_4219_) == 0 {
                    v_a_4220_ = crate::leanh::lean_ctor_get(v___x_4219_, 0);
                    v_isSharedCheck_4227_ = (!crate::leanh::lean_is_exclusive(v___x_4219_)) as u8;
                    if v_isSharedCheck_4227_ == 0 {
                        v___x_4222_ = v___x_4219_;
                        v_isShared_4223_ = v_isSharedCheck_4227_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4220_);
                        crate::leanh::lean_dec(v___x_4219_);
                        v___x_4222_ = crate::leanh::lean_box(0);
                        v_isShared_4223_ = v_isSharedCheck_4227_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4228_ = crate::leanh::lean_ctor_get(v___x_4219_, 0);
                    crate::leanh::lean_inc(v_a_4228_);
                    crate::leanh::lean_dec_ref_known(v___x_4219_, 1);
                    v___x_4229_ =
                        l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_a_4228_);
                    if crate::leanh::lean_obj_tag(v___x_4229_) == 0 {
                        crate::leanh::lean_dec(v_a_4228_);
                        v_a_4230_ = crate::leanh::lean_ctor_get(v___x_4229_, 0);
                        v_isSharedCheck_4237_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4229_)) as u8;
                        if v_isSharedCheck_4237_ == 0 {
                            v___x_4232_ = v___x_4229_;
                            v_isShared_4233_ = v_isSharedCheck_4237_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4230_);
                            crate::leanh::lean_dec(v___x_4229_);
                            v___x_4232_ = crate::leanh::lean_box(0);
                            v_isShared_4233_ = v_isSharedCheck_4237_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4238_ = crate::leanh::lean_ctor_get(v___x_4229_, 0);
                        crate::leanh::lean_inc(v_a_4238_);
                        crate::leanh::lean_dec_ref_known(v___x_4229_, 1);
                        v___x_4354_ = l_Lake_Manifest_toJson___closed__4;
                        v___x_4355_ = l_Lake_JsonObject_getJson_x3f(v_a_4228_, v___x_4354_);
                        if crate::leanh::lean_obj_tag(v___x_4355_) == 0 {
                            state = 27;
                            continue;
                        } else {
                            v_val_4356_ = crate::leanh::lean_ctor_get(v___x_4355_, 0);
                            crate::leanh::lean_inc(v_val_4356_);
                            crate::leanh::lean_dec_ref_known(v___x_4355_, 1);
                            v___x_4357_ =
                                l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1(
                                    v_val_4356_,
                                );
                            crate::leanh::lean_dec(v_val_4356_);
                            if crate::leanh::lean_obj_tag(v___x_4357_) == 0 {
                                crate::leanh::lean_dec(v_a_4238_);
                                crate::leanh::lean_dec(v_a_4228_);
                                v_a_4358_ = crate::leanh::lean_ctor_get(v___x_4357_, 0);
                                v_isSharedCheck_4367_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4357_)) as u8;
                                if v_isSharedCheck_4367_ == 0 {
                                    v___x_4360_ = v___x_4357_;
                                    v_isShared_4361_ = v_isSharedCheck_4367_;
                                    state = 28;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4358_);
                                    crate::leanh::lean_dec(v___x_4357_);
                                    v___x_4360_ = crate::leanh::lean_box(0);
                                    v_isShared_4361_ = v_isSharedCheck_4367_;
                                    state = 28;
                                    continue;
                                }
                            } else {
                                if crate::leanh::lean_obj_tag(v___x_4357_) == 0 {
                                    crate::leanh::lean_dec(v_a_4238_);
                                    crate::leanh::lean_dec(v_a_4228_);
                                    v_a_4368_ = crate::leanh::lean_ctor_get(v___x_4357_, 0);
                                    v_isSharedCheck_4375_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4357_)) as u8;
                                    if v_isSharedCheck_4375_ == 0 {
                                        v___x_4370_ = v___x_4357_;
                                        v_isShared_4371_ = v_isSharedCheck_4375_;
                                        state = 30;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4368_);
                                        crate::leanh::lean_dec(v___x_4357_);
                                        v___x_4370_ = crate::leanh::lean_box(0);
                                        v_isShared_4371_ = v_isSharedCheck_4375_;
                                        state = 30;
                                        continue;
                                    }
                                } else {
                                    v_a_4376_ = crate::leanh::lean_ctor_get(v___x_4357_, 0);
                                    crate::leanh::lean_inc(v_a_4376_);
                                    crate::leanh::lean_dec_ref_known(v___x_4357_, 1);
                                    if crate::leanh::lean_obj_tag(v_a_4376_) == 0 {
                                        state = 27;
                                        continue;
                                    } else {
                                        v_val_4377_ = crate::leanh::lean_ctor_get(v_a_4376_, 0);
                                        crate::leanh::lean_inc(v_val_4377_);
                                        crate::leanh::lean_dec_ref_known(v_a_4376_, 1);
                                        v___x_4378_ = (crate::leanh::lean_unbox(v_val_4377_) as u8);
                                        crate::leanh::lean_dec(v_val_4377_);
                                        v_a_4327_ = v___x_4378_;
                                        state = 22;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4223_ == 0 {
                    v___x_4225_ = v___x_4222_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4226_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_a_4220_);
                    v___x_4225_ = v_reuseFailAlloc_4226_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4225_;
            }
            3 => {
                if v_isShared_4233_ == 0 {
                    v___x_4235_ = v___x_4232_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4236_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4230_);
                    v___x_4235_ = v_reuseFailAlloc_4236_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4235_;
            }
            5 => {
                v___x_4244_ = l_Lake_Manifest_version___closed__1;
                v___x_4245_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4245_, 0, v_a_4238_);
                crate::leanh::lean_ctor_set(v___x_4245_, 1, v___x_4244_);
                v___x_4246_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(
                    v___x_4245_,
                    v_a_4228_,
                );
                crate::leanh::lean_dec(v_a_4228_);
                crate::leanh::lean_dec_ref_known(v___x_4245_, 2);
                if crate::leanh::lean_obj_tag(v___x_4246_) == 0 {
                    crate::leanh::lean_dec(v_a_4243_);
                    crate::leanh::lean_dec(v___y_4242_);
                    crate::leanh::lean_dec_ref(v___y_4241_);
                    v_a_4247_ = crate::leanh::lean_ctor_get(v___x_4246_, 0);
                    v_isSharedCheck_4254_ = (!crate::leanh::lean_is_exclusive(v___x_4246_)) as u8;
                    if v_isSharedCheck_4254_ == 0 {
                        v___x_4249_ = v___x_4246_;
                        v_isShared_4250_ = v_isSharedCheck_4254_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4247_);
                        crate::leanh::lean_dec(v___x_4246_);
                        v___x_4249_ = crate::leanh::lean_box(0);
                        v_isShared_4250_ = v_isSharedCheck_4254_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_a_4255_ = crate::leanh::lean_ctor_get(v___x_4246_, 0);
                    v_isSharedCheck_4263_ = (!crate::leanh::lean_is_exclusive(v___x_4246_)) as u8;
                    if v_isSharedCheck_4263_ == 0 {
                        v___x_4257_ = v___x_4246_;
                        v_isShared_4258_ = v_isSharedCheck_4263_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4255_);
                        crate::leanh::lean_dec(v___x_4246_);
                        v___x_4257_ = crate::leanh::lean_box(0);
                        v_isShared_4258_ = v_isSharedCheck_4263_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_4250_ == 0 {
                    v___x_4252_ = v___x_4249_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4253_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_a_4247_);
                    v___x_4252_ = v_reuseFailAlloc_4253_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4252_;
            }
            8 => {
                v___x_4259_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4259_, 0, v___y_4242_);
                crate::leanh::lean_ctor_set(v___x_4259_, 1, v___y_4241_);
                crate::leanh::lean_ctor_set(v___x_4259_, 2, v_a_4243_);
                crate::leanh::lean_ctor_set(v___x_4259_, 3, v_a_4255_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4259_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___y_4240_,
                );
                if v_isShared_4258_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4257_, 0, v___x_4259_);
                    v___x_4261_ = v___x_4257_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4262_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4262_, 0, v___x_4259_);
                    v___x_4261_ = v_reuseFailAlloc_4262_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4261_;
            }
            10 => {
                v___x_4268_ = l_Lake_Manifest_toJson___closed__6;
                v___x_4269_ = l_Lake_JsonObject_getJson_x3f(v_a_4228_, v___x_4268_);
                if crate::leanh::lean_obj_tag(v___x_4269_) == 0 {
                    v___x_4270_ = crate::leanh::lean_box(0);
                    v___y_4240_ = v___y_4265_;
                    v___y_4241_ = v_a_4267_;
                    v___y_4242_ = v___y_4266_;
                    v_a_4243_ = v___x_4270_;
                    state = 5;
                    continue;
                } else {
                    v_val_4271_ = crate::leanh::lean_ctor_get(v___x_4269_, 0);
                    crate::leanh::lean_inc(v_val_4271_);
                    crate::leanh::lean_dec_ref_known(v___x_4269_, 1);
                    v___x_4272_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_4271_);
                    if crate::leanh::lean_obj_tag(v___x_4272_) == 0 {
                        crate::leanh::lean_dec_ref(v_a_4267_);
                        crate::leanh::lean_dec(v___y_4266_);
                        crate::leanh::lean_dec(v_a_4238_);
                        crate::leanh::lean_dec(v_a_4228_);
                        v_a_4273_ = crate::leanh::lean_ctor_get(v___x_4272_, 0);
                        v_isSharedCheck_4282_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4272_)) as u8;
                        if v_isSharedCheck_4282_ == 0 {
                            v___x_4275_ = v___x_4272_;
                            v_isShared_4276_ = v_isSharedCheck_4282_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4273_);
                            crate::leanh::lean_dec(v___x_4272_);
                            v___x_4275_ = crate::leanh::lean_box(0);
                            v_isShared_4276_ = v_isSharedCheck_4282_;
                            state = 11;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_4272_) == 0 {
                            crate::leanh::lean_dec_ref(v_a_4267_);
                            crate::leanh::lean_dec(v___y_4266_);
                            crate::leanh::lean_dec(v_a_4238_);
                            crate::leanh::lean_dec(v_a_4228_);
                            v_a_4283_ = crate::leanh::lean_ctor_get(v___x_4272_, 0);
                            v_isSharedCheck_4290_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4272_)) as u8;
                            if v_isSharedCheck_4290_ == 0 {
                                v___x_4285_ = v___x_4272_;
                                v_isShared_4286_ = v_isSharedCheck_4290_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4283_);
                                crate::leanh::lean_dec(v___x_4272_);
                                v___x_4285_ = crate::leanh::lean_box(0);
                                v_isShared_4286_ = v_isSharedCheck_4290_;
                                state = 13;
                                continue;
                            }
                        } else {
                            v_a_4291_ = crate::leanh::lean_ctor_get(v___x_4272_, 0);
                            crate::leanh::lean_inc(v_a_4291_);
                            crate::leanh::lean_dec_ref_known(v___x_4272_, 1);
                            v___y_4240_ = v___y_4265_;
                            v___y_4241_ = v_a_4267_;
                            v___y_4242_ = v___y_4266_;
                            v_a_4243_ = v_a_4291_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            11 => {
                v___x_4277_ = l_Lake_Manifest_fromJson_x3f___closed__0;
                v___x_4278_ = lean_string_append(v___x_4277_, v_a_4273_);
                crate::leanh::lean_dec(v_a_4273_);
                if v_isShared_4276_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4275_, 0, v___x_4278_);
                    v___x_4280_ = v___x_4275_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4281_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4281_, 0, v___x_4278_);
                    v___x_4280_ = v_reuseFailAlloc_4281_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4280_;
            }
            13 => {
                if v_isShared_4286_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4285_, 0);
                    v___x_4288_ = v___x_4285_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4289_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4283_);
                    v___x_4288_ = v_reuseFailAlloc_4289_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4288_;
            }
            15 => {
                v___x_4295_ = l_Lake_defaultLakeDir;
                v___y_4265_ = v___y_4293_;
                v___y_4266_ = v___y_4294_;
                v_a_4267_ = v___x_4295_;
                state = 10;
                continue;
            }
            16 => {
                v___x_4299_ = l_Lake_Manifest_toJson___closed__5;
                v___x_4300_ = l_Lake_JsonObject_getJson_x3f(v_a_4228_, v___x_4299_);
                if crate::leanh::lean_obj_tag(v___x_4300_) == 0 {
                    v___y_4293_ = v___y_4297_;
                    v___y_4294_ = v_a_4298_;
                    state = 15;
                    continue;
                } else {
                    v_val_4301_ = crate::leanh::lean_ctor_get(v___x_4300_, 0);
                    crate::leanh::lean_inc(v_val_4301_);
                    crate::leanh::lean_dec_ref_known(v___x_4300_, 1);
                    v___x_4302_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_4301_);
                    if crate::leanh::lean_obj_tag(v___x_4302_) == 0 {
                        crate::leanh::lean_dec(v_a_4298_);
                        crate::leanh::lean_dec(v_a_4238_);
                        crate::leanh::lean_dec(v_a_4228_);
                        v_a_4303_ = crate::leanh::lean_ctor_get(v___x_4302_, 0);
                        v_isSharedCheck_4312_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4302_)) as u8;
                        if v_isSharedCheck_4312_ == 0 {
                            v___x_4305_ = v___x_4302_;
                            v_isShared_4306_ = v_isSharedCheck_4312_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4303_);
                            crate::leanh::lean_dec(v___x_4302_);
                            v___x_4305_ = crate::leanh::lean_box(0);
                            v_isShared_4306_ = v_isSharedCheck_4312_;
                            state = 17;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_4302_) == 0 {
                            crate::leanh::lean_dec(v_a_4298_);
                            crate::leanh::lean_dec(v_a_4238_);
                            crate::leanh::lean_dec(v_a_4228_);
                            v_a_4313_ = crate::leanh::lean_ctor_get(v___x_4302_, 0);
                            v_isSharedCheck_4320_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4302_)) as u8;
                            if v_isSharedCheck_4320_ == 0 {
                                v___x_4315_ = v___x_4302_;
                                v_isShared_4316_ = v_isSharedCheck_4320_;
                                state = 19;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4313_);
                                crate::leanh::lean_dec(v___x_4302_);
                                v___x_4315_ = crate::leanh::lean_box(0);
                                v_isShared_4316_ = v_isSharedCheck_4320_;
                                state = 19;
                                continue;
                            }
                        } else {
                            v_a_4321_ = crate::leanh::lean_ctor_get(v___x_4302_, 0);
                            crate::leanh::lean_inc(v_a_4321_);
                            crate::leanh::lean_dec_ref_known(v___x_4302_, 1);
                            if crate::leanh::lean_obj_tag(v_a_4321_) == 0 {
                                v___y_4293_ = v___y_4297_;
                                v___y_4294_ = v_a_4298_;
                                state = 15;
                                continue;
                            } else {
                                v_val_4322_ = crate::leanh::lean_ctor_get(v_a_4321_, 0);
                                crate::leanh::lean_inc(v_val_4322_);
                                crate::leanh::lean_dec_ref_known(v_a_4321_, 1);
                                v___y_4265_ = v___y_4297_;
                                v___y_4266_ = v_a_4298_;
                                v_a_4267_ = v_val_4322_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                }
            }
            17 => {
                v___x_4307_ = l_Lake_Manifest_fromJson_x3f___closed__1;
                v___x_4308_ = lean_string_append(v___x_4307_, v_a_4303_);
                crate::leanh::lean_dec(v_a_4303_);
                if v_isShared_4306_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4305_, 0, v___x_4308_);
                    v___x_4310_ = v___x_4305_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4311_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4311_, 0, v___x_4308_);
                    v___x_4310_ = v_reuseFailAlloc_4311_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4310_;
            }
            19 => {
                if v_isShared_4316_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4315_, 0);
                    v___x_4318_ = v___x_4315_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4319_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4313_);
                    v___x_4318_ = v_reuseFailAlloc_4319_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4318_;
            }
            21 => {
                v___x_4325_ = crate::leanh::lean_box(0);
                v___y_4297_ = v___y_4324_;
                v_a_4298_ = v___x_4325_;
                state = 16;
                continue;
            }
            22 => {
                v___x_4328_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6;
                v___x_4329_ = l_Lake_JsonObject_getJson_x3f(v_a_4228_, v___x_4328_);
                if crate::leanh::lean_obj_tag(v___x_4329_) == 0 {
                    v___y_4324_ = v_a_4327_;
                    state = 21;
                    continue;
                } else {
                    v_val_4330_ = crate::leanh::lean_ctor_get(v___x_4329_, 0);
                    crate::leanh::lean_inc(v_val_4330_);
                    crate::leanh::lean_dec_ref_known(v___x_4329_, 1);
                    v___x_4331_ = l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0(
                        v_val_4330_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4331_) == 0 {
                        crate::leanh::lean_dec(v_a_4238_);
                        crate::leanh::lean_dec(v_a_4228_);
                        v_a_4332_ = crate::leanh::lean_ctor_get(v___x_4331_, 0);
                        v_isSharedCheck_4341_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4331_)) as u8;
                        if v_isSharedCheck_4341_ == 0 {
                            v___x_4334_ = v___x_4331_;
                            v_isShared_4335_ = v_isSharedCheck_4341_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4332_);
                            crate::leanh::lean_dec(v___x_4331_);
                            v___x_4334_ = crate::leanh::lean_box(0);
                            v_isShared_4335_ = v_isSharedCheck_4341_;
                            state = 23;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_4331_) == 0 {
                            crate::leanh::lean_dec(v_a_4238_);
                            crate::leanh::lean_dec(v_a_4228_);
                            v_a_4342_ = crate::leanh::lean_ctor_get(v___x_4331_, 0);
                            v_isSharedCheck_4349_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4331_)) as u8;
                            if v_isSharedCheck_4349_ == 0 {
                                v___x_4344_ = v___x_4331_;
                                v_isShared_4345_ = v_isSharedCheck_4349_;
                                state = 25;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4342_);
                                crate::leanh::lean_dec(v___x_4331_);
                                v___x_4344_ = crate::leanh::lean_box(0);
                                v_isShared_4345_ = v_isSharedCheck_4349_;
                                state = 25;
                                continue;
                            }
                        } else {
                            v_a_4350_ = crate::leanh::lean_ctor_get(v___x_4331_, 0);
                            crate::leanh::lean_inc(v_a_4350_);
                            crate::leanh::lean_dec_ref_known(v___x_4331_, 1);
                            if crate::leanh::lean_obj_tag(v_a_4350_) == 0 {
                                v___y_4324_ = v_a_4327_;
                                state = 21;
                                continue;
                            } else {
                                v_val_4351_ = crate::leanh::lean_ctor_get(v_a_4350_, 0);
                                crate::leanh::lean_inc(v_val_4351_);
                                crate::leanh::lean_dec_ref_known(v_a_4350_, 1);
                                v___y_4297_ = v_a_4327_;
                                v_a_4298_ = v_val_4351_;
                                state = 16;
                                continue;
                            }
                        }
                    }
                }
            }
            23 => {
                v___x_4336_ = l_Lake_PackageEntry_fromJson_x3f___closed__1;
                v___x_4337_ = lean_string_append(v___x_4336_, v_a_4332_);
                crate::leanh::lean_dec(v_a_4332_);
                if v_isShared_4335_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4334_, 0, v___x_4337_);
                    v___x_4339_ = v___x_4334_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4340_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4340_, 0, v___x_4337_);
                    v___x_4339_ = v_reuseFailAlloc_4340_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4339_;
            }
            25 => {
                if v_isShared_4345_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4344_, 0);
                    v___x_4347_ = v___x_4344_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4348_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_a_4342_);
                    v___x_4347_ = v_reuseFailAlloc_4348_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_4347_;
            }
            27 => {
                v___x_4353_ = 0;
                v_a_4327_ = v___x_4353_;
                state = 22;
                continue;
            }
            28 => {
                v___x_4362_ = l_Lake_Manifest_fromJson_x3f___closed__2;
                v___x_4363_ = lean_string_append(v___x_4362_, v_a_4358_);
                crate::leanh::lean_dec(v_a_4358_);
                if v_isShared_4361_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4360_, 0, v___x_4363_);
                    v___x_4365_ = v___x_4360_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4366_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4366_, 0, v___x_4363_);
                    v___x_4365_ = v_reuseFailAlloc_4366_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_4365_;
            }
            30 => {
                if v_isShared_4371_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4370_, 0);
                    v___x_4373_ = v___x_4370_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4374_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_a_4368_);
                    v___x_4373_ = v_reuseFailAlloc_4374_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_4373_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Manifest_parse(
    mut v_data_4382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4387_: u8 = 0;
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4393_: u8 = 0;
    let mut v_a_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4383_ = l_Lean_Json_parse(v_data_4382_);
                if crate::leanh::lean_obj_tag(v___x_4383_) == 0 {
                    v_a_4384_ = crate::leanh::lean_ctor_get(v___x_4383_, 0);
                    v_isSharedCheck_4393_ = (!crate::leanh::lean_is_exclusive(v___x_4383_)) as u8;
                    if v_isSharedCheck_4393_ == 0 {
                        v___x_4386_ = v___x_4383_;
                        v_isShared_4387_ = v_isSharedCheck_4393_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4384_);
                        crate::leanh::lean_dec(v___x_4383_);
                        v___x_4386_ = crate::leanh::lean_box(0);
                        v_isShared_4387_ = v_isSharedCheck_4393_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4394_ = crate::leanh::lean_ctor_get(v___x_4383_, 0);
                    crate::leanh::lean_inc(v_a_4394_);
                    crate::leanh::lean_dec_ref_known(v___x_4383_, 1);
                    v___x_4395_ = l_Lake_Manifest_fromJson_x3f(v_a_4394_);
                    return v___x_4395_;
                }
            }
            1 => {
                v___x_4388_ = l_Lake_Manifest_parse___closed__0;
                v___x_4389_ = lean_string_append(v___x_4388_, v_a_4384_);
                crate::leanh::lean_dec(v_a_4384_);
                if v_isShared_4387_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4386_, 0, v___x_4389_);
                    v___x_4391_ = v___x_4386_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4392_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4392_, 0, v___x_4389_);
                    v___x_4391_ = v_reuseFailAlloc_4392_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4391_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Manifest_load(
    mut v_file_4397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4403_: u8 = 0;
    let mut v_a_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4423_: u8 = 0;
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4427_: u8 = 0;
    let mut v_isSharedCheck_4428_: u8 = 0;
    let mut v_a_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4432_: u8 = 0;
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4436_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4399_ = l_IO_FS_readFile(v_file_4397_);
                if crate::leanh::lean_obj_tag(v___x_4399_) == 0 {
                    v_a_4400_ = crate::leanh::lean_ctor_get(v___x_4399_, 0);
                    v_isSharedCheck_4428_ = (!crate::leanh::lean_is_exclusive(v___x_4399_)) as u8;
                    if v_isSharedCheck_4428_ == 0 {
                        v___x_4402_ = v___x_4399_;
                        v_isShared_4403_ = v_isSharedCheck_4428_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4400_);
                        crate::leanh::lean_dec(v___x_4399_);
                        v___x_4402_ = crate::leanh::lean_box(0);
                        v_isShared_4403_ = v_isSharedCheck_4428_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_file_4397_);
                    v_a_4429_ = crate::leanh::lean_ctor_get(v___x_4399_, 0);
                    v_isSharedCheck_4436_ = (!crate::leanh::lean_is_exclusive(v___x_4399_)) as u8;
                    if v_isSharedCheck_4436_ == 0 {
                        v___x_4431_ = v___x_4399_;
                        v_isShared_4432_ = v_isSharedCheck_4436_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4429_);
                        crate::leanh::lean_dec(v___x_4399_);
                        v___x_4431_ = crate::leanh::lean_box(0);
                        v_isShared_4432_ = v_isSharedCheck_4436_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4413_ = l_Lean_Json_parse(v_a_4400_);
                if crate::leanh::lean_obj_tag(v___x_4413_) == 0 {
                    v_a_4414_ = crate::leanh::lean_ctor_get(v___x_4413_, 0);
                    crate::leanh::lean_inc(v_a_4414_);
                    crate::leanh::lean_dec_ref_known(v___x_4413_, 1);
                    v___x_4415_ = l_Lake_Manifest_parse___closed__0;
                    v___x_4416_ = lean_string_append(v___x_4415_, v_a_4414_);
                    crate::leanh::lean_dec(v_a_4414_);
                    v_a_4405_ = v___x_4416_;
                    state = 2;
                    continue;
                } else {
                    v_a_4417_ = crate::leanh::lean_ctor_get(v___x_4413_, 0);
                    crate::leanh::lean_inc(v_a_4417_);
                    crate::leanh::lean_dec_ref_known(v___x_4413_, 1);
                    v___x_4418_ = l_Lake_Manifest_fromJson_x3f(v_a_4417_);
                    if crate::leanh::lean_obj_tag(v___x_4418_) == 0 {
                        v_a_4419_ = crate::leanh::lean_ctor_get(v___x_4418_, 0);
                        crate::leanh::lean_inc(v_a_4419_);
                        crate::leanh::lean_dec_ref_known(v___x_4418_, 1);
                        v_a_4405_ = v_a_4419_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_4402_);
                        crate::leanh::lean_dec_ref(v_file_4397_);
                        v_a_4420_ = crate::leanh::lean_ctor_get(v___x_4418_, 0);
                        v_isSharedCheck_4427_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4418_)) as u8;
                        if v_isSharedCheck_4427_ == 0 {
                            v___x_4422_ = v___x_4418_;
                            v_isShared_4423_ = v_isSharedCheck_4427_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4420_);
                            crate::leanh::lean_dec(v___x_4418_);
                            v___x_4422_ = crate::leanh::lean_box(0);
                            v_isShared_4423_ = v_isSharedCheck_4427_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_4406_ = l_Lake_Manifest_load___closed__0;
                v___x_4407_ = lean_string_append(v_file_4397_, v___x_4406_);
                v___x_4408_ = lean_string_append(v___x_4407_, v_a_4405_);
                crate::leanh::lean_dec_ref(v_a_4405_);
                v___x_4409_ = lean_mk_io_user_error(v___x_4408_);
                if v_isShared_4403_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4402_, 1);
                    crate::leanh::lean_ctor_set(v___x_4402_, 0, v___x_4409_);
                    v___x_4411_ = v___x_4402_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4412_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4412_, 0, v___x_4409_);
                    v___x_4411_ = v_reuseFailAlloc_4412_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4411_;
            }
            4 => {
                if v_isShared_4423_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4422_, 0);
                    v___x_4425_ = v___x_4422_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4426_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_a_4420_);
                    v___x_4425_ = v_reuseFailAlloc_4426_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4425_;
            }
            6 => {
                if v_isShared_4432_ == 0 {
                    v___x_4434_ = v___x_4431_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4435_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4429_);
                    v___x_4434_ = v_reuseFailAlloc_4435_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4434_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Manifest_load___boxed(
    mut v_file_4437_: *mut crate::leanh::LeanObject,
    mut v_a_4438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4439_ = l_Lake_Manifest_load(v_file_4437_);
    return v_res_4439_;
}
pub unsafe fn l_Lake_Manifest_load_x3f(
    mut v_file_4440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4451_: u8 = 0;
    let mut v_a_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4468_: u8 = 0;
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4475_: u8 = 0;
    let mut v_isSharedCheck_4476_: u8 = 0;
    let mut v_a_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4447_ = l_IO_FS_readFile(v_file_4440_);
                if crate::leanh::lean_obj_tag(v___x_4447_) == 0 {
                    v_a_4448_ = crate::leanh::lean_ctor_get(v___x_4447_, 0);
                    v_isSharedCheck_4476_ = (!crate::leanh::lean_is_exclusive(v___x_4447_)) as u8;
                    if v_isSharedCheck_4476_ == 0 {
                        v___x_4450_ = v___x_4447_;
                        v_isShared_4451_ = v_isSharedCheck_4476_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4448_);
                        crate::leanh::lean_dec(v___x_4447_);
                        v___x_4450_ = crate::leanh::lean_box(0);
                        v_isShared_4451_ = v_isSharedCheck_4476_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_file_4440_);
                    v_a_4477_ = crate::leanh::lean_ctor_get(v___x_4447_, 0);
                    crate::leanh::lean_inc(v_a_4477_);
                    crate::leanh::lean_dec_ref_known(v___x_4447_, 1);
                    v_a_4443_ = v_a_4477_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4443_) == 11 {
                    crate::leanh::lean_dec_ref_known(v_a_4443_, 2);
                    v___x_4444_ = crate::leanh::lean_box(0);
                    v___x_4445_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4445_, 0, v___x_4444_);
                    return v___x_4445_;
                } else {
                    v___x_4446_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4446_, 0, v_a_4443_);
                    return v___x_4446_;
                }
            }
            2 => {
                v___x_4458_ = l_Lean_Json_parse(v_a_4448_);
                if crate::leanh::lean_obj_tag(v___x_4458_) == 0 {
                    crate::leanh::lean_del_object(v___x_4450_);
                    v_a_4459_ = crate::leanh::lean_ctor_get(v___x_4458_, 0);
                    crate::leanh::lean_inc(v_a_4459_);
                    crate::leanh::lean_dec_ref_known(v___x_4458_, 1);
                    v___x_4460_ = l_Lake_Manifest_parse___closed__0;
                    v___x_4461_ = lean_string_append(v___x_4460_, v_a_4459_);
                    crate::leanh::lean_dec(v_a_4459_);
                    v_a_4453_ = v___x_4461_;
                    state = 3;
                    continue;
                } else {
                    v_a_4462_ = crate::leanh::lean_ctor_get(v___x_4458_, 0);
                    crate::leanh::lean_inc(v_a_4462_);
                    crate::leanh::lean_dec_ref_known(v___x_4458_, 1);
                    v___x_4463_ = l_Lake_Manifest_fromJson_x3f(v_a_4462_);
                    if crate::leanh::lean_obj_tag(v___x_4463_) == 0 {
                        crate::leanh::lean_del_object(v___x_4450_);
                        v_a_4464_ = crate::leanh::lean_ctor_get(v___x_4463_, 0);
                        crate::leanh::lean_inc(v_a_4464_);
                        crate::leanh::lean_dec_ref_known(v___x_4463_, 1);
                        v_a_4453_ = v_a_4464_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_file_4440_);
                        v_a_4465_ = crate::leanh::lean_ctor_get(v___x_4463_, 0);
                        v_isSharedCheck_4475_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4463_)) as u8;
                        if v_isSharedCheck_4475_ == 0 {
                            v___x_4467_ = v___x_4463_;
                            v_isShared_4468_ = v_isSharedCheck_4475_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4465_);
                            crate::leanh::lean_dec(v___x_4463_);
                            v___x_4467_ = crate::leanh::lean_box(0);
                            v_isShared_4468_ = v_isSharedCheck_4475_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_4454_ = l_Lake_Manifest_load___closed__0;
                v___x_4455_ = lean_string_append(v_file_4440_, v___x_4454_);
                v___x_4456_ = lean_string_append(v___x_4455_, v_a_4453_);
                crate::leanh::lean_dec_ref(v_a_4453_);
                v___x_4457_ = lean_mk_io_user_error(v___x_4456_);
                v_a_4443_ = v___x_4457_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_4468_ == 0 {
                    v___x_4470_ = v___x_4467_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4474_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4465_);
                    v___x_4470_ = v_reuseFailAlloc_4474_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4451_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4450_, 0, v___x_4470_);
                    v___x_4472_ = v___x_4450_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4473_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4473_, 0, v___x_4470_);
                    v___x_4472_ = v_reuseFailAlloc_4473_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4472_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Manifest_load_x3f___boxed(
    mut v_file_4478_: *mut crate::leanh::LeanObject,
    mut v_a_4479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4480_ = l_Lake_Manifest_load_x3f(v_file_4478_);
    return v_res_4480_;
}
pub unsafe fn l_Lake_Manifest_save(
    mut v_self_4481_: *mut crate::leanh::LeanObject,
    mut v_manifestFile_4482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contents_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: u32 = 0;
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4484_ = l_Lake_Manifest_toJson(v_self_4481_);
    v___x_4485_ = crate::leanh::lean_unsigned_to_nat(80);
    v_contents_4486_ = l_Lean_Json_pretty(v___x_4484_, v___x_4485_);
    v___x_4487_ = 10;
    v___x_4488_ = lean_string_push(v_contents_4486_, v___x_4487_);
    v___x_4489_ = l_IO_FS_writeFile(v_manifestFile_4482_, v___x_4488_);
    crate::leanh::lean_dec_ref(v___x_4488_);
    return v___x_4489_;
}
pub unsafe fn l_Lake_Manifest_save___boxed(
    mut v_self_4490_: *mut crate::leanh::LeanObject,
    mut v_manifestFile_4491_: *mut crate::leanh::LeanObject,
    mut v_a_4492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4493_ = l_Lake_Manifest_save(v_self_4490_, v_manifestFile_4491_);
    crate::leanh::lean_dec_ref(v_manifestFile_4491_);
    return v_res_4493_;
}
pub unsafe fn l_Lake_Manifest_decodeEntries(
    mut v_data_4494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4499_: u8 = 0;
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4503_: u8 = 0;
    let mut v_a_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4509_: u8 = 0;
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4513_: u8 = 0;
    let mut v_a_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4495_ = l_Lean_Json_getObj_x3f(v_data_4494_);
                if crate::leanh::lean_obj_tag(v___x_4495_) == 0 {
                    v_a_4496_ = crate::leanh::lean_ctor_get(v___x_4495_, 0);
                    v_isSharedCheck_4503_ = (!crate::leanh::lean_is_exclusive(v___x_4495_)) as u8;
                    if v_isSharedCheck_4503_ == 0 {
                        v___x_4498_ = v___x_4495_;
                        v_isShared_4499_ = v_isSharedCheck_4503_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4496_);
                        crate::leanh::lean_dec(v___x_4495_);
                        v___x_4498_ = crate::leanh::lean_box(0);
                        v_isShared_4499_ = v_isSharedCheck_4503_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4504_ = crate::leanh::lean_ctor_get(v___x_4495_, 0);
                    crate::leanh::lean_inc(v_a_4504_);
                    crate::leanh::lean_dec_ref_known(v___x_4495_, 1);
                    v___x_4505_ =
                        l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_a_4504_);
                    if crate::leanh::lean_obj_tag(v___x_4505_) == 0 {
                        crate::leanh::lean_dec(v_a_4504_);
                        v_a_4506_ = crate::leanh::lean_ctor_get(v___x_4505_, 0);
                        v_isSharedCheck_4513_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4505_)) as u8;
                        if v_isSharedCheck_4513_ == 0 {
                            v___x_4508_ = v___x_4505_;
                            v_isShared_4509_ = v_isSharedCheck_4513_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4506_);
                            crate::leanh::lean_dec(v___x_4505_);
                            v___x_4508_ = crate::leanh::lean_box(0);
                            v_isShared_4509_ = v_isSharedCheck_4513_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4514_ = crate::leanh::lean_ctor_get(v___x_4505_, 0);
                        crate::leanh::lean_inc(v_a_4514_);
                        crate::leanh::lean_dec_ref_known(v___x_4505_, 1);
                        v___x_4515_ = l_Lake_Manifest_version___closed__1;
                        v___x_4516_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4516_, 0, v_a_4514_);
                        crate::leanh::lean_ctor_set(v___x_4516_, 1, v___x_4515_);
                        v___x_4517_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(
                            v___x_4516_,
                            v_a_4504_,
                        );
                        crate::leanh::lean_dec(v_a_4504_);
                        crate::leanh::lean_dec_ref_known(v___x_4516_, 2);
                        return v___x_4517_;
                    }
                }
            }
            1 => {
                if v_isShared_4499_ == 0 {
                    v___x_4501_ = v___x_4498_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4502_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_a_4496_);
                    v___x_4501_ = v_reuseFailAlloc_4502_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4501_;
            }
            3 => {
                if v_isShared_4509_ == 0 {
                    v___x_4511_ = v___x_4508_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4512_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4506_);
                    v___x_4511_ = v_reuseFailAlloc_4512_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4511_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Manifest_parseEntries(
    mut v_data_4518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4523_: u8 = 0;
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4529_: u8 = 0;
    let mut v_a_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4519_ = l_Lean_Json_parse(v_data_4518_);
                if crate::leanh::lean_obj_tag(v___x_4519_) == 0 {
                    v_a_4520_ = crate::leanh::lean_ctor_get(v___x_4519_, 0);
                    v_isSharedCheck_4529_ = (!crate::leanh::lean_is_exclusive(v___x_4519_)) as u8;
                    if v_isSharedCheck_4529_ == 0 {
                        v___x_4522_ = v___x_4519_;
                        v_isShared_4523_ = v_isSharedCheck_4529_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4520_);
                        crate::leanh::lean_dec(v___x_4519_);
                        v___x_4522_ = crate::leanh::lean_box(0);
                        v_isShared_4523_ = v_isSharedCheck_4529_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4530_ = crate::leanh::lean_ctor_get(v___x_4519_, 0);
                    crate::leanh::lean_inc(v_a_4530_);
                    crate::leanh::lean_dec_ref_known(v___x_4519_, 1);
                    v___x_4531_ = l_Lake_Manifest_decodeEntries(v_a_4530_);
                    return v___x_4531_;
                }
            }
            1 => {
                v___x_4524_ = l_Lake_Manifest_parse___closed__0;
                v___x_4525_ = lean_string_append(v___x_4524_, v_a_4520_);
                crate::leanh::lean_dec(v_a_4520_);
                if v_isShared_4523_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4522_, 0, v___x_4525_);
                    v___x_4527_ = v___x_4522_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4528_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4528_, 0, v___x_4525_);
                    v___x_4527_ = v_reuseFailAlloc_4528_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4527_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Manifest_loadEntries(
    mut v_file_4532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4538_: u8 = 0;
    let mut v_a_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4558_: u8 = 0;
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4562_: u8 = 0;
    let mut v_isSharedCheck_4563_: u8 = 0;
    let mut v_a_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4567_: u8 = 0;
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4571_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4534_ = l_IO_FS_readFile(v_file_4532_);
                if crate::leanh::lean_obj_tag(v___x_4534_) == 0 {
                    v_a_4535_ = crate::leanh::lean_ctor_get(v___x_4534_, 0);
                    v_isSharedCheck_4563_ = (!crate::leanh::lean_is_exclusive(v___x_4534_)) as u8;
                    if v_isSharedCheck_4563_ == 0 {
                        v___x_4537_ = v___x_4534_;
                        v_isShared_4538_ = v_isSharedCheck_4563_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4535_);
                        crate::leanh::lean_dec(v___x_4534_);
                        v___x_4537_ = crate::leanh::lean_box(0);
                        v_isShared_4538_ = v_isSharedCheck_4563_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_file_4532_);
                    v_a_4564_ = crate::leanh::lean_ctor_get(v___x_4534_, 0);
                    v_isSharedCheck_4571_ = (!crate::leanh::lean_is_exclusive(v___x_4534_)) as u8;
                    if v_isSharedCheck_4571_ == 0 {
                        v___x_4566_ = v___x_4534_;
                        v_isShared_4567_ = v_isSharedCheck_4571_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4564_);
                        crate::leanh::lean_dec(v___x_4534_);
                        v___x_4566_ = crate::leanh::lean_box(0);
                        v_isShared_4567_ = v_isSharedCheck_4571_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4548_ = l_Lean_Json_parse(v_a_4535_);
                if crate::leanh::lean_obj_tag(v___x_4548_) == 0 {
                    v_a_4549_ = crate::leanh::lean_ctor_get(v___x_4548_, 0);
                    crate::leanh::lean_inc(v_a_4549_);
                    crate::leanh::lean_dec_ref_known(v___x_4548_, 1);
                    v___x_4550_ = l_Lake_Manifest_parse___closed__0;
                    v___x_4551_ = lean_string_append(v___x_4550_, v_a_4549_);
                    crate::leanh::lean_dec(v_a_4549_);
                    v_a_4540_ = v___x_4551_;
                    state = 2;
                    continue;
                } else {
                    v_a_4552_ = crate::leanh::lean_ctor_get(v___x_4548_, 0);
                    crate::leanh::lean_inc(v_a_4552_);
                    crate::leanh::lean_dec_ref_known(v___x_4548_, 1);
                    v___x_4553_ = l_Lake_Manifest_decodeEntries(v_a_4552_);
                    if crate::leanh::lean_obj_tag(v___x_4553_) == 0 {
                        v_a_4554_ = crate::leanh::lean_ctor_get(v___x_4553_, 0);
                        crate::leanh::lean_inc(v_a_4554_);
                        crate::leanh::lean_dec_ref_known(v___x_4553_, 1);
                        v_a_4540_ = v_a_4554_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_4537_);
                        crate::leanh::lean_dec_ref(v_file_4532_);
                        v_a_4555_ = crate::leanh::lean_ctor_get(v___x_4553_, 0);
                        v_isSharedCheck_4562_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4553_)) as u8;
                        if v_isSharedCheck_4562_ == 0 {
                            v___x_4557_ = v___x_4553_;
                            v_isShared_4558_ = v_isSharedCheck_4562_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4555_);
                            crate::leanh::lean_dec(v___x_4553_);
                            v___x_4557_ = crate::leanh::lean_box(0);
                            v_isShared_4558_ = v_isSharedCheck_4562_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_4541_ = l_Lake_Manifest_load___closed__0;
                v___x_4542_ = lean_string_append(v_file_4532_, v___x_4541_);
                v___x_4543_ = lean_string_append(v___x_4542_, v_a_4540_);
                crate::leanh::lean_dec_ref(v_a_4540_);
                v___x_4544_ = lean_mk_io_user_error(v___x_4543_);
                if v_isShared_4538_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4537_, 1);
                    crate::leanh::lean_ctor_set(v___x_4537_, 0, v___x_4544_);
                    v___x_4546_ = v___x_4537_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4547_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4547_, 0, v___x_4544_);
                    v___x_4546_ = v_reuseFailAlloc_4547_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4546_;
            }
            4 => {
                if v_isShared_4558_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4557_, 0);
                    v___x_4560_ = v___x_4557_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4561_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4555_);
                    v___x_4560_ = v_reuseFailAlloc_4561_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4560_;
            }
            6 => {
                if v_isShared_4567_ == 0 {
                    v___x_4569_ = v___x_4566_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4570_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_a_4564_);
                    v___x_4569_ = v_reuseFailAlloc_4570_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4569_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Manifest_loadEntries___boxed(
    mut v_file_4572_: *mut crate::leanh::LeanObject,
    mut v_a_4573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4574_ = l_Lake_Manifest_loadEntries(v_file_4572_);
    return v_res_4574_;
}
pub unsafe fn l_Lake_Manifest_tryLoadEntries(
    mut v_file_4575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4591_: u8 = 0;
    let mut v_a_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4609_: u8 = 0;
    let mut v_a_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4587_ = l_IO_FS_readFile(v_file_4575_);
                if crate::leanh::lean_obj_tag(v___x_4587_) == 0 {
                    v_a_4588_ = crate::leanh::lean_ctor_get(v___x_4587_, 0);
                    v_isSharedCheck_4609_ = (!crate::leanh::lean_is_exclusive(v___x_4587_)) as u8;
                    if v_isSharedCheck_4609_ == 0 {
                        v___x_4590_ = v___x_4587_;
                        v_isShared_4591_ = v_isSharedCheck_4609_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4588_);
                        crate::leanh::lean_dec(v___x_4587_);
                        v___x_4590_ = crate::leanh::lean_box(0);
                        v_isShared_4591_ = v_isSharedCheck_4609_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4610_ = crate::leanh::lean_ctor_get(v___x_4587_, 0);
                    crate::leanh::lean_inc(v_a_4610_);
                    crate::leanh::lean_dec_ref_known(v___x_4587_, 1);
                    v_a_4578_ = v_a_4610_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4578_) == 11 {
                    crate::leanh::lean_dec_ref_known(v_a_4578_, 2);
                    crate::leanh::lean_dec_ref(v_file_4575_);
                    v___x_4579_ =
                        l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__1;
                    v___x_4580_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4580_, 0, v___x_4579_);
                    return v___x_4580_;
                } else {
                    v___x_4581_ = l_Lake_Manifest_load___closed__0;
                    v___x_4582_ = lean_string_append(v_file_4575_, v___x_4581_);
                    v___x_4583_ = lean_io_error_to_string(v_a_4578_);
                    v___x_4584_ = lean_string_append(v___x_4582_, v___x_4583_);
                    crate::leanh::lean_dec_ref(v___x_4583_);
                    v___x_4585_ = lean_mk_io_user_error(v___x_4584_);
                    v___x_4586_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4586_, 0, v___x_4585_);
                    return v___x_4586_;
                }
            }
            2 => {
                v___x_4598_ = l_Lean_Json_parse(v_a_4588_);
                if crate::leanh::lean_obj_tag(v___x_4598_) == 0 {
                    crate::leanh::lean_del_object(v___x_4590_);
                    v_a_4599_ = crate::leanh::lean_ctor_get(v___x_4598_, 0);
                    crate::leanh::lean_inc(v_a_4599_);
                    crate::leanh::lean_dec_ref_known(v___x_4598_, 1);
                    v___x_4600_ = l_Lake_Manifest_parse___closed__0;
                    v___x_4601_ = lean_string_append(v___x_4600_, v_a_4599_);
                    crate::leanh::lean_dec(v_a_4599_);
                    v_a_4593_ = v___x_4601_;
                    state = 3;
                    continue;
                } else {
                    v_a_4602_ = crate::leanh::lean_ctor_get(v___x_4598_, 0);
                    crate::leanh::lean_inc(v_a_4602_);
                    crate::leanh::lean_dec_ref_known(v___x_4598_, 1);
                    v___x_4603_ = l_Lake_Manifest_decodeEntries(v_a_4602_);
                    if crate::leanh::lean_obj_tag(v___x_4603_) == 0 {
                        crate::leanh::lean_del_object(v___x_4590_);
                        v_a_4604_ = crate::leanh::lean_ctor_get(v___x_4603_, 0);
                        crate::leanh::lean_inc(v_a_4604_);
                        crate::leanh::lean_dec_ref_known(v___x_4603_, 1);
                        v_a_4593_ = v_a_4604_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_file_4575_);
                        v_a_4605_ = crate::leanh::lean_ctor_get(v___x_4603_, 0);
                        crate::leanh::lean_inc(v_a_4605_);
                        crate::leanh::lean_dec_ref_known(v___x_4603_, 1);
                        if v_isShared_4591_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4590_, 0, v_a_4605_);
                            v___x_4607_ = v___x_4590_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4608_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4608_, 0, v_a_4605_);
                            v___x_4607_ = v_reuseFailAlloc_4608_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_4594_ = l_Lake_Manifest_load___closed__0;
                crate::leanh::lean_inc_ref(v_file_4575_);
                v___x_4595_ = lean_string_append(v_file_4575_, v___x_4594_);
                v___x_4596_ = lean_string_append(v___x_4595_, v_a_4593_);
                crate::leanh::lean_dec_ref(v_a_4593_);
                v___x_4597_ = lean_mk_io_user_error(v___x_4596_);
                v_a_4578_ = v___x_4597_;
                state = 1;
                continue;
            }
            4 => {
                return v___x_4607_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Manifest_tryLoadEntries___boxed(
    mut v_file_4611_: *mut crate::leanh::LeanObject,
    mut v_a_4612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4613_ = l_Lake_Manifest_tryLoadEntries(v_file_4611_);
    return v_res_4613_;
}
pub unsafe fn _init_l_Lake_Manifest_saveEntries___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4614_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Manifest_toJson___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Manifest_toJson___closed__2_once),
        _init_l_Lake_Manifest_toJson___closed__2,
    );
    v___x_4615_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7;
    v___x_4616_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4616_, 0, v___x_4615_);
    crate::leanh::lean_ctor_set(v___x_4616_, 1, v___x_4614_);
    return v___x_4616_;
}
pub unsafe fn l_Lake_Manifest_saveEntries(
    mut v_file_4617_: *mut crate::leanh::LeanObject,
    mut v_entries_4618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contents_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: u32 = 0;
    let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4620_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Manifest_saveEntries___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Manifest_saveEntries___closed__0_once),
        _init_l_Lake_Manifest_saveEntries___closed__0,
    );
    v___x_4621_ = l_Lake_Manifest_toJson___closed__7;
    v___x_4622_ = l_Array_toJson___at___00Lake_Manifest_toJson_spec__0(v_entries_4618_);
    v___x_4623_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4623_, 0, v___x_4621_);
    crate::leanh::lean_ctor_set(v___x_4623_, 1, v___x_4622_);
    v___x_4624_ = crate::leanh::lean_box(0);
    v___x_4625_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4625_, 0, v___x_4623_);
    crate::leanh::lean_ctor_set(v___x_4625_, 1, v___x_4624_);
    v___x_4626_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4626_, 0, v___x_4620_);
    crate::leanh::lean_ctor_set(v___x_4626_, 1, v___x_4625_);
    v___x_4627_ = l_Lean_Json_mkObj(v___x_4626_);
    crate::leanh::lean_dec_ref_known(v___x_4626_, 2);
    v___x_4628_ = crate::leanh::lean_unsigned_to_nat(80);
    v_contents_4629_ = l_Lean_Json_pretty(v___x_4627_, v___x_4628_);
    v___x_4630_ = 10;
    v___x_4631_ = lean_string_push(v_contents_4629_, v___x_4630_);
    v___x_4632_ = l_IO_FS_writeFile(v_file_4617_, v___x_4631_);
    crate::leanh::lean_dec_ref(v___x_4631_);
    return v___x_4632_;
}
pub unsafe fn l_Lake_Manifest_saveEntries___boxed(
    mut v_file_4633_: *mut crate::leanh::LeanObject,
    mut v_entries_4634_: *mut crate::leanh::LeanObject,
    mut v_a_4635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4636_ = l_Lake_Manifest_saveEntries(v_file_4633_, v_entries_4634_);
    crate::leanh::lean_dec_ref(v_file_4633_);
    return v_res_4636_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Load_Manifest(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Util_Version(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Defaults(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Git(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Error(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_FilePath(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_JsonObject(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Coe(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lake_instInhabitedPackageEntry_default = _init_l_Lake_instInhabitedPackageEntry_default();
    crate::leanh::lean_mark_persistent(l_Lake_instInhabitedPackageEntry_default);
    l_Lake_instInhabitedPackageEntry = _init_l_Lake_instInhabitedPackageEntry();
    crate::leanh::lean_mark_persistent(l_Lake_instInhabitedPackageEntry);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Load_Manifest(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Load_Manifest(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Util_Version(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Defaults(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Git(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Error(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_FilePath(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_JsonObject(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Coe(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Manifest(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Load_Manifest(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Load_Manifest(builtin);
}
