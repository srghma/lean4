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
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_lt, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Ord::String::lean_string_compare;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_array_get_borrowed, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_mul, lean_panic_fn_borrowed,
    lean_string_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_4, lean_apply_7,
    lean_box, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l_Lake_Manifest_version___closed__0_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((1 as usize) << 1) | 1) as *mut LeanObject,
        (((2 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_Manifest_version___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_version___closed__0_value) as *mut LeanObject;
pub static l_Lake_Manifest_version___closed__1_value: LeanStringObject<1> = LeanStringObject {
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
static mut l_Lake_Manifest_version___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_version___closed__1_value) as *mut LeanObject;
pub static l_Lake_Manifest_version___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Manifest_version___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Manifest_version___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Manifest_version___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_version___closed__2_value) as *mut LeanObject;
pub static mut l_Lake_Manifest_version: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_version___closed__2_value) as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [91, 97, 110, 111, 110, 121, 109, 111, 117, 115, 93, 0]};
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__1_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 96, 78, 97, 109, 101, 96, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0___closed__0_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 96, 78, 97, 109, 101, 77, 97, 112, 96, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__0_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 97, 103, 32, 102, 111, 117, 110, 100, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__0_value) as *mut LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__1_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 97, 116, 104, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [103, 105, 116, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__4_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 109, 97, 116, 99, 104, 101, 100, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__4_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__5_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__4_value) as *mut LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__5_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 97, 109, 101, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6_value) as *mut LeanObject,5949480926448383572 as *mut LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__7_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__8_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [111, 112, 116, 115, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__8_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__8_value) as *mut LeanObject,6757902475951869745 as *mut LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__9_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 104, 101, 114, 105, 116, 101, 100, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10_value) as *mut LeanObject,12300627446236246789 as *mut LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__11_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [117, 114, 108, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12_value) as *mut LeanObject,13553787595962583263 as *mut LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__13_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [114, 101, 118, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14_value) as *mut LeanObject,13413232538026238679 as *mut LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__15_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 112, 117, 116, 82, 101, 118, 63, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__16_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__16_value) as *mut LeanObject,12690480075422432291 as *mut LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__17_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__18_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [115, 117, 98, 68, 105, 114, 63, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__18_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__19_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__18_value) as *mut LeanObject,2445562219981734856 as *mut LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__19_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__20_value: LeanArrayObject<7> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*7) as u16, other: 0, tag: 246 }, m_size: 7, m_capacity: 7, m_data: [core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__13_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__15_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__17_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__19_value) as *mut LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__20_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__21_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__20_value) as *mut LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__21_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [100, 105, 114, 0]};
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__23_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22_value) as *mut LeanObject,13475008931517935237 as *mut LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__23: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__23_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__24_value: LeanArrayObject<4> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*4) as u16, other: 0, tag: 246 }, m_size: 4, m_capacity: 4, m_data: [core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__23_value) as *mut LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__24: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__24_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__25_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__24_value) as *mut LeanObject] };
static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__25: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__25_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6___closed__0_value
) as *mut LeanObject;
pub static mut l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6___closed__0_value
)
    as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__0_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 66, 97, 108, 97, 110, 99, 105, 110, 103, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__1_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 76, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__2_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 76, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__2_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__5_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 82, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__5_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__6_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 82, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__6_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6___closed__0_value
) as *mut LeanObject;
pub static mut l___private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6___closed__0_value
)
    as *mut LeanObject;
pub static l_Lake_instInhabitedPackageEntryV6_default___closed__0_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_Manifest_version___closed__1_value) as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lake_instInhabitedPackageEntryV6_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedPackageEntryV6_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lake_instInhabitedPackageEntryV6_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedPackageEntryV6_default___closed__0_value)
        as *mut LeanObject;
pub static mut l___private_Lake_Load_Manifest_0__Lake_instInhabitedPackageEntryV6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedPackageEntryV6_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedPackageEntrySrc_default___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_Manifest_version___closed__1_value) as *mut LeanObject],
    };
static mut l_Lake_instInhabitedPackageEntrySrc_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedPackageEntrySrc_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lake_instInhabitedPackageEntrySrc_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedPackageEntrySrc_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lake_instInhabitedPackageEntrySrc: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedPackageEntrySrc_default___closed__0_value)
        as *mut LeanObject;
static mut l_Lake_instInhabitedPackageEntry_default___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedPackageEntry_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedPackageEntry_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_instInhabitedPackageEntry: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_PackageEntry_toJson___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_PackageEntry_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__0_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_toJson___closed__1_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_PackageEntry_toJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__1_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_toJson___closed__2_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_PackageEntry_toJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__2_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_toJson___closed__3_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_PackageEntry_toJson___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__3_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_toJson___closed__4_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2_value) as *mut LeanObject] };
static mut l_Lake_PackageEntry_toJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__4_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_toJson___closed__5_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_PackageEntry_toJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__5_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_toJson___closed__6_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3_value) as *mut LeanObject] };
static mut l_Lake_PackageEntry_toJson___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__6_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_toJson___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_PackageEntry_toJson___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__7_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_toJson___closed__8_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_PackageEntry_toJson___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__8_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_toJson___closed__9_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_PackageEntry_toJson___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_toJson___closed__9_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_instToJson___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_PackageEntry_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_PackageEntry_instToJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_instToJson___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_PackageEntry_instToJson: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_instToJson___closed__0_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___lam__0___closed__0_value: LeanStringObject<16> =
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
            112, 97, 99, 107, 97, 103, 101, 32, 101, 110, 116, 114, 121, 58, 32, 0,
        ],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__0_value: LeanStringObject<25> =
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
            112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
            58, 32, 110, 97, 109, 101, 0,
        ],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__1_value: LeanStringObject<7> =
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
        m_data: [110, 97, 109, 101, 58, 32, 0],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__2_value: LeanStringObject<16> =
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
            112, 97, 99, 107, 97, 103, 101, 32, 101, 110, 116, 114, 121, 32, 39, 0,
        ],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__2_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__3_value: LeanStringObject<4> =
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
        m_data: [39, 58, 32, 0],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__3_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__4_value: LeanStringObject<9> =
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
        m_data: [115, 117, 98, 68, 105, 114, 58, 32, 0],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__4_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__5_value: LeanStringObject<29> =
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
            117, 110, 107, 110, 111, 119, 110, 32, 112, 97, 99, 107, 97, 103, 101, 32, 101, 110,
            116, 114, 121, 32, 116, 121, 112, 101, 32, 39, 0,
        ],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__5_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__6_value: LeanStringObject<24> =
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
            112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
            58, 32, 117, 114, 108, 0,
        ],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__6_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__7_value: LeanStringObject<6> =
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
        m_data: [117, 114, 108, 58, 32, 0],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__7_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__8_value: LeanStringObject<24> =
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
            112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
            58, 32, 114, 101, 118, 0,
        ],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__8_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__9_value: LeanStringObject<6> =
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
        m_data: [114, 101, 118, 58, 32, 0],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__9_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__10_value: LeanStringObject<11> =
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
        m_data: [105, 110, 112, 117, 116, 82, 101, 118, 58, 32, 0],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__10_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__11_value: LeanStringObject<24> =
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
            112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
            58, 32, 100, 105, 114, 0,
        ],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__11_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__12_value: LeanStringObject<6> =
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
        m_data: [100, 105, 114, 58, 32, 0],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__12_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__13_value: LeanStringObject<15> =
    LeanStringObject {
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
            109, 97, 110, 105, 102, 101, 115, 116, 70, 105, 108, 101, 58, 32, 0,
        ],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__13_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__14_value: LeanStringObject<25> =
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
            112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
            58, 32, 116, 121, 112, 101, 0,
        ],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__14_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__15_value: LeanStringObject<7> =
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
        m_data: [116, 121, 112, 101, 58, 32, 0],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__15_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__16_value: LeanStringObject<30> =
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
            112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
            58, 32, 105, 110, 104, 101, 114, 105, 116, 101, 100, 0,
        ],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__16_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__17_value: LeanStringObject<12> =
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
        m_data: [105, 110, 104, 101, 114, 105, 116, 101, 100, 58, 32, 0],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__17_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__18_value: LeanStringObject<13> =
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
        m_data: [99, 111, 110, 102, 105, 103, 70, 105, 108, 101, 58, 32, 0],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__18_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_fromJson_x3f___closed__19_value: LeanStringObject<8> =
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
        m_data: [115, 99, 111, 112, 101, 58, 32, 0],
    };
static mut l_Lake_PackageEntry_fromJson_x3f___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_fromJson_x3f___closed__19_value) as *mut LeanObject;
pub static l_Lake_PackageEntry_instFromJson___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_PackageEntry_fromJson_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_PackageEntry_instFromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_instFromJson___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_PackageEntry_instFromJson: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_PackageEntry_instFromJson___closed__0_value) as *mut LeanObject;
pub static l_Lake_Manifest_toJson___closed__0_value: LeanStringObject<8> = LeanStringObject {
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
static mut l_Lake_Manifest_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_toJson___closed__0_value) as *mut LeanObject;
static mut l_Lake_Manifest_toJson___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Manifest_toJson___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Manifest_toJson___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Manifest_toJson___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_Manifest_toJson___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Manifest_toJson___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Manifest_toJson___closed__4_value: LeanStringObject<15> = LeanStringObject {
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
        102, 105, 120, 101, 100, 84, 111, 111, 108, 99, 104, 97, 105, 110, 0,
    ],
};
static mut l_Lake_Manifest_toJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_toJson___closed__4_value) as *mut LeanObject;
pub static l_Lake_Manifest_toJson___closed__5_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Manifest_toJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_toJson___closed__5_value) as *mut LeanObject;
pub static l_Lake_Manifest_toJson___closed__6_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Manifest_toJson___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_toJson___closed__6_value) as *mut LeanObject;
pub static l_Lake_Manifest_toJson___closed__7_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Manifest_toJson___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_toJson___closed__7_value) as *mut LeanObject;
pub static l_Lake_Manifest_instToJson___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Manifest_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Manifest_instToJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_instToJson___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Manifest_instToJson: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_instToJson___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__0_value:
    LeanStringObject<32> = LeanStringObject {
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
        105, 110, 99, 111, 109, 112, 97, 116, 105, 98, 108, 101, 32, 109, 97, 110, 105, 102, 101,
        115, 116, 32, 118, 101, 114, 115, 105, 111, 110, 32, 39, 0,
    ],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__0_value
)
    as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        (((5 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__1_value
)
    as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__2_value:
    LeanStringObject<17> = LeanStringObject {
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
        115, 99, 104, 101, 109, 97, 32, 118, 101, 114, 115, 105, 111, 110, 32, 39, 0,
    ],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__2: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__2_value
)
    as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__3_value:
    LeanStringObject<50> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__3: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__3_value
)
    as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4_value:
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
        39, 59, 32, 121, 111, 117, 32, 109, 97, 121, 32, 110, 101, 101, 100, 32, 116, 111, 32, 117,
        112, 100, 97, 116, 101, 32, 121, 111, 117, 114, 32, 39, 108, 101, 97, 110, 45, 116, 111,
        111, 108, 99, 104, 97, 105, 110, 39, 0,
    ],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4_value
)
    as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__5_value:
    LeanStringObject<18> = LeanStringObject {
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
        105, 110, 118, 97, 108, 105, 100, 32, 118, 101, 114, 115, 105, 111, 110, 32, 39, 0,
    ],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__5: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__5_value
)
    as *mut LeanObject;
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7_value:
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
        115, 99, 104, 101, 109, 97, 86, 101, 114, 115, 105, 111, 110, 0,
    ],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7_value
)
    as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__8_value:
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
        112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 58,
        32, 115, 99, 104, 101, 109, 97, 86, 101, 114, 115, 105, 111, 110, 0,
    ],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__8: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__8_value
)
    as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__9_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__8_value
    ) as *mut LeanObject],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__9: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__9_value
)
    as *mut LeanObject;
pub static l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1___closed__0_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__0_value:
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
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__1_value:
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
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__2_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__1_value
    ) as *mut LeanObject],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__2_value
) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__3_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        (((7 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__3_value
) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__4_value:
    LeanCtorObject<2> = LeanCtorObject {
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
            l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Manifest_version___closed__1_value) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__4_value
) as *mut LeanObject;
pub static l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__5_value:
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
    m_data: [112, 97, 99, 107, 97, 103, 101, 115, 58, 32, 0],
};
static mut l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__5_value
) as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0___closed__0_value:
    LeanCtorObject<1> = LeanCtorObject {
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
static mut l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1___closed__0_value:
    LeanCtorObject<1> = LeanCtorObject {
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
static mut l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1___closed__0_value
) as *mut LeanObject;
pub static l_Lake_Manifest_fromJson_x3f___closed__0_value: LeanStringObject<14> =
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
        m_data: [112, 97, 99, 107, 97, 103, 101, 115, 68, 105, 114, 58, 32, 0],
    };
static mut l_Lake_Manifest_fromJson_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_fromJson_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_Manifest_fromJson_x3f___closed__1_value: LeanStringObject<10> =
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
        m_data: [108, 97, 107, 101, 68, 105, 114, 58, 32, 0],
    };
static mut l_Lake_Manifest_fromJson_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_fromJson_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lake_Manifest_fromJson_x3f___closed__2_value: LeanStringObject<17> =
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
            102, 105, 120, 101, 100, 84, 111, 111, 108, 99, 104, 97, 105, 110, 58, 32, 0,
        ],
    };
static mut l_Lake_Manifest_fromJson_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_fromJson_x3f___closed__2_value) as *mut LeanObject;
pub static l_Lake_Manifest_instFromJson___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_Manifest_fromJson_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Manifest_instFromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_instFromJson___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Manifest_instFromJson: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_instFromJson___closed__0_value) as *mut LeanObject;
pub static l_Lake_Manifest_parse___closed__0_value: LeanStringObject<15> = LeanStringObject {
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
        105, 110, 118, 97, 108, 105, 100, 32, 74, 83, 79, 78, 58, 32, 0,
    ],
};
static mut l_Lake_Manifest_parse___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_parse___closed__0_value) as *mut LeanObject;
pub static l_Lake_Manifest_load___closed__0_value: LeanStringObject<3> = LeanStringObject {
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
static mut l_Lake_Manifest_load___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Manifest_load___closed__0_value) as *mut LeanObject;
static mut l_Lake_Manifest_saveEntries___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Manifest_saveEntries___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorIdx(
    mut v_x_2328_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2328_) == 0 {
        let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
        v___x_2329_ = lean_unsigned_to_nat(0);
        return v___x_2329_;
    } else {
        let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
        v___x_2330_ = lean_unsigned_to_nat(1);
        return v___x_2330_;
    }
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorIdx___boxed(
    mut v_x_2331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2332_: *mut LeanObject = core::ptr::null_mut();
    v_res_2332_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorIdx(v_x_2331_);
    lean_dec_ref(v_x_2331_);
    return v_res_2332_;
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(
    mut v_t_2333_: *mut LeanObject,
    mut v_k_2334_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_2333_) == 0 {
        let mut v_name_2335_: *mut LeanObject = core::ptr::null_mut();
        let mut v_opts_2336_: *mut LeanObject = core::ptr::null_mut();
        let mut v_inherited_2337_: u8 = 0;
        let mut v_dir_2338_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
        v_name_2335_ = lean_ctor_get(v_t_2333_, 0);
        lean_inc(v_name_2335_);
        v_opts_2336_ = lean_ctor_get(v_t_2333_, 1);
        lean_inc(v_opts_2336_);
        v_inherited_2337_ = lean_ctor_get_uint8(
            v_t_2333_,
            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        );
        v_dir_2338_ = lean_ctor_get(v_t_2333_, 2);
        lean_inc_ref(v_dir_2338_);
        lean_dec_ref_known(v_t_2333_, 3);
        v___x_2339_ = lean_box((v_inherited_2337_) as usize);
        v___x_2340_ = lean_apply_4(
            v_k_2334_,
            v_name_2335_,
            v_opts_2336_,
            v___x_2339_,
            v_dir_2338_,
        );
        return v___x_2340_;
    } else {
        let mut v_name_2341_: *mut LeanObject = core::ptr::null_mut();
        let mut v_opts_2342_: *mut LeanObject = core::ptr::null_mut();
        let mut v_inherited_2343_: u8 = 0;
        let mut v_url_2344_: *mut LeanObject = core::ptr::null_mut();
        let mut v_rev_2345_: *mut LeanObject = core::ptr::null_mut();
        let mut v_inputRev_x3f_2346_: *mut LeanObject = core::ptr::null_mut();
        let mut v_subDir_x3f_2347_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
        v_name_2341_ = lean_ctor_get(v_t_2333_, 0);
        lean_inc(v_name_2341_);
        v_opts_2342_ = lean_ctor_get(v_t_2333_, 1);
        lean_inc(v_opts_2342_);
        v_inherited_2343_ = lean_ctor_get_uint8(
            v_t_2333_,
            (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
        );
        v_url_2344_ = lean_ctor_get(v_t_2333_, 2);
        lean_inc_ref(v_url_2344_);
        v_rev_2345_ = lean_ctor_get(v_t_2333_, 3);
        lean_inc_ref(v_rev_2345_);
        v_inputRev_x3f_2346_ = lean_ctor_get(v_t_2333_, 4);
        lean_inc(v_inputRev_x3f_2346_);
        v_subDir_x3f_2347_ = lean_ctor_get(v_t_2333_, 5);
        lean_inc(v_subDir_x3f_2347_);
        lean_dec_ref_known(v_t_2333_, 6);
        v___x_2348_ = lean_box((v_inherited_2343_) as usize);
        v___x_2349_ = lean_apply_7(
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
    mut v_motive_2350_: *mut LeanObject,
    mut v_ctorIdx_2351_: *mut LeanObject,
    mut v_t_2352_: *mut LeanObject,
    mut v_h_2353_: *mut LeanObject,
    mut v_k_2354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    v___x_2355_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(
        v_t_2352_, v_k_2354_,
    );
    return v___x_2355_;
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___boxed(
    mut v_motive_2356_: *mut LeanObject,
    mut v_ctorIdx_2357_: *mut LeanObject,
    mut v_t_2358_: *mut LeanObject,
    mut v_h_2359_: *mut LeanObject,
    mut v_k_2360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2361_: *mut LeanObject = core::ptr::null_mut();
    v_res_2361_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim(
        v_motive_2356_,
        v_ctorIdx_2357_,
        v_t_2358_,
        v_h_2359_,
        v_k_2360_,
    );
    lean_dec(v_ctorIdx_2357_);
    return v_res_2361_;
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_path_elim___redArg(
    mut v_t_2362_: *mut LeanObject,
    mut v_path_2363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    v___x_2364_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(
        v_t_2362_,
        v_path_2363_,
    );
    return v___x_2364_;
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_path_elim(
    mut v_motive_2365_: *mut LeanObject,
    mut v_t_2366_: *mut LeanObject,
    mut v_h_2367_: *mut LeanObject,
    mut v_path_2368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    v___x_2369_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(
        v_t_2366_,
        v_path_2368_,
    );
    return v___x_2369_;
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_git_elim___redArg(
    mut v_t_2370_: *mut LeanObject,
    mut v_git_2371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    v___x_2372_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(
        v_t_2370_,
        v_git_2371_,
    );
    return v___x_2372_;
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_git_elim(
    mut v_motive_2373_: *mut LeanObject,
    mut v_t_2374_: *mut LeanObject,
    mut v_h_2375_: *mut LeanObject,
    mut v_git_2376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    v___x_2377_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntryV6_ctorElim___redArg(
        v_t_2374_,
        v_git_2376_,
    );
    return v___x_2377_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(
    mut v_x_2380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2386_: u8 = 0;
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2390_: u8 = 0;
    let mut v_a_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2394_: u8 = 0;
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2399_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2380_) == 0 {
                    v___x_2381_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0;
                    return v___x_2381_;
                } else {
                    v___x_2382_ = l_Lean_Json_getStr_x3f(v_x_2380_);
                    if lean_obj_tag(v___x_2382_) == 0 {
                        v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
                        v_isSharedCheck_2390_ = (!lean_is_exclusive(v___x_2382_)) as u8;
                        if v_isSharedCheck_2390_ == 0 {
                            v___x_2385_ = v___x_2382_;
                            v_isShared_2386_ = v_isSharedCheck_2390_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2383_);
                            lean_dec(v___x_2382_);
                            v___x_2385_ = lean_box(0);
                            v_isShared_2386_ = v_isSharedCheck_2390_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2391_ = lean_ctor_get(v___x_2382_, 0);
                        v_isSharedCheck_2399_ = (!lean_is_exclusive(v___x_2382_)) as u8;
                        if v_isSharedCheck_2399_ == 0 {
                            v___x_2393_ = v___x_2382_;
                            v_isShared_2394_ = v_isSharedCheck_2399_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2391_);
                            lean_dec(v___x_2382_);
                            v___x_2393_ = lean_box(0);
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
                    v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2383_);
                    v___x_2388_ = v_reuseFailAlloc_2389_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2388_;
            }
            3 => {
                v___x_2395_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2395_, 0, v_a_2391_);
                if v_isShared_2394_ == 0 {
                    lean_ctor_set(v___x_2393_, 0, v___x_2395_);
                    v___x_2397_ = v___x_2393_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2395_);
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
    mut v_x_2400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2406_: u8 = 0;
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2410_: u8 = 0;
    let mut v_a_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2414_: u8 = 0;
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2419_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2400_) == 0 {
                    v___x_2401_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1___closed__0;
                    return v___x_2401_;
                } else {
                    v___x_2402_ = l_Lean_Json_getStr_x3f(v_x_2400_);
                    if lean_obj_tag(v___x_2402_) == 0 {
                        v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
                        v_isSharedCheck_2410_ = (!lean_is_exclusive(v___x_2402_)) as u8;
                        if v_isSharedCheck_2410_ == 0 {
                            v___x_2405_ = v___x_2402_;
                            v_isShared_2406_ = v_isSharedCheck_2410_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2403_);
                            lean_dec(v___x_2402_);
                            v___x_2405_ = lean_box(0);
                            v_isShared_2406_ = v_isSharedCheck_2410_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2411_ = lean_ctor_get(v___x_2402_, 0);
                        v_isSharedCheck_2419_ = (!lean_is_exclusive(v___x_2402_)) as u8;
                        if v_isSharedCheck_2419_ == 0 {
                            v___x_2413_ = v___x_2402_;
                            v_isShared_2414_ = v_isSharedCheck_2419_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2411_);
                            lean_dec(v___x_2402_);
                            v___x_2413_ = lean_box(0);
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
                    v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_a_2403_);
                    v___x_2408_ = v_reuseFailAlloc_2409_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2408_;
            }
            3 => {
                v___x_2415_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2415_, 0, v_a_2411_);
                if v_isShared_2414_ == 0 {
                    lean_ctor_set(v___x_2413_, 0, v___x_2415_);
                    v___x_2417_ = v___x_2413_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2415_);
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
    mut v_init_2423_: *mut LeanObject,
    mut v_x_2424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2433_: u8 = 0;
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: u8 = 0;
    let mut v_n_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: u8 = 0;
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2442_: u8 = 0;
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2446_: u8 = 0;
    let mut v_a_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2461_: u8 = 0;
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2465_: u8 = 0;
    let mut v_a_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2470_: u8 = 0;
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2424_) == 0 {
                    v_k_2425_ = lean_ctor_get(v_x_2424_, 1);
                    lean_inc(v_k_2425_);
                    v_v_2426_ = lean_ctor_get(v_x_2424_, 2);
                    lean_inc(v_v_2426_);
                    v_l_2427_ = lean_ctor_get(v_x_2424_, 3);
                    lean_inc(v_l_2427_);
                    v_r_2428_ = lean_ctor_get(v_x_2424_, 4);
                    lean_inc(v_r_2428_);
                    lean_dec_ref_known(v_x_2424_, 5);
                    v___x_2429_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0(v_init_2423_, v_l_2427_);
                    if lean_obj_tag(v___x_2429_) == 0 {
                        lean_dec(v_r_2428_);
                        lean_dec(v_v_2426_);
                        lean_dec(v_k_2425_);
                        return v___x_2429_;
                    } else {
                        v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
                        v_isSharedCheck_2470_ = (!lean_is_exclusive(v___x_2429_)) as u8;
                        if v_isSharedCheck_2470_ == 0 {
                            v___x_2432_ = v___x_2429_;
                            v_isShared_2433_ = v_isSharedCheck_2470_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2430_);
                            lean_dec(v___x_2429_);
                            v___x_2432_ = lean_box(0);
                            v_isShared_2433_ = v_isSharedCheck_2470_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_2471_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2471_, 0, v_init_2423_);
                    return v___x_2471_;
                }
            }
            1 => {
                v___x_2434_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__0;
                v___x_2435_ = lean_string_dec_eq(v_k_2425_, v___x_2434_);
                if v___x_2435_ == 0 {
                    lean_inc(v_k_2425_);
                    v_n_2436_ = l_String_toName(v_k_2425_);
                    v___x_2437_ = l_Lean_Name_isAnonymous(v_n_2436_);
                    if v___x_2437_ == 0 {
                        lean_del_object(v___x_2432_);
                        lean_dec(v_k_2425_);
                        v___x_2438_ = l_Lean_Json_getStr_x3f(v_v_2426_);
                        if lean_obj_tag(v___x_2438_) == 0 {
                            lean_dec(v_n_2436_);
                            lean_dec(v_a_2430_);
                            lean_dec(v_r_2428_);
                            v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
                            v_isSharedCheck_2446_ = (!lean_is_exclusive(v___x_2438_)) as u8;
                            if v_isSharedCheck_2446_ == 0 {
                                v___x_2441_ = v___x_2438_;
                                v_isShared_2442_ = v_isSharedCheck_2446_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_2439_);
                                lean_dec(v___x_2438_);
                                v___x_2441_ = lean_box(0);
                                v_isShared_2442_ = v_isSharedCheck_2446_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_a_2447_ = lean_ctor_get(v___x_2438_, 0);
                            lean_inc(v_a_2447_);
                            lean_dec_ref_known(v___x_2438_, 1);
                            v___x_2448_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_2436_, v_a_2447_, v_a_2430_);
                            v_init_2423_ = v___x_2448_;
                            v_x_2424_ = v_r_2428_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec(v_n_2436_);
                        lean_dec(v_a_2430_);
                        lean_dec(v_r_2428_);
                        lean_dec(v_v_2426_);
                        v___x_2450_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__1;
                        v___x_2451_ = lean_string_append(v___x_2450_, v_k_2425_);
                        lean_dec(v_k_2425_);
                        v___x_2452_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2;
                        v___x_2453_ = lean_string_append(v___x_2451_, v___x_2452_);
                        if v_isShared_2433_ == 0 {
                            lean_ctor_set_tag(v___x_2432_, 0);
                            lean_ctor_set(v___x_2432_, 0, v___x_2453_);
                            v___x_2455_ = v___x_2432_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2453_);
                            v___x_2455_ = v_reuseFailAlloc_2456_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2432_);
                    lean_dec(v_k_2425_);
                    v___x_2457_ = l_Lean_Json_getStr_x3f(v_v_2426_);
                    if lean_obj_tag(v___x_2457_) == 0 {
                        lean_dec(v_a_2430_);
                        lean_dec(v_r_2428_);
                        v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
                        v_isSharedCheck_2465_ = (!lean_is_exclusive(v___x_2457_)) as u8;
                        if v_isSharedCheck_2465_ == 0 {
                            v___x_2460_ = v___x_2457_;
                            v_isShared_2461_ = v_isSharedCheck_2465_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_2458_);
                            lean_dec(v___x_2457_);
                            v___x_2460_ = lean_box(0);
                            v_isShared_2461_ = v_isSharedCheck_2465_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_2466_ = lean_ctor_get(v___x_2457_, 0);
                        lean_inc(v_a_2466_);
                        lean_dec_ref_known(v___x_2457_, 1);
                        v___x_2467_ = lean_box(0);
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
                    v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2439_);
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
                    v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
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
    mut v_x_2473_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2473_) == 5 {
        let mut v_kvPairs_2474_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
        v_kvPairs_2474_ = lean_ctor_get(v_x_2473_, 0);
        lean_inc(v_kvPairs_2474_);
        lean_dec_ref_known(v_x_2473_, 1);
        v___x_2475_ = lean_box(1);
        v___x_2476_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0(v___x_2475_, v_kvPairs_2474_);
        return v___x_2476_;
    } else {
        let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
        v___x_2477_ = l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0___closed__0;
        v___x_2478_ = lean_unsigned_to_nat(80);
        v___x_2479_ = l_Lean_Json_pretty(v_x_2473_, v___x_2478_);
        v___x_2480_ = lean_string_append(v___x_2477_, v___x_2479_);
        lean_dec_ref(v___x_2479_);
        v___x_2481_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2;
        v___x_2482_ = lean_string_append(v___x_2480_, v___x_2481_);
        v___x_2483_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2483_, 0, v___x_2482_);
        return v___x_2483_;
    }
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson(
    mut v_json_2546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: u8 = 0;
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: u8 = 0;
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2562_: u8 = 0;
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2566_: u8 = 0;
    let mut v_a_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2574_: u8 = 0;
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2578_: u8 = 0;
    let mut v_a_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2586_: u8 = 0;
    let mut v___x_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2590_: u8 = 0;
    let mut v_a_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2598_: u8 = 0;
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2602_: u8 = 0;
    let mut v_a_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2610_: u8 = 0;
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2614_: u8 = 0;
    let mut v_a_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2622_: u8 = 0;
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2626_: u8 = 0;
    let mut v_a_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2634_: u8 = 0;
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2638_: u8 = 0;
    let mut v_a_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2646_: u8 = 0;
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2650_: u8 = 0;
    let mut v_a_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2654_: u8 = 0;
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: u8 = 0;
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2660_: u8 = 0;
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2667_: u8 = 0;
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2671_: u8 = 0;
    let mut v_a_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2679_: u8 = 0;
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2683_: u8 = 0;
    let mut v_a_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2691_: u8 = 0;
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2695_: u8 = 0;
    let mut v_a_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2703_: u8 = 0;
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2707_: u8 = 0;
    let mut v_a_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2715_: u8 = 0;
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2719_: u8 = 0;
    let mut v_a_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2723_: u8 = 0;
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: u8 = 0;
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2729_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_json_2546_);
                v___x_2547_ = l_Lean_Json_getTag_x3f(v_json_2546_);
                if lean_obj_tag(v___x_2547_) == 0 {
                    lean_dec(v_json_2546_);
                    v___x_2548_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__1;
                    return v___x_2548_;
                } else {
                    v_val_2549_ = lean_ctor_get(v___x_2547_, 0);
                    lean_inc(v_val_2549_);
                    lean_dec_ref_known(v___x_2547_, 1);
                    v___x_2550_ = lean_box(0);
                    v___x_2551_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2;
                    v___x_2552_ = lean_string_dec_eq(v_val_2549_, v___x_2551_);
                    if v___x_2552_ == 0 {
                        v___x_2553_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3;
                        v___x_2554_ = lean_string_dec_eq(v_val_2549_, v___x_2553_);
                        lean_dec(v_val_2549_);
                        if v___x_2554_ == 0 {
                            lean_dec(v_json_2546_);
                            v___x_2555_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__5;
                            return v___x_2555_;
                        } else {
                            v___x_2556_ = lean_unsigned_to_nat(7);
                            v___x_2557_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__21;
                            v___x_2558_ = l_Lean_Json_parseCtorFields(
                                v_json_2546_,
                                v___x_2553_,
                                v___x_2556_,
                                v___x_2557_,
                            );
                            if lean_obj_tag(v___x_2558_) == 0 {
                                v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
                                v_isSharedCheck_2566_ = (!lean_is_exclusive(v___x_2558_)) as u8;
                                if v_isSharedCheck_2566_ == 0 {
                                    v___x_2561_ = v___x_2558_;
                                    v_isShared_2562_ = v_isSharedCheck_2566_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_2559_);
                                    lean_dec(v___x_2558_);
                                    v___x_2561_ = lean_box(0);
                                    v_isShared_2562_ = v_isSharedCheck_2566_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_2567_ = lean_ctor_get(v___x_2558_, 0);
                                lean_inc(v_a_2567_);
                                lean_dec_ref_known(v___x_2558_, 1);
                                v___x_2568_ = lean_unsigned_to_nat(0);
                                v___x_2569_ =
                                    lean_array_get_borrowed(v___x_2550_, v_a_2567_, v___x_2568_);
                                lean_inc(v___x_2569_);
                                v___x_2570_ = l_Lean_Name_fromJson_x3f(v___x_2569_);
                                if lean_obj_tag(v___x_2570_) == 0 {
                                    lean_dec(v_a_2567_);
                                    v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
                                    v_isSharedCheck_2578_ = (!lean_is_exclusive(v___x_2570_)) as u8;
                                    if v_isSharedCheck_2578_ == 0 {
                                        v___x_2573_ = v___x_2570_;
                                        v_isShared_2574_ = v_isSharedCheck_2578_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2571_);
                                        lean_dec(v___x_2570_);
                                        v___x_2573_ = lean_box(0);
                                        v_isShared_2574_ = v_isSharedCheck_2578_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    v_a_2579_ = lean_ctor_get(v___x_2570_, 0);
                                    lean_inc(v_a_2579_);
                                    lean_dec_ref_known(v___x_2570_, 1);
                                    v___x_2580_ = lean_unsigned_to_nat(1);
                                    v___x_2581_ = lean_array_get_borrowed(
                                        v___x_2550_,
                                        v_a_2567_,
                                        v___x_2580_,
                                    );
                                    lean_inc(v___x_2581_);
                                    v___x_2582_ = l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0(v___x_2581_);
                                    if lean_obj_tag(v___x_2582_) == 0 {
                                        lean_dec(v_a_2579_);
                                        lean_dec(v_a_2567_);
                                        v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
                                        v_isSharedCheck_2590_ =
                                            (!lean_is_exclusive(v___x_2582_)) as u8;
                                        if v_isSharedCheck_2590_ == 0 {
                                            v___x_2585_ = v___x_2582_;
                                            v_isShared_2586_ = v_isSharedCheck_2590_;
                                            state = 5;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2583_);
                                            lean_dec(v___x_2582_);
                                            v___x_2585_ = lean_box(0);
                                            v_isShared_2586_ = v_isSharedCheck_2590_;
                                            state = 5;
                                            continue;
                                        }
                                    } else {
                                        v_a_2591_ = lean_ctor_get(v___x_2582_, 0);
                                        lean_inc(v_a_2591_);
                                        lean_dec_ref_known(v___x_2582_, 1);
                                        v___x_2592_ = lean_unsigned_to_nat(2);
                                        v___x_2593_ = lean_array_get_borrowed(
                                            v___x_2550_,
                                            v_a_2567_,
                                            v___x_2592_,
                                        );
                                        v___x_2594_ = l_Lean_Json_getBool_x3f(v___x_2593_);
                                        if lean_obj_tag(v___x_2594_) == 0 {
                                            lean_dec(v_a_2591_);
                                            lean_dec(v_a_2579_);
                                            lean_dec(v_a_2567_);
                                            v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
                                            v_isSharedCheck_2602_ =
                                                (!lean_is_exclusive(v___x_2594_)) as u8;
                                            if v_isSharedCheck_2602_ == 0 {
                                                v___x_2597_ = v___x_2594_;
                                                v_isShared_2598_ = v_isSharedCheck_2602_;
                                                state = 7;
                                                continue;
                                            } else {
                                                lean_inc(v_a_2595_);
                                                lean_dec(v___x_2594_);
                                                v___x_2597_ = lean_box(0);
                                                v_isShared_2598_ = v_isSharedCheck_2602_;
                                                state = 7;
                                                continue;
                                            }
                                        } else {
                                            v_a_2603_ = lean_ctor_get(v___x_2594_, 0);
                                            lean_inc(v_a_2603_);
                                            lean_dec_ref_known(v___x_2594_, 1);
                                            v___x_2604_ = lean_unsigned_to_nat(3);
                                            v___x_2605_ = lean_array_get_borrowed(
                                                v___x_2550_,
                                                v_a_2567_,
                                                v___x_2604_,
                                            );
                                            lean_inc(v___x_2605_);
                                            v___x_2606_ = l_Lean_Json_getStr_x3f(v___x_2605_);
                                            if lean_obj_tag(v___x_2606_) == 0 {
                                                lean_dec(v_a_2603_);
                                                lean_dec(v_a_2591_);
                                                lean_dec(v_a_2579_);
                                                lean_dec(v_a_2567_);
                                                v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
                                                v_isSharedCheck_2614_ =
                                                    (!lean_is_exclusive(v___x_2606_)) as u8;
                                                if v_isSharedCheck_2614_ == 0 {
                                                    v___x_2609_ = v___x_2606_;
                                                    v_isShared_2610_ = v_isSharedCheck_2614_;
                                                    state = 9;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_2607_);
                                                    lean_dec(v___x_2606_);
                                                    v___x_2609_ = lean_box(0);
                                                    v_isShared_2610_ = v_isSharedCheck_2614_;
                                                    state = 9;
                                                    continue;
                                                }
                                            } else {
                                                v_a_2615_ = lean_ctor_get(v___x_2606_, 0);
                                                lean_inc(v_a_2615_);
                                                lean_dec_ref_known(v___x_2606_, 1);
                                                v___x_2616_ = lean_unsigned_to_nat(4);
                                                v___x_2617_ = lean_array_get_borrowed(
                                                    v___x_2550_,
                                                    v_a_2567_,
                                                    v___x_2616_,
                                                );
                                                lean_inc(v___x_2617_);
                                                v___x_2618_ = l_Lean_Json_getStr_x3f(v___x_2617_);
                                                if lean_obj_tag(v___x_2618_) == 0 {
                                                    lean_dec(v_a_2615_);
                                                    lean_dec(v_a_2603_);
                                                    lean_dec(v_a_2591_);
                                                    lean_dec(v_a_2579_);
                                                    lean_dec(v_a_2567_);
                                                    v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
                                                    v_isSharedCheck_2626_ =
                                                        (!lean_is_exclusive(v___x_2618_)) as u8;
                                                    if v_isSharedCheck_2626_ == 0 {
                                                        v___x_2621_ = v___x_2618_;
                                                        v_isShared_2622_ = v_isSharedCheck_2626_;
                                                        state = 11;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_2619_);
                                                        lean_dec(v___x_2618_);
                                                        v___x_2621_ = lean_box(0);
                                                        v_isShared_2622_ = v_isSharedCheck_2626_;
                                                        state = 11;
                                                        continue;
                                                    }
                                                } else {
                                                    v_a_2627_ = lean_ctor_get(v___x_2618_, 0);
                                                    lean_inc(v_a_2627_);
                                                    lean_dec_ref_known(v___x_2618_, 1);
                                                    v___x_2628_ = lean_unsigned_to_nat(5);
                                                    v___x_2629_ = lean_array_get_borrowed(
                                                        v___x_2550_,
                                                        v_a_2567_,
                                                        v___x_2628_,
                                                    );
                                                    lean_inc(v___x_2629_);
                                                    v___x_2630_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(v___x_2629_);
                                                    if lean_obj_tag(v___x_2630_) == 0 {
                                                        lean_dec(v_a_2627_);
                                                        lean_dec(v_a_2615_);
                                                        lean_dec(v_a_2603_);
                                                        lean_dec(v_a_2591_);
                                                        lean_dec(v_a_2579_);
                                                        lean_dec(v_a_2567_);
                                                        v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
                                                        v_isSharedCheck_2638_ =
                                                            (!lean_is_exclusive(v___x_2630_)) as u8;
                                                        if v_isSharedCheck_2638_ == 0 {
                                                            v___x_2633_ = v___x_2630_;
                                                            v_isShared_2634_ =
                                                                v_isSharedCheck_2638_;
                                                            state = 13;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_2631_);
                                                            lean_dec(v___x_2630_);
                                                            v___x_2633_ = lean_box(0);
                                                            v_isShared_2634_ =
                                                                v_isSharedCheck_2638_;
                                                            state = 13;
                                                            continue;
                                                        }
                                                    } else {
                                                        v_a_2639_ = lean_ctor_get(v___x_2630_, 0);
                                                        lean_inc(v_a_2639_);
                                                        lean_dec_ref_known(v___x_2630_, 1);
                                                        v___x_2640_ = lean_unsigned_to_nat(6);
                                                        v___x_2641_ = lean_array_get(
                                                            v___x_2550_,
                                                            v_a_2567_,
                                                            v___x_2640_,
                                                        );
                                                        lean_dec(v_a_2567_);
                                                        v___x_2642_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v___x_2641_);
                                                        if lean_obj_tag(v___x_2642_) == 0 {
                                                            lean_dec(v_a_2639_);
                                                            lean_dec(v_a_2627_);
                                                            lean_dec(v_a_2615_);
                                                            lean_dec(v_a_2603_);
                                                            lean_dec(v_a_2591_);
                                                            lean_dec(v_a_2579_);
                                                            v_a_2643_ =
                                                                lean_ctor_get(v___x_2642_, 0);
                                                            v_isSharedCheck_2650_ =
                                                                (!lean_is_exclusive(v___x_2642_))
                                                                    as u8;
                                                            if v_isSharedCheck_2650_ == 0 {
                                                                v___x_2645_ = v___x_2642_;
                                                                v_isShared_2646_ =
                                                                    v_isSharedCheck_2650_;
                                                                state = 15;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_2643_);
                                                                lean_dec(v___x_2642_);
                                                                v___x_2645_ = lean_box(0);
                                                                v_isShared_2646_ =
                                                                    v_isSharedCheck_2650_;
                                                                state = 15;
                                                                continue;
                                                            }
                                                        } else {
                                                            v_a_2651_ =
                                                                lean_ctor_get(v___x_2642_, 0);
                                                            v_isSharedCheck_2660_ =
                                                                (!lean_is_exclusive(v___x_2642_))
                                                                    as u8;
                                                            if v_isSharedCheck_2660_ == 0 {
                                                                v___x_2653_ = v___x_2642_;
                                                                v_isShared_2654_ =
                                                                    v_isSharedCheck_2660_;
                                                                state = 17;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_2651_);
                                                                lean_dec(v___x_2642_);
                                                                v___x_2653_ = lean_box(0);
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
                        lean_dec(v_val_2549_);
                        v___x_2661_ = lean_unsigned_to_nat(4);
                        v___x_2662_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__25;
                        v___x_2663_ = l_Lean_Json_parseCtorFields(
                            v_json_2546_,
                            v___x_2551_,
                            v___x_2661_,
                            v___x_2662_,
                        );
                        if lean_obj_tag(v___x_2663_) == 0 {
                            v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
                            v_isSharedCheck_2671_ = (!lean_is_exclusive(v___x_2663_)) as u8;
                            if v_isSharedCheck_2671_ == 0 {
                                v___x_2666_ = v___x_2663_;
                                v_isShared_2667_ = v_isSharedCheck_2671_;
                                state = 19;
                                continue;
                            } else {
                                lean_inc(v_a_2664_);
                                lean_dec(v___x_2663_);
                                v___x_2666_ = lean_box(0);
                                v_isShared_2667_ = v_isSharedCheck_2671_;
                                state = 19;
                                continue;
                            }
                        } else {
                            v_a_2672_ = lean_ctor_get(v___x_2663_, 0);
                            lean_inc(v_a_2672_);
                            lean_dec_ref_known(v___x_2663_, 1);
                            v___x_2673_ = lean_unsigned_to_nat(0);
                            v___x_2674_ =
                                lean_array_get_borrowed(v___x_2550_, v_a_2672_, v___x_2673_);
                            lean_inc(v___x_2674_);
                            v___x_2675_ = l_Lean_Name_fromJson_x3f(v___x_2674_);
                            if lean_obj_tag(v___x_2675_) == 0 {
                                lean_dec(v_a_2672_);
                                v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
                                v_isSharedCheck_2683_ = (!lean_is_exclusive(v___x_2675_)) as u8;
                                if v_isSharedCheck_2683_ == 0 {
                                    v___x_2678_ = v___x_2675_;
                                    v_isShared_2679_ = v_isSharedCheck_2683_;
                                    state = 21;
                                    continue;
                                } else {
                                    lean_inc(v_a_2676_);
                                    lean_dec(v___x_2675_);
                                    v___x_2678_ = lean_box(0);
                                    v_isShared_2679_ = v_isSharedCheck_2683_;
                                    state = 21;
                                    continue;
                                }
                            } else {
                                v_a_2684_ = lean_ctor_get(v___x_2675_, 0);
                                lean_inc(v_a_2684_);
                                lean_dec_ref_known(v___x_2675_, 1);
                                v___x_2685_ = lean_unsigned_to_nat(1);
                                v___x_2686_ =
                                    lean_array_get_borrowed(v___x_2550_, v_a_2672_, v___x_2685_);
                                lean_inc(v___x_2686_);
                                v___x_2687_ = l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0(v___x_2686_);
                                if lean_obj_tag(v___x_2687_) == 0 {
                                    lean_dec(v_a_2684_);
                                    lean_dec(v_a_2672_);
                                    v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
                                    v_isSharedCheck_2695_ = (!lean_is_exclusive(v___x_2687_)) as u8;
                                    if v_isSharedCheck_2695_ == 0 {
                                        v___x_2690_ = v___x_2687_;
                                        v_isShared_2691_ = v_isSharedCheck_2695_;
                                        state = 23;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2688_);
                                        lean_dec(v___x_2687_);
                                        v___x_2690_ = lean_box(0);
                                        v_isShared_2691_ = v_isSharedCheck_2695_;
                                        state = 23;
                                        continue;
                                    }
                                } else {
                                    v_a_2696_ = lean_ctor_get(v___x_2687_, 0);
                                    lean_inc(v_a_2696_);
                                    lean_dec_ref_known(v___x_2687_, 1);
                                    v___x_2697_ = lean_unsigned_to_nat(2);
                                    v___x_2698_ = lean_array_get_borrowed(
                                        v___x_2550_,
                                        v_a_2672_,
                                        v___x_2697_,
                                    );
                                    v___x_2699_ = l_Lean_Json_getBool_x3f(v___x_2698_);
                                    if lean_obj_tag(v___x_2699_) == 0 {
                                        lean_dec(v_a_2696_);
                                        lean_dec(v_a_2684_);
                                        lean_dec(v_a_2672_);
                                        v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
                                        v_isSharedCheck_2707_ =
                                            (!lean_is_exclusive(v___x_2699_)) as u8;
                                        if v_isSharedCheck_2707_ == 0 {
                                            v___x_2702_ = v___x_2699_;
                                            v_isShared_2703_ = v_isSharedCheck_2707_;
                                            state = 25;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2700_);
                                            lean_dec(v___x_2699_);
                                            v___x_2702_ = lean_box(0);
                                            v_isShared_2703_ = v_isSharedCheck_2707_;
                                            state = 25;
                                            continue;
                                        }
                                    } else {
                                        v_a_2708_ = lean_ctor_get(v___x_2699_, 0);
                                        lean_inc(v_a_2708_);
                                        lean_dec_ref_known(v___x_2699_, 1);
                                        v___x_2709_ = lean_unsigned_to_nat(3);
                                        v___x_2710_ =
                                            lean_array_get(v___x_2550_, v_a_2672_, v___x_2709_);
                                        lean_dec(v_a_2672_);
                                        v___x_2711_ = l_Lean_Json_getStr_x3f(v___x_2710_);
                                        if lean_obj_tag(v___x_2711_) == 0 {
                                            lean_dec(v_a_2708_);
                                            lean_dec(v_a_2696_);
                                            lean_dec(v_a_2684_);
                                            v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
                                            v_isSharedCheck_2719_ =
                                                (!lean_is_exclusive(v___x_2711_)) as u8;
                                            if v_isSharedCheck_2719_ == 0 {
                                                v___x_2714_ = v___x_2711_;
                                                v_isShared_2715_ = v_isSharedCheck_2719_;
                                                state = 27;
                                                continue;
                                            } else {
                                                lean_inc(v_a_2712_);
                                                lean_dec(v___x_2711_);
                                                v___x_2714_ = lean_box(0);
                                                v_isShared_2715_ = v_isSharedCheck_2719_;
                                                state = 27;
                                                continue;
                                            }
                                        } else {
                                            v_a_2720_ = lean_ctor_get(v___x_2711_, 0);
                                            v_isSharedCheck_2729_ =
                                                (!lean_is_exclusive(v___x_2711_)) as u8;
                                            if v_isSharedCheck_2729_ == 0 {
                                                v___x_2722_ = v___x_2711_;
                                                v_isShared_2723_ = v_isSharedCheck_2729_;
                                                state = 29;
                                                continue;
                                            } else {
                                                lean_inc(v_a_2720_);
                                                lean_dec(v___x_2711_);
                                                v___x_2722_ = lean_box(0);
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
                    v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
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
                    v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
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
                    v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
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
                    v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
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
                    v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
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
                    v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
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
                    v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
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
                    v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
                    v___x_2648_ = v_reuseFailAlloc_2649_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2648_;
            }
            17 => {
                v___x_2655_ = lean_alloc_ctor(1, 6, (1) as u32);
                lean_ctor_set(v___x_2655_, 0, v_a_2579_);
                lean_ctor_set(v___x_2655_, 1, v_a_2591_);
                lean_ctor_set(v___x_2655_, 2, v_a_2615_);
                lean_ctor_set(v___x_2655_, 3, v_a_2627_);
                lean_ctor_set(v___x_2655_, 4, v_a_2639_);
                lean_ctor_set(v___x_2655_, 5, v_a_2651_);
                v___x_2656_ = (lean_unbox(v_a_2603_) as u8);
                lean_dec(v_a_2603_);
                lean_ctor_set_uint8(
                    v___x_2655_,
                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                    v___x_2656_,
                );
                if v_isShared_2654_ == 0 {
                    lean_ctor_set(v___x_2653_, 0, v___x_2655_);
                    v___x_2658_ = v___x_2653_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2655_);
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
                    v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
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
                    v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
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
                    v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
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
                    v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
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
                    v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2712_);
                    v___x_2717_ = v_reuseFailAlloc_2718_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2717_;
            }
            29 => {
                v___x_2724_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_2724_, 0, v_a_2684_);
                lean_ctor_set(v___x_2724_, 1, v_a_2696_);
                lean_ctor_set(v___x_2724_, 2, v_a_2720_);
                v___x_2725_ = (lean_unbox(v_a_2708_) as u8);
                lean_dec(v_a_2708_);
                lean_ctor_set_uint8(
                    v___x_2724_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2725_,
                );
                if v_isShared_2723_ == 0 {
                    lean_ctor_set(v___x_2722_, 0, v___x_2724_);
                    v___x_2727_ = v___x_2722_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2724_);
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
    mut v_x_2732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2737_: u8 = 0;
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2741_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2732_) == 0 {
                    v___x_2733_ = lean_box(0);
                    return v___x_2733_;
                } else {
                    v_val_2734_ = lean_ctor_get(v_x_2732_, 0);
                    v_isSharedCheck_2741_ = (!lean_is_exclusive(v_x_2732_)) as u8;
                    if v_isSharedCheck_2741_ == 0 {
                        v___x_2736_ = v_x_2732_;
                        v_isShared_2737_ = v_isSharedCheck_2741_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2734_);
                        lean_dec(v_x_2732_);
                        v___x_2736_ = lean_box(0);
                        v_isShared_2737_ = v_isSharedCheck_2741_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2737_ == 0 {
                    lean_ctor_set_tag(v___x_2736_, 3);
                    v___x_2739_ = v___x_2736_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2740_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_val_2734_);
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
    mut v_x_2742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2747_: u8 = 0;
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2752_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2742_) == 0 {
                    v___x_2743_ = lean_box(0);
                    return v___x_2743_;
                } else {
                    v_val_2744_ = lean_ctor_get(v_x_2742_, 0);
                    v_isSharedCheck_2752_ = (!lean_is_exclusive(v_x_2742_)) as u8;
                    if v_isSharedCheck_2752_ == 0 {
                        v___x_2746_ = v_x_2742_;
                        v_isShared_2747_ = v_isSharedCheck_2752_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2744_);
                        lean_dec(v_x_2742_);
                        v___x_2746_ = lean_box(0);
                        v_isShared_2747_ = v_isSharedCheck_2752_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2748_ = l_Lake_mkRelPathString(v_val_2744_);
                if v_isShared_2747_ == 0 {
                    lean_ctor_set_tag(v___x_2746_, 3);
                    lean_ctor_set(v___x_2746_, 0, v___x_2748_);
                    v___x_2750_ = v___x_2746_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2751_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2748_);
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
    mut v_msg_2753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    v___x_2754_ = lean_box(1);
    v___x_2755_ = lean_panic_fn_borrowed(v___x_2754_, v_msg_2753_);
    return v___x_2755_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    v___x_2759_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__2;
    v___x_2760_ = lean_unsigned_to_nat(35);
    v___x_2761_ = lean_unsigned_to_nat(182);
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
-> *mut LeanObject {
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    v___x_2765_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__2;
    v___x_2766_ = lean_unsigned_to_nat(21);
    v___x_2767_ = lean_unsigned_to_nat(183);
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
-> *mut LeanObject {
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    v___x_2773_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__6;
    v___x_2774_ = lean_unsigned_to_nat(35);
    v___x_2775_ = lean_unsigned_to_nat(276);
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
-> *mut LeanObject {
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    v___x_2779_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__6;
    v___x_2780_ = lean_unsigned_to_nat(21);
    v___x_2781_ = lean_unsigned_to_nat(277);
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
    mut v_k_2785_: *mut LeanObject,
    mut v_v_2786_: *mut LeanObject,
    mut v_t_2787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2795_: u8 = 0;
    let mut v___x_2796_: u8 = 0;
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: u8 = 0;
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2815_: u8 = 0;
    let mut v_size_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: u8 = 0;
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2827_: u8 = 0;
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2854_: u8 = 0;
    let mut v_unused_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2869_: u8 = 0;
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2873_: u8 = 0;
    let mut v_unused_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2884_: u8 = 0;
    let mut v_unused_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2903_: u8 = 0;
    let mut v_size_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2914_: u8 = 0;
    let mut v_unused_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2921_: u8 = 0;
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2930_: u8 = 0;
    let mut v_unused_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2939_: u8 = 0;
    let mut v_k_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2944_: u8 = 0;
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2956_: u8 = 0;
    let mut v_unused_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2960_: u8 = 0;
    let mut v_unused_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: u8 = 0;
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2993_: u8 = 0;
    let mut v_size_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: u8 = 0;
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3005_: u8 = 0;
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3031_: u8 = 0;
    let mut v_unused_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3045_: u8 = 0;
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3049_: u8 = 0;
    let mut v_unused_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3060_: u8 = 0;
    let mut v_unused_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3079_: u8 = 0;
    let mut v_size_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3090_: u8 = 0;
    let mut v_unused_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3097_: u8 = 0;
    let mut v_k_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3102_: u8 = 0;
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3114_: u8 = 0;
    let mut v_unused_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3118_: u8 = 0;
    let mut v_unused_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3127_: u8 = 0;
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3136_: u8 = 0;
    let mut v_unused_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3148_: u8 = 0;
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_2787_) == 0 {
                    v_size_2788_ = lean_ctor_get(v_t_2787_, 0);
                    v_k_2789_ = lean_ctor_get(v_t_2787_, 1);
                    v_v_2790_ = lean_ctor_get(v_t_2787_, 2);
                    v_l_2791_ = lean_ctor_get(v_t_2787_, 3);
                    v_r_2792_ = lean_ctor_get(v_t_2787_, 4);
                    v_isSharedCheck_3148_ = (!lean_is_exclusive(v_t_2787_)) as u8;
                    if v_isSharedCheck_3148_ == 0 {
                        v___x_2794_ = v_t_2787_;
                        v_isShared_2795_ = v_isSharedCheck_3148_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_2792_);
                        lean_inc(v_l_2791_);
                        lean_inc(v_v_2790_);
                        lean_inc(v_k_2789_);
                        lean_inc(v_size_2788_);
                        lean_dec(v_t_2787_);
                        v___x_2794_ = lean_box(0);
                        v_isShared_2795_ = v_isSharedCheck_3148_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3149_ = lean_unsigned_to_nat(1);
                    v___x_3150_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_3150_, 0, v___x_3149_);
                    lean_ctor_set(v___x_3150_, 1, v_k_2785_);
                    lean_ctor_set(v___x_3150_, 2, v_v_2786_);
                    lean_ctor_set(v___x_3150_, 3, v_t_2787_);
                    lean_ctor_set(v___x_3150_, 4, v_t_2787_);
                    return v___x_3150_;
                }
            }
            1 => {
                v___x_2796_ = lean_string_compare(v_k_2785_, v_k_2789_);
                match v___x_2796_ {
                    0 => {
                        lean_dec(v_size_2788_);
                        v___x_2797_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(v_k_2785_, v_v_2786_, v_l_2791_);
                        if lean_obj_tag(v_r_2792_) == 0 {
                            if lean_obj_tag(v___x_2797_) == 0 {
                                v_size_2798_ = lean_ctor_get(v_r_2792_, 0);
                                v_size_2799_ = lean_ctor_get(v___x_2797_, 0);
                                lean_inc(v_size_2799_);
                                v_k_2800_ = lean_ctor_get(v___x_2797_, 1);
                                lean_inc(v_k_2800_);
                                v_v_2801_ = lean_ctor_get(v___x_2797_, 2);
                                lean_inc(v_v_2801_);
                                v_l_2802_ = lean_ctor_get(v___x_2797_, 3);
                                lean_inc(v_l_2802_);
                                v_r_2803_ = lean_ctor_get(v___x_2797_, 4);
                                lean_inc(v_r_2803_);
                                v___x_2804_ = lean_unsigned_to_nat(3);
                                v___x_2805_ = lean_nat_mul(v___x_2804_, v_size_2798_);
                                v___x_2806_ = lean_nat_dec_lt(v___x_2805_, v_size_2799_);
                                lean_dec(v___x_2805_);
                                if v___x_2806_ == 0 {
                                    lean_dec(v_r_2803_);
                                    lean_dec(v_l_2802_);
                                    lean_dec(v_v_2801_);
                                    lean_dec(v_k_2800_);
                                    v___x_2807_ = lean_unsigned_to_nat(1);
                                    v___x_2808_ = lean_nat_add(v___x_2807_, v_size_2799_);
                                    lean_dec(v_size_2799_);
                                    v___x_2809_ = lean_nat_add(v___x_2808_, v_size_2798_);
                                    lean_dec(v___x_2808_);
                                    if v_isShared_2795_ == 0 {
                                        lean_ctor_set(v___x_2794_, 3, v___x_2797_);
                                        lean_ctor_set(v___x_2794_, 0, v___x_2809_);
                                        v___x_2811_ = v___x_2794_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2809_);
                                        lean_ctor_set(v_reuseFailAlloc_2812_, 1, v_k_2789_);
                                        lean_ctor_set(v_reuseFailAlloc_2812_, 2, v_v_2790_);
                                        lean_ctor_set(v_reuseFailAlloc_2812_, 3, v___x_2797_);
                                        lean_ctor_set(v_reuseFailAlloc_2812_, 4, v_r_2792_);
                                        v___x_2811_ = v_reuseFailAlloc_2812_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v_isSharedCheck_2884_ = (!lean_is_exclusive(v___x_2797_)) as u8;
                                    if v_isSharedCheck_2884_ == 0 {
                                        v_unused_2885_ = lean_ctor_get(v___x_2797_, 4);
                                        lean_dec(v_unused_2885_);
                                        v_unused_2886_ = lean_ctor_get(v___x_2797_, 3);
                                        lean_dec(v_unused_2886_);
                                        v_unused_2887_ = lean_ctor_get(v___x_2797_, 2);
                                        lean_dec(v_unused_2887_);
                                        v_unused_2888_ = lean_ctor_get(v___x_2797_, 1);
                                        lean_dec(v_unused_2888_);
                                        v_unused_2889_ = lean_ctor_get(v___x_2797_, 0);
                                        lean_dec(v_unused_2889_);
                                        v___x_2814_ = v___x_2797_;
                                        v_isShared_2815_ = v_isSharedCheck_2884_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_dec(v___x_2797_);
                                        v___x_2814_ = lean_box(0);
                                        v_isShared_2815_ = v_isSharedCheck_2884_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_2890_ = lean_ctor_get(v_r_2792_, 0);
                                v___x_2891_ = lean_unsigned_to_nat(1);
                                v___x_2892_ = lean_nat_add(v___x_2891_, v_size_2890_);
                                if v_isShared_2795_ == 0 {
                                    lean_ctor_set(v___x_2794_, 3, v___x_2797_);
                                    lean_ctor_set(v___x_2794_, 0, v___x_2892_);
                                    v___x_2894_ = v___x_2794_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2892_);
                                    lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_k_2789_);
                                    lean_ctor_set(v_reuseFailAlloc_2895_, 2, v_v_2790_);
                                    lean_ctor_set(v_reuseFailAlloc_2895_, 3, v___x_2797_);
                                    lean_ctor_set(v_reuseFailAlloc_2895_, 4, v_r_2792_);
                                    v___x_2894_ = v_reuseFailAlloc_2895_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if lean_obj_tag(v___x_2797_) == 0 {
                                v_l_2896_ = lean_ctor_get(v___x_2797_, 3);
                                lean_inc(v_l_2896_);
                                if lean_obj_tag(v_l_2896_) == 0 {
                                    v_r_2897_ = lean_ctor_get(v___x_2797_, 4);
                                    lean_inc(v_r_2897_);
                                    if lean_obj_tag(v_r_2897_) == 0 {
                                        v_size_2898_ = lean_ctor_get(v___x_2797_, 0);
                                        v_k_2899_ = lean_ctor_get(v___x_2797_, 1);
                                        v_v_2900_ = lean_ctor_get(v___x_2797_, 2);
                                        v_isSharedCheck_2914_ =
                                            (!lean_is_exclusive(v___x_2797_)) as u8;
                                        if v_isSharedCheck_2914_ == 0 {
                                            v_unused_2915_ = lean_ctor_get(v___x_2797_, 4);
                                            lean_dec(v_unused_2915_);
                                            v_unused_2916_ = lean_ctor_get(v___x_2797_, 3);
                                            lean_dec(v_unused_2916_);
                                            v___x_2902_ = v___x_2797_;
                                            v_isShared_2903_ = v_isSharedCheck_2914_;
                                            state = 14;
                                            continue;
                                        } else {
                                            lean_inc(v_v_2900_);
                                            lean_inc(v_k_2899_);
                                            lean_inc(v_size_2898_);
                                            lean_dec(v___x_2797_);
                                            v___x_2902_ = lean_box(0);
                                            v_isShared_2903_ = v_isSharedCheck_2914_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_2917_ = lean_ctor_get(v___x_2797_, 1);
                                        v_v_2918_ = lean_ctor_get(v___x_2797_, 2);
                                        v_isSharedCheck_2930_ =
                                            (!lean_is_exclusive(v___x_2797_)) as u8;
                                        if v_isSharedCheck_2930_ == 0 {
                                            v_unused_2931_ = lean_ctor_get(v___x_2797_, 4);
                                            lean_dec(v_unused_2931_);
                                            v_unused_2932_ = lean_ctor_get(v___x_2797_, 3);
                                            lean_dec(v_unused_2932_);
                                            v_unused_2933_ = lean_ctor_get(v___x_2797_, 0);
                                            lean_dec(v_unused_2933_);
                                            v___x_2920_ = v___x_2797_;
                                            v_isShared_2921_ = v_isSharedCheck_2930_;
                                            state = 17;
                                            continue;
                                        } else {
                                            lean_inc(v_v_2918_);
                                            lean_inc(v_k_2917_);
                                            lean_dec(v___x_2797_);
                                            v___x_2920_ = lean_box(0);
                                            v_isShared_2921_ = v_isSharedCheck_2930_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_2934_ = lean_ctor_get(v___x_2797_, 4);
                                    lean_inc(v_r_2934_);
                                    if lean_obj_tag(v_r_2934_) == 0 {
                                        v_k_2935_ = lean_ctor_get(v___x_2797_, 1);
                                        v_v_2936_ = lean_ctor_get(v___x_2797_, 2);
                                        v_isSharedCheck_2960_ =
                                            (!lean_is_exclusive(v___x_2797_)) as u8;
                                        if v_isSharedCheck_2960_ == 0 {
                                            v_unused_2961_ = lean_ctor_get(v___x_2797_, 4);
                                            lean_dec(v_unused_2961_);
                                            v_unused_2962_ = lean_ctor_get(v___x_2797_, 3);
                                            lean_dec(v_unused_2962_);
                                            v_unused_2963_ = lean_ctor_get(v___x_2797_, 0);
                                            lean_dec(v_unused_2963_);
                                            v___x_2938_ = v___x_2797_;
                                            v_isShared_2939_ = v_isSharedCheck_2960_;
                                            state = 20;
                                            continue;
                                        } else {
                                            lean_inc(v_v_2936_);
                                            lean_inc(v_k_2935_);
                                            lean_dec(v___x_2797_);
                                            v___x_2938_ = lean_box(0);
                                            v_isShared_2939_ = v_isSharedCheck_2960_;
                                            state = 20;
                                            continue;
                                        }
                                    } else {
                                        v___x_2964_ = lean_unsigned_to_nat(2);
                                        if v_isShared_2795_ == 0 {
                                            lean_ctor_set(v___x_2794_, 4, v_r_2934_);
                                            lean_ctor_set(v___x_2794_, 3, v___x_2797_);
                                            lean_ctor_set(v___x_2794_, 0, v___x_2964_);
                                            v___x_2966_ = v___x_2794_;
                                            state = 25;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_2967_ =
                                                lean_alloc_ctor(0, 5, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2964_);
                                            lean_ctor_set(v_reuseFailAlloc_2967_, 1, v_k_2789_);
                                            lean_ctor_set(v_reuseFailAlloc_2967_, 2, v_v_2790_);
                                            lean_ctor_set(v_reuseFailAlloc_2967_, 3, v___x_2797_);
                                            lean_ctor_set(v_reuseFailAlloc_2967_, 4, v_r_2934_);
                                            v___x_2966_ = v_reuseFailAlloc_2967_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_2968_ = lean_unsigned_to_nat(1);
                                if v_isShared_2795_ == 0 {
                                    lean_ctor_set(v___x_2794_, 4, v___x_2797_);
                                    lean_ctor_set(v___x_2794_, 3, v___x_2797_);
                                    lean_ctor_set(v___x_2794_, 0, v___x_2968_);
                                    v___x_2970_ = v___x_2794_;
                                    state = 26;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2968_);
                                    lean_ctor_set(v_reuseFailAlloc_2971_, 1, v_k_2789_);
                                    lean_ctor_set(v_reuseFailAlloc_2971_, 2, v_v_2790_);
                                    lean_ctor_set(v_reuseFailAlloc_2971_, 3, v___x_2797_);
                                    lean_ctor_set(v_reuseFailAlloc_2971_, 4, v___x_2797_);
                                    v___x_2970_ = v_reuseFailAlloc_2971_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    }
                    1 => {
                        lean_dec(v_v_2790_);
                        lean_dec(v_k_2789_);
                        if v_isShared_2795_ == 0 {
                            lean_ctor_set(v___x_2794_, 2, v_v_2786_);
                            lean_ctor_set(v___x_2794_, 1, v_k_2785_);
                            v___x_2973_ = v___x_2794_;
                            state = 27;
                            continue;
                        } else {
                            v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_size_2788_);
                            lean_ctor_set(v_reuseFailAlloc_2974_, 1, v_k_2785_);
                            lean_ctor_set(v_reuseFailAlloc_2974_, 2, v_v_2786_);
                            lean_ctor_set(v_reuseFailAlloc_2974_, 3, v_l_2791_);
                            lean_ctor_set(v_reuseFailAlloc_2974_, 4, v_r_2792_);
                            v___x_2973_ = v_reuseFailAlloc_2974_;
                            state = 27;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec(v_size_2788_);
                        v___x_2975_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(v_k_2785_, v_v_2786_, v_r_2792_);
                        if lean_obj_tag(v_l_2791_) == 0 {
                            if lean_obj_tag(v___x_2975_) == 0 {
                                v_size_2976_ = lean_ctor_get(v_l_2791_, 0);
                                v_size_2977_ = lean_ctor_get(v___x_2975_, 0);
                                lean_inc(v_size_2977_);
                                v_k_2978_ = lean_ctor_get(v___x_2975_, 1);
                                lean_inc(v_k_2978_);
                                v_v_2979_ = lean_ctor_get(v___x_2975_, 2);
                                lean_inc(v_v_2979_);
                                v_l_2980_ = lean_ctor_get(v___x_2975_, 3);
                                lean_inc(v_l_2980_);
                                v_r_2981_ = lean_ctor_get(v___x_2975_, 4);
                                lean_inc(v_r_2981_);
                                v___x_2982_ = lean_unsigned_to_nat(3);
                                v___x_2983_ = lean_nat_mul(v___x_2982_, v_size_2976_);
                                v___x_2984_ = lean_nat_dec_lt(v___x_2983_, v_size_2977_);
                                lean_dec(v___x_2983_);
                                if v___x_2984_ == 0 {
                                    lean_dec(v_r_2981_);
                                    lean_dec(v_l_2980_);
                                    lean_dec(v_v_2979_);
                                    lean_dec(v_k_2978_);
                                    v___x_2985_ = lean_unsigned_to_nat(1);
                                    v___x_2986_ = lean_nat_add(v___x_2985_, v_size_2976_);
                                    v___x_2987_ = lean_nat_add(v___x_2986_, v_size_2977_);
                                    lean_dec(v_size_2977_);
                                    lean_dec(v___x_2986_);
                                    if v_isShared_2795_ == 0 {
                                        lean_ctor_set(v___x_2794_, 4, v___x_2975_);
                                        lean_ctor_set(v___x_2794_, 0, v___x_2987_);
                                        v___x_2989_ = v___x_2794_;
                                        state = 28;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2987_);
                                        lean_ctor_set(v_reuseFailAlloc_2990_, 1, v_k_2789_);
                                        lean_ctor_set(v_reuseFailAlloc_2990_, 2, v_v_2790_);
                                        lean_ctor_set(v_reuseFailAlloc_2990_, 3, v_l_2791_);
                                        lean_ctor_set(v_reuseFailAlloc_2990_, 4, v___x_2975_);
                                        v___x_2989_ = v_reuseFailAlloc_2990_;
                                        state = 28;
                                        continue;
                                    }
                                } else {
                                    v_isSharedCheck_3060_ = (!lean_is_exclusive(v___x_2975_)) as u8;
                                    if v_isSharedCheck_3060_ == 0 {
                                        v_unused_3061_ = lean_ctor_get(v___x_2975_, 4);
                                        lean_dec(v_unused_3061_);
                                        v_unused_3062_ = lean_ctor_get(v___x_2975_, 3);
                                        lean_dec(v_unused_3062_);
                                        v_unused_3063_ = lean_ctor_get(v___x_2975_, 2);
                                        lean_dec(v_unused_3063_);
                                        v_unused_3064_ = lean_ctor_get(v___x_2975_, 1);
                                        lean_dec(v_unused_3064_);
                                        v_unused_3065_ = lean_ctor_get(v___x_2975_, 0);
                                        lean_dec(v_unused_3065_);
                                        v___x_2992_ = v___x_2975_;
                                        v_isShared_2993_ = v_isSharedCheck_3060_;
                                        state = 29;
                                        continue;
                                    } else {
                                        lean_dec(v___x_2975_);
                                        v___x_2992_ = lean_box(0);
                                        v_isShared_2993_ = v_isSharedCheck_3060_;
                                        state = 29;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_3066_ = lean_ctor_get(v_l_2791_, 0);
                                v___x_3067_ = lean_unsigned_to_nat(1);
                                v___x_3068_ = lean_nat_add(v___x_3067_, v_size_3066_);
                                if v_isShared_2795_ == 0 {
                                    lean_ctor_set(v___x_2794_, 4, v___x_2975_);
                                    lean_ctor_set(v___x_2794_, 0, v___x_3068_);
                                    v___x_3070_ = v___x_2794_;
                                    state = 39;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3071_, 0, v___x_3068_);
                                    lean_ctor_set(v_reuseFailAlloc_3071_, 1, v_k_2789_);
                                    lean_ctor_set(v_reuseFailAlloc_3071_, 2, v_v_2790_);
                                    lean_ctor_set(v_reuseFailAlloc_3071_, 3, v_l_2791_);
                                    lean_ctor_set(v_reuseFailAlloc_3071_, 4, v___x_2975_);
                                    v___x_3070_ = v_reuseFailAlloc_3071_;
                                    state = 39;
                                    continue;
                                }
                            }
                        } else {
                            if lean_obj_tag(v___x_2975_) == 0 {
                                v_l_3072_ = lean_ctor_get(v___x_2975_, 3);
                                lean_inc(v_l_3072_);
                                if lean_obj_tag(v_l_3072_) == 0 {
                                    v_r_3073_ = lean_ctor_get(v___x_2975_, 4);
                                    lean_inc(v_r_3073_);
                                    if lean_obj_tag(v_r_3073_) == 0 {
                                        v_size_3074_ = lean_ctor_get(v___x_2975_, 0);
                                        v_k_3075_ = lean_ctor_get(v___x_2975_, 1);
                                        v_v_3076_ = lean_ctor_get(v___x_2975_, 2);
                                        v_isSharedCheck_3090_ =
                                            (!lean_is_exclusive(v___x_2975_)) as u8;
                                        if v_isSharedCheck_3090_ == 0 {
                                            v_unused_3091_ = lean_ctor_get(v___x_2975_, 4);
                                            lean_dec(v_unused_3091_);
                                            v_unused_3092_ = lean_ctor_get(v___x_2975_, 3);
                                            lean_dec(v_unused_3092_);
                                            v___x_3078_ = v___x_2975_;
                                            v_isShared_3079_ = v_isSharedCheck_3090_;
                                            state = 40;
                                            continue;
                                        } else {
                                            lean_inc(v_v_3076_);
                                            lean_inc(v_k_3075_);
                                            lean_inc(v_size_3074_);
                                            lean_dec(v___x_2975_);
                                            v___x_3078_ = lean_box(0);
                                            v_isShared_3079_ = v_isSharedCheck_3090_;
                                            state = 40;
                                            continue;
                                        }
                                    } else {
                                        v_k_3093_ = lean_ctor_get(v___x_2975_, 1);
                                        v_v_3094_ = lean_ctor_get(v___x_2975_, 2);
                                        v_isSharedCheck_3118_ =
                                            (!lean_is_exclusive(v___x_2975_)) as u8;
                                        if v_isSharedCheck_3118_ == 0 {
                                            v_unused_3119_ = lean_ctor_get(v___x_2975_, 4);
                                            lean_dec(v_unused_3119_);
                                            v_unused_3120_ = lean_ctor_get(v___x_2975_, 3);
                                            lean_dec(v_unused_3120_);
                                            v_unused_3121_ = lean_ctor_get(v___x_2975_, 0);
                                            lean_dec(v_unused_3121_);
                                            v___x_3096_ = v___x_2975_;
                                            v_isShared_3097_ = v_isSharedCheck_3118_;
                                            state = 43;
                                            continue;
                                        } else {
                                            lean_inc(v_v_3094_);
                                            lean_inc(v_k_3093_);
                                            lean_dec(v___x_2975_);
                                            v___x_3096_ = lean_box(0);
                                            v_isShared_3097_ = v_isSharedCheck_3118_;
                                            state = 43;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_3122_ = lean_ctor_get(v___x_2975_, 4);
                                    lean_inc(v_r_3122_);
                                    if lean_obj_tag(v_r_3122_) == 0 {
                                        v_k_3123_ = lean_ctor_get(v___x_2975_, 1);
                                        v_v_3124_ = lean_ctor_get(v___x_2975_, 2);
                                        v_isSharedCheck_3136_ =
                                            (!lean_is_exclusive(v___x_2975_)) as u8;
                                        if v_isSharedCheck_3136_ == 0 {
                                            v_unused_3137_ = lean_ctor_get(v___x_2975_, 4);
                                            lean_dec(v_unused_3137_);
                                            v_unused_3138_ = lean_ctor_get(v___x_2975_, 3);
                                            lean_dec(v_unused_3138_);
                                            v_unused_3139_ = lean_ctor_get(v___x_2975_, 0);
                                            lean_dec(v_unused_3139_);
                                            v___x_3126_ = v___x_2975_;
                                            v_isShared_3127_ = v_isSharedCheck_3136_;
                                            state = 48;
                                            continue;
                                        } else {
                                            lean_inc(v_v_3124_);
                                            lean_inc(v_k_3123_);
                                            lean_dec(v___x_2975_);
                                            v___x_3126_ = lean_box(0);
                                            v_isShared_3127_ = v_isSharedCheck_3136_;
                                            state = 48;
                                            continue;
                                        }
                                    } else {
                                        v___x_3140_ = lean_unsigned_to_nat(2);
                                        if v_isShared_2795_ == 0 {
                                            lean_ctor_set(v___x_2794_, 4, v___x_2975_);
                                            lean_ctor_set(v___x_2794_, 3, v_r_3122_);
                                            lean_ctor_set(v___x_2794_, 0, v___x_3140_);
                                            v___x_3142_ = v___x_2794_;
                                            state = 51;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3143_ =
                                                lean_alloc_ctor(0, 5, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3140_);
                                            lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_k_2789_);
                                            lean_ctor_set(v_reuseFailAlloc_3143_, 2, v_v_2790_);
                                            lean_ctor_set(v_reuseFailAlloc_3143_, 3, v_r_3122_);
                                            lean_ctor_set(v_reuseFailAlloc_3143_, 4, v___x_2975_);
                                            v___x_3142_ = v_reuseFailAlloc_3143_;
                                            state = 51;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_3144_ = lean_unsigned_to_nat(1);
                                if v_isShared_2795_ == 0 {
                                    lean_ctor_set(v___x_2794_, 4, v___x_2975_);
                                    lean_ctor_set(v___x_2794_, 3, v___x_2975_);
                                    lean_ctor_set(v___x_2794_, 0, v___x_3144_);
                                    v___x_3146_ = v___x_2794_;
                                    state = 52;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3147_, 0, v___x_3144_);
                                    lean_ctor_set(v_reuseFailAlloc_3147_, 1, v_k_2789_);
                                    lean_ctor_set(v_reuseFailAlloc_3147_, 2, v_v_2790_);
                                    lean_ctor_set(v_reuseFailAlloc_3147_, 3, v___x_2975_);
                                    lean_ctor_set(v_reuseFailAlloc_3147_, 4, v___x_2975_);
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
                if lean_obj_tag(v_l_2802_) == 0 {
                    if lean_obj_tag(v_r_2803_) == 0 {
                        v_size_2816_ = lean_ctor_get(v_l_2802_, 0);
                        v_size_2817_ = lean_ctor_get(v_r_2803_, 0);
                        v_k_2818_ = lean_ctor_get(v_r_2803_, 1);
                        v_v_2819_ = lean_ctor_get(v_r_2803_, 2);
                        v_l_2820_ = lean_ctor_get(v_r_2803_, 3);
                        v_r_2821_ = lean_ctor_get(v_r_2803_, 4);
                        v___x_2822_ = lean_unsigned_to_nat(2);
                        v___x_2823_ = lean_nat_mul(v___x_2822_, v_size_2816_);
                        v___x_2824_ = lean_nat_dec_lt(v_size_2817_, v___x_2823_);
                        lean_dec(v___x_2823_);
                        if v___x_2824_ == 0 {
                            lean_inc(v_r_2821_);
                            lean_inc(v_l_2820_);
                            lean_inc(v_v_2819_);
                            lean_inc(v_k_2818_);
                            v_isSharedCheck_2854_ = (!lean_is_exclusive(v_r_2803_)) as u8;
                            if v_isSharedCheck_2854_ == 0 {
                                v_unused_2855_ = lean_ctor_get(v_r_2803_, 4);
                                lean_dec(v_unused_2855_);
                                v_unused_2856_ = lean_ctor_get(v_r_2803_, 3);
                                lean_dec(v_unused_2856_);
                                v_unused_2857_ = lean_ctor_get(v_r_2803_, 2);
                                lean_dec(v_unused_2857_);
                                v_unused_2858_ = lean_ctor_get(v_r_2803_, 1);
                                lean_dec(v_unused_2858_);
                                v_unused_2859_ = lean_ctor_get(v_r_2803_, 0);
                                lean_dec(v_unused_2859_);
                                v___x_2826_ = v_r_2803_;
                                v_isShared_2827_ = v_isSharedCheck_2854_;
                                state = 4;
                                continue;
                            } else {
                                lean_dec(v_r_2803_);
                                v___x_2826_ = lean_box(0);
                                v_isShared_2827_ = v_isSharedCheck_2854_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2794_);
                            v___x_2860_ = lean_unsigned_to_nat(1);
                            v___x_2861_ = lean_nat_add(v___x_2860_, v_size_2799_);
                            lean_dec(v_size_2799_);
                            v___x_2862_ = lean_nat_add(v___x_2861_, v_size_2798_);
                            lean_dec(v___x_2861_);
                            v___x_2863_ = lean_nat_add(v___x_2860_, v_size_2798_);
                            v___x_2864_ = lean_nat_add(v___x_2863_, v_size_2817_);
                            lean_dec(v___x_2863_);
                            lean_inc_ref(v_r_2792_);
                            if v_isShared_2815_ == 0 {
                                lean_ctor_set(v___x_2814_, 4, v_r_2792_);
                                lean_ctor_set(v___x_2814_, 3, v_r_2803_);
                                lean_ctor_set(v___x_2814_, 2, v_v_2790_);
                                lean_ctor_set(v___x_2814_, 1, v_k_2789_);
                                lean_ctor_set(v___x_2814_, 0, v___x_2864_);
                                v___x_2866_ = v___x_2814_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2864_);
                                lean_ctor_set(v_reuseFailAlloc_2879_, 1, v_k_2789_);
                                lean_ctor_set(v_reuseFailAlloc_2879_, 2, v_v_2790_);
                                lean_ctor_set(v_reuseFailAlloc_2879_, 3, v_r_2803_);
                                lean_ctor_set(v_reuseFailAlloc_2879_, 4, v_r_2792_);
                                v___x_2866_ = v_reuseFailAlloc_2879_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_l_2802_, 5);
                        lean_del_object(v___x_2814_);
                        lean_dec(v_v_2801_);
                        lean_dec(v_k_2800_);
                        lean_dec(v_size_2799_);
                        lean_dec_ref_known(v_r_2792_, 5);
                        lean_del_object(v___x_2794_);
                        lean_dec(v_v_2790_);
                        lean_dec(v_k_2789_);
                        v___x_2880_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__3);
                        v___x_2881_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v___x_2880_);
                        return v___x_2881_;
                    }
                } else {
                    lean_del_object(v___x_2814_);
                    lean_dec(v_r_2803_);
                    lean_dec(v_v_2801_);
                    lean_dec(v_k_2800_);
                    lean_dec(v_size_2799_);
                    lean_dec_ref_known(v_r_2792_, 5);
                    lean_del_object(v___x_2794_);
                    lean_dec(v_v_2790_);
                    lean_dec(v_k_2789_);
                    v___x_2882_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__4);
                    v___x_2883_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v___x_2882_);
                    return v___x_2883_;
                }
            }
            4 => {
                v___x_2828_ = lean_unsigned_to_nat(1);
                v___x_2829_ = lean_nat_add(v___x_2828_, v_size_2799_);
                lean_dec(v_size_2799_);
                v___x_2830_ = lean_nat_add(v___x_2829_, v_size_2798_);
                lean_dec(v___x_2829_);
                v___x_2842_ = lean_nat_add(v___x_2828_, v_size_2816_);
                if lean_obj_tag(v_l_2820_) == 0 {
                    v_size_2852_ = lean_ctor_get(v_l_2820_, 0);
                    lean_inc(v_size_2852_);
                    v___y_2844_ = v_size_2852_;
                    state = 8;
                    continue;
                } else {
                    v___x_2853_ = lean_unsigned_to_nat(0);
                    v___y_2844_ = v___x_2853_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_2835_ = lean_nat_add(v___y_2832_, v___y_2834_);
                lean_dec(v___y_2834_);
                lean_dec(v___y_2832_);
                if v_isShared_2827_ == 0 {
                    lean_ctor_set(v___x_2826_, 4, v_r_2792_);
                    lean_ctor_set(v___x_2826_, 3, v_r_2821_);
                    lean_ctor_set(v___x_2826_, 2, v_v_2790_);
                    lean_ctor_set(v___x_2826_, 1, v_k_2789_);
                    lean_ctor_set(v___x_2826_, 0, v___x_2835_);
                    v___x_2837_ = v___x_2826_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2835_);
                    lean_ctor_set(v_reuseFailAlloc_2841_, 1, v_k_2789_);
                    lean_ctor_set(v_reuseFailAlloc_2841_, 2, v_v_2790_);
                    lean_ctor_set(v_reuseFailAlloc_2841_, 3, v_r_2821_);
                    lean_ctor_set(v_reuseFailAlloc_2841_, 4, v_r_2792_);
                    v___x_2837_ = v_reuseFailAlloc_2841_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2815_ == 0 {
                    lean_ctor_set(v___x_2814_, 4, v___x_2837_);
                    lean_ctor_set(v___x_2814_, 3, v___y_2833_);
                    lean_ctor_set(v___x_2814_, 2, v_v_2819_);
                    lean_ctor_set(v___x_2814_, 1, v_k_2818_);
                    lean_ctor_set(v___x_2814_, 0, v___x_2830_);
                    v___x_2839_ = v___x_2814_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2830_);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_k_2818_);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 2, v_v_2819_);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 3, v___y_2833_);
                    lean_ctor_set(v_reuseFailAlloc_2840_, 4, v___x_2837_);
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
                lean_dec(v___y_2844_);
                lean_dec(v___x_2842_);
                if v_isShared_2795_ == 0 {
                    lean_ctor_set(v___x_2794_, 4, v_l_2820_);
                    lean_ctor_set(v___x_2794_, 3, v_l_2802_);
                    lean_ctor_set(v___x_2794_, 2, v_v_2801_);
                    lean_ctor_set(v___x_2794_, 1, v_k_2800_);
                    lean_ctor_set(v___x_2794_, 0, v___x_2845_);
                    v___x_2847_ = v___x_2794_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2845_);
                    lean_ctor_set(v_reuseFailAlloc_2851_, 1, v_k_2800_);
                    lean_ctor_set(v_reuseFailAlloc_2851_, 2, v_v_2801_);
                    lean_ctor_set(v_reuseFailAlloc_2851_, 3, v_l_2802_);
                    lean_ctor_set(v_reuseFailAlloc_2851_, 4, v_l_2820_);
                    v___x_2847_ = v_reuseFailAlloc_2851_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2848_ = lean_nat_add(v___x_2828_, v_size_2798_);
                if lean_obj_tag(v_r_2821_) == 0 {
                    v_size_2849_ = lean_ctor_get(v_r_2821_, 0);
                    lean_inc(v_size_2849_);
                    v___y_2832_ = v___x_2848_;
                    v___y_2833_ = v___x_2847_;
                    v___y_2834_ = v_size_2849_;
                    state = 5;
                    continue;
                } else {
                    v___x_2850_ = lean_unsigned_to_nat(0);
                    v___y_2832_ = v___x_2848_;
                    v___y_2833_ = v___x_2847_;
                    v___y_2834_ = v___x_2850_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_2873_ = (!lean_is_exclusive(v_r_2792_)) as u8;
                if v_isSharedCheck_2873_ == 0 {
                    v_unused_2874_ = lean_ctor_get(v_r_2792_, 4);
                    lean_dec(v_unused_2874_);
                    v_unused_2875_ = lean_ctor_get(v_r_2792_, 3);
                    lean_dec(v_unused_2875_);
                    v_unused_2876_ = lean_ctor_get(v_r_2792_, 2);
                    lean_dec(v_unused_2876_);
                    v_unused_2877_ = lean_ctor_get(v_r_2792_, 1);
                    lean_dec(v_unused_2877_);
                    v_unused_2878_ = lean_ctor_get(v_r_2792_, 0);
                    lean_dec(v_unused_2878_);
                    v___x_2868_ = v_r_2792_;
                    v_isShared_2869_ = v_isSharedCheck_2873_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_r_2792_);
                    v___x_2868_ = lean_box(0);
                    v_isShared_2869_ = v_isSharedCheck_2873_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2869_ == 0 {
                    lean_ctor_set(v___x_2868_, 4, v___x_2866_);
                    lean_ctor_set(v___x_2868_, 3, v_l_2802_);
                    lean_ctor_set(v___x_2868_, 2, v_v_2801_);
                    lean_ctor_set(v___x_2868_, 1, v_k_2800_);
                    lean_ctor_set(v___x_2868_, 0, v___x_2862_);
                    v___x_2871_ = v___x_2868_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2872_, 0, v___x_2862_);
                    lean_ctor_set(v_reuseFailAlloc_2872_, 1, v_k_2800_);
                    lean_ctor_set(v_reuseFailAlloc_2872_, 2, v_v_2801_);
                    lean_ctor_set(v_reuseFailAlloc_2872_, 3, v_l_2802_);
                    lean_ctor_set(v_reuseFailAlloc_2872_, 4, v___x_2866_);
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
                v_size_2904_ = lean_ctor_get(v_r_2897_, 0);
                v___x_2905_ = lean_unsigned_to_nat(1);
                v___x_2906_ = lean_nat_add(v___x_2905_, v_size_2898_);
                lean_dec(v_size_2898_);
                v___x_2907_ = lean_nat_add(v___x_2905_, v_size_2904_);
                if v_isShared_2903_ == 0 {
                    lean_ctor_set(v___x_2902_, 4, v_r_2792_);
                    lean_ctor_set(v___x_2902_, 3, v_r_2897_);
                    lean_ctor_set(v___x_2902_, 2, v_v_2790_);
                    lean_ctor_set(v___x_2902_, 1, v_k_2789_);
                    lean_ctor_set(v___x_2902_, 0, v___x_2907_);
                    v___x_2909_ = v___x_2902_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2907_);
                    lean_ctor_set(v_reuseFailAlloc_2913_, 1, v_k_2789_);
                    lean_ctor_set(v_reuseFailAlloc_2913_, 2, v_v_2790_);
                    lean_ctor_set(v_reuseFailAlloc_2913_, 3, v_r_2897_);
                    lean_ctor_set(v_reuseFailAlloc_2913_, 4, v_r_2792_);
                    v___x_2909_ = v_reuseFailAlloc_2913_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_2795_ == 0 {
                    lean_ctor_set(v___x_2794_, 4, v___x_2909_);
                    lean_ctor_set(v___x_2794_, 3, v_l_2896_);
                    lean_ctor_set(v___x_2794_, 2, v_v_2900_);
                    lean_ctor_set(v___x_2794_, 1, v_k_2899_);
                    lean_ctor_set(v___x_2794_, 0, v___x_2906_);
                    v___x_2911_ = v___x_2794_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2906_);
                    lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_k_2899_);
                    lean_ctor_set(v_reuseFailAlloc_2912_, 2, v_v_2900_);
                    lean_ctor_set(v_reuseFailAlloc_2912_, 3, v_l_2896_);
                    lean_ctor_set(v_reuseFailAlloc_2912_, 4, v___x_2909_);
                    v___x_2911_ = v_reuseFailAlloc_2912_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2911_;
            }
            17 => {
                v___x_2922_ = lean_unsigned_to_nat(3);
                v___x_2923_ = lean_unsigned_to_nat(1);
                if v_isShared_2921_ == 0 {
                    lean_ctor_set(v___x_2920_, 3, v_r_2897_);
                    lean_ctor_set(v___x_2920_, 2, v_v_2790_);
                    lean_ctor_set(v___x_2920_, 1, v_k_2789_);
                    lean_ctor_set(v___x_2920_, 0, v___x_2923_);
                    v___x_2925_ = v___x_2920_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2929_, 0, v___x_2923_);
                    lean_ctor_set(v_reuseFailAlloc_2929_, 1, v_k_2789_);
                    lean_ctor_set(v_reuseFailAlloc_2929_, 2, v_v_2790_);
                    lean_ctor_set(v_reuseFailAlloc_2929_, 3, v_r_2897_);
                    lean_ctor_set(v_reuseFailAlloc_2929_, 4, v_r_2897_);
                    v___x_2925_ = v_reuseFailAlloc_2929_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_2795_ == 0 {
                    lean_ctor_set(v___x_2794_, 4, v___x_2925_);
                    lean_ctor_set(v___x_2794_, 3, v_l_2896_);
                    lean_ctor_set(v___x_2794_, 2, v_v_2918_);
                    lean_ctor_set(v___x_2794_, 1, v_k_2917_);
                    lean_ctor_set(v___x_2794_, 0, v___x_2922_);
                    v___x_2927_ = v___x_2794_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2928_, 0, v___x_2922_);
                    lean_ctor_set(v_reuseFailAlloc_2928_, 1, v_k_2917_);
                    lean_ctor_set(v_reuseFailAlloc_2928_, 2, v_v_2918_);
                    lean_ctor_set(v_reuseFailAlloc_2928_, 3, v_l_2896_);
                    lean_ctor_set(v_reuseFailAlloc_2928_, 4, v___x_2925_);
                    v___x_2927_ = v_reuseFailAlloc_2928_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2927_;
            }
            20 => {
                v_k_2940_ = lean_ctor_get(v_r_2934_, 1);
                v_v_2941_ = lean_ctor_get(v_r_2934_, 2);
                v_isSharedCheck_2956_ = (!lean_is_exclusive(v_r_2934_)) as u8;
                if v_isSharedCheck_2956_ == 0 {
                    v_unused_2957_ = lean_ctor_get(v_r_2934_, 4);
                    lean_dec(v_unused_2957_);
                    v_unused_2958_ = lean_ctor_get(v_r_2934_, 3);
                    lean_dec(v_unused_2958_);
                    v_unused_2959_ = lean_ctor_get(v_r_2934_, 0);
                    lean_dec(v_unused_2959_);
                    v___x_2943_ = v_r_2934_;
                    v_isShared_2944_ = v_isSharedCheck_2956_;
                    state = 21;
                    continue;
                } else {
                    lean_inc(v_v_2941_);
                    lean_inc(v_k_2940_);
                    lean_dec(v_r_2934_);
                    v___x_2943_ = lean_box(0);
                    v_isShared_2944_ = v_isSharedCheck_2956_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_2945_ = lean_unsigned_to_nat(3);
                v___x_2946_ = lean_unsigned_to_nat(1);
                if v_isShared_2944_ == 0 {
                    lean_ctor_set(v___x_2943_, 4, v_l_2896_);
                    lean_ctor_set(v___x_2943_, 3, v_l_2896_);
                    lean_ctor_set(v___x_2943_, 2, v_v_2936_);
                    lean_ctor_set(v___x_2943_, 1, v_k_2935_);
                    lean_ctor_set(v___x_2943_, 0, v___x_2946_);
                    v___x_2948_ = v___x_2943_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2946_);
                    lean_ctor_set(v_reuseFailAlloc_2955_, 1, v_k_2935_);
                    lean_ctor_set(v_reuseFailAlloc_2955_, 2, v_v_2936_);
                    lean_ctor_set(v_reuseFailAlloc_2955_, 3, v_l_2896_);
                    lean_ctor_set(v_reuseFailAlloc_2955_, 4, v_l_2896_);
                    v___x_2948_ = v_reuseFailAlloc_2955_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_2939_ == 0 {
                    lean_ctor_set(v___x_2938_, 4, v_l_2896_);
                    lean_ctor_set(v___x_2938_, 2, v_v_2790_);
                    lean_ctor_set(v___x_2938_, 1, v_k_2789_);
                    lean_ctor_set(v___x_2938_, 0, v___x_2946_);
                    v___x_2950_ = v___x_2938_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2946_);
                    lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_k_2789_);
                    lean_ctor_set(v_reuseFailAlloc_2954_, 2, v_v_2790_);
                    lean_ctor_set(v_reuseFailAlloc_2954_, 3, v_l_2896_);
                    lean_ctor_set(v_reuseFailAlloc_2954_, 4, v_l_2896_);
                    v___x_2950_ = v_reuseFailAlloc_2954_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_2795_ == 0 {
                    lean_ctor_set(v___x_2794_, 4, v___x_2950_);
                    lean_ctor_set(v___x_2794_, 3, v___x_2948_);
                    lean_ctor_set(v___x_2794_, 2, v_v_2941_);
                    lean_ctor_set(v___x_2794_, 1, v_k_2940_);
                    lean_ctor_set(v___x_2794_, 0, v___x_2945_);
                    v___x_2952_ = v___x_2794_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2945_);
                    lean_ctor_set(v_reuseFailAlloc_2953_, 1, v_k_2940_);
                    lean_ctor_set(v_reuseFailAlloc_2953_, 2, v_v_2941_);
                    lean_ctor_set(v_reuseFailAlloc_2953_, 3, v___x_2948_);
                    lean_ctor_set(v_reuseFailAlloc_2953_, 4, v___x_2950_);
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
                if lean_obj_tag(v_l_2980_) == 0 {
                    if lean_obj_tag(v_r_2981_) == 0 {
                        v_size_2994_ = lean_ctor_get(v_l_2980_, 0);
                        v_k_2995_ = lean_ctor_get(v_l_2980_, 1);
                        v_v_2996_ = lean_ctor_get(v_l_2980_, 2);
                        v_l_2997_ = lean_ctor_get(v_l_2980_, 3);
                        v_r_2998_ = lean_ctor_get(v_l_2980_, 4);
                        v_size_2999_ = lean_ctor_get(v_r_2981_, 0);
                        v___x_3000_ = lean_unsigned_to_nat(2);
                        v___x_3001_ = lean_nat_mul(v___x_3000_, v_size_2999_);
                        v___x_3002_ = lean_nat_dec_lt(v_size_2994_, v___x_3001_);
                        lean_dec(v___x_3001_);
                        if v___x_3002_ == 0 {
                            lean_inc(v_r_2998_);
                            lean_inc(v_l_2997_);
                            lean_inc(v_v_2996_);
                            lean_inc(v_k_2995_);
                            v_isSharedCheck_3031_ = (!lean_is_exclusive(v_l_2980_)) as u8;
                            if v_isSharedCheck_3031_ == 0 {
                                v_unused_3032_ = lean_ctor_get(v_l_2980_, 4);
                                lean_dec(v_unused_3032_);
                                v_unused_3033_ = lean_ctor_get(v_l_2980_, 3);
                                lean_dec(v_unused_3033_);
                                v_unused_3034_ = lean_ctor_get(v_l_2980_, 2);
                                lean_dec(v_unused_3034_);
                                v_unused_3035_ = lean_ctor_get(v_l_2980_, 1);
                                lean_dec(v_unused_3035_);
                                v_unused_3036_ = lean_ctor_get(v_l_2980_, 0);
                                lean_dec(v_unused_3036_);
                                v___x_3004_ = v_l_2980_;
                                v_isShared_3005_ = v_isSharedCheck_3031_;
                                state = 30;
                                continue;
                            } else {
                                lean_dec(v_l_2980_);
                                v___x_3004_ = lean_box(0);
                                v_isShared_3005_ = v_isSharedCheck_3031_;
                                state = 30;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2794_);
                            v___x_3037_ = lean_unsigned_to_nat(1);
                            v___x_3038_ = lean_nat_add(v___x_3037_, v_size_2976_);
                            v___x_3039_ = lean_nat_add(v___x_3038_, v_size_2977_);
                            lean_dec(v_size_2977_);
                            v___x_3040_ = lean_nat_add(v___x_3038_, v_size_2994_);
                            lean_dec(v___x_3038_);
                            lean_inc_ref(v_l_2791_);
                            if v_isShared_2993_ == 0 {
                                lean_ctor_set(v___x_2992_, 4, v_l_2980_);
                                lean_ctor_set(v___x_2992_, 3, v_l_2791_);
                                lean_ctor_set(v___x_2992_, 2, v_v_2790_);
                                lean_ctor_set(v___x_2992_, 1, v_k_2789_);
                                lean_ctor_set(v___x_2992_, 0, v___x_3040_);
                                v___x_3042_ = v___x_2992_;
                                state = 36;
                                continue;
                            } else {
                                v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3040_);
                                lean_ctor_set(v_reuseFailAlloc_3055_, 1, v_k_2789_);
                                lean_ctor_set(v_reuseFailAlloc_3055_, 2, v_v_2790_);
                                lean_ctor_set(v_reuseFailAlloc_3055_, 3, v_l_2791_);
                                lean_ctor_set(v_reuseFailAlloc_3055_, 4, v_l_2980_);
                                v___x_3042_ = v_reuseFailAlloc_3055_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_l_2980_, 5);
                        lean_del_object(v___x_2992_);
                        lean_dec(v_v_2979_);
                        lean_dec(v_k_2978_);
                        lean_dec(v_size_2977_);
                        lean_dec_ref_known(v_l_2791_, 5);
                        lean_del_object(v___x_2794_);
                        lean_dec(v_v_2790_);
                        lean_dec(v_k_2789_);
                        v___x_3056_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__7);
                        v___x_3057_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v___x_3056_);
                        return v___x_3057_;
                    }
                } else {
                    lean_del_object(v___x_2992_);
                    lean_dec(v_r_2981_);
                    lean_dec(v_v_2979_);
                    lean_dec(v_k_2978_);
                    lean_dec(v_size_2977_);
                    lean_dec_ref_known(v_l_2791_, 5);
                    lean_del_object(v___x_2794_);
                    lean_dec(v_v_2790_);
                    lean_dec(v_k_2789_);
                    v___x_3058_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg___closed__8);
                    v___x_3059_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v___x_3058_);
                    return v___x_3059_;
                }
            }
            30 => {
                v___x_3006_ = lean_unsigned_to_nat(1);
                v___x_3007_ = lean_nat_add(v___x_3006_, v_size_2976_);
                v___x_3008_ = lean_nat_add(v___x_3007_, v_size_2977_);
                lean_dec(v_size_2977_);
                if lean_obj_tag(v_l_2997_) == 0 {
                    v_size_3029_ = lean_ctor_get(v_l_2997_, 0);
                    lean_inc(v_size_3029_);
                    v___y_3021_ = v_size_3029_;
                    state = 34;
                    continue;
                } else {
                    v___x_3030_ = lean_unsigned_to_nat(0);
                    v___y_3021_ = v___x_3030_;
                    state = 34;
                    continue;
                }
            }
            31 => {
                v___x_3013_ = lean_nat_add(v___y_3011_, v___y_3012_);
                lean_dec(v___y_3012_);
                lean_dec(v___y_3011_);
                if v_isShared_3005_ == 0 {
                    lean_ctor_set(v___x_3004_, 4, v_r_2981_);
                    lean_ctor_set(v___x_3004_, 3, v_r_2998_);
                    lean_ctor_set(v___x_3004_, 2, v_v_2979_);
                    lean_ctor_set(v___x_3004_, 1, v_k_2978_);
                    lean_ctor_set(v___x_3004_, 0, v___x_3013_);
                    v___x_3015_ = v___x_3004_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_3013_);
                    lean_ctor_set(v_reuseFailAlloc_3019_, 1, v_k_2978_);
                    lean_ctor_set(v_reuseFailAlloc_3019_, 2, v_v_2979_);
                    lean_ctor_set(v_reuseFailAlloc_3019_, 3, v_r_2998_);
                    lean_ctor_set(v_reuseFailAlloc_3019_, 4, v_r_2981_);
                    v___x_3015_ = v_reuseFailAlloc_3019_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_2993_ == 0 {
                    lean_ctor_set(v___x_2992_, 4, v___x_3015_);
                    lean_ctor_set(v___x_2992_, 3, v___y_3010_);
                    lean_ctor_set(v___x_2992_, 2, v_v_2996_);
                    lean_ctor_set(v___x_2992_, 1, v_k_2995_);
                    lean_ctor_set(v___x_2992_, 0, v___x_3008_);
                    v___x_3017_ = v___x_2992_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3018_, 0, v___x_3008_);
                    lean_ctor_set(v_reuseFailAlloc_3018_, 1, v_k_2995_);
                    lean_ctor_set(v_reuseFailAlloc_3018_, 2, v_v_2996_);
                    lean_ctor_set(v_reuseFailAlloc_3018_, 3, v___y_3010_);
                    lean_ctor_set(v_reuseFailAlloc_3018_, 4, v___x_3015_);
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
                lean_dec(v___y_3021_);
                lean_dec(v___x_3007_);
                if v_isShared_2795_ == 0 {
                    lean_ctor_set(v___x_2794_, 4, v_l_2997_);
                    lean_ctor_set(v___x_2794_, 0, v___x_3022_);
                    v___x_3024_ = v___x_2794_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3022_);
                    lean_ctor_set(v_reuseFailAlloc_3028_, 1, v_k_2789_);
                    lean_ctor_set(v_reuseFailAlloc_3028_, 2, v_v_2790_);
                    lean_ctor_set(v_reuseFailAlloc_3028_, 3, v_l_2791_);
                    lean_ctor_set(v_reuseFailAlloc_3028_, 4, v_l_2997_);
                    v___x_3024_ = v_reuseFailAlloc_3028_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_3025_ = lean_nat_add(v___x_3006_, v_size_2999_);
                if lean_obj_tag(v_r_2998_) == 0 {
                    v_size_3026_ = lean_ctor_get(v_r_2998_, 0);
                    lean_inc(v_size_3026_);
                    v___y_3010_ = v___x_3024_;
                    v___y_3011_ = v___x_3025_;
                    v___y_3012_ = v_size_3026_;
                    state = 31;
                    continue;
                } else {
                    v___x_3027_ = lean_unsigned_to_nat(0);
                    v___y_3010_ = v___x_3024_;
                    v___y_3011_ = v___x_3025_;
                    v___y_3012_ = v___x_3027_;
                    state = 31;
                    continue;
                }
            }
            36 => {
                v_isSharedCheck_3049_ = (!lean_is_exclusive(v_l_2791_)) as u8;
                if v_isSharedCheck_3049_ == 0 {
                    v_unused_3050_ = lean_ctor_get(v_l_2791_, 4);
                    lean_dec(v_unused_3050_);
                    v_unused_3051_ = lean_ctor_get(v_l_2791_, 3);
                    lean_dec(v_unused_3051_);
                    v_unused_3052_ = lean_ctor_get(v_l_2791_, 2);
                    lean_dec(v_unused_3052_);
                    v_unused_3053_ = lean_ctor_get(v_l_2791_, 1);
                    lean_dec(v_unused_3053_);
                    v_unused_3054_ = lean_ctor_get(v_l_2791_, 0);
                    lean_dec(v_unused_3054_);
                    v___x_3044_ = v_l_2791_;
                    v_isShared_3045_ = v_isSharedCheck_3049_;
                    state = 37;
                    continue;
                } else {
                    lean_dec(v_l_2791_);
                    v___x_3044_ = lean_box(0);
                    v_isShared_3045_ = v_isSharedCheck_3049_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_3045_ == 0 {
                    lean_ctor_set(v___x_3044_, 4, v_r_2981_);
                    lean_ctor_set(v___x_3044_, 3, v___x_3042_);
                    lean_ctor_set(v___x_3044_, 2, v_v_2979_);
                    lean_ctor_set(v___x_3044_, 1, v_k_2978_);
                    lean_ctor_set(v___x_3044_, 0, v___x_3039_);
                    v___x_3047_ = v___x_3044_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3039_);
                    lean_ctor_set(v_reuseFailAlloc_3048_, 1, v_k_2978_);
                    lean_ctor_set(v_reuseFailAlloc_3048_, 2, v_v_2979_);
                    lean_ctor_set(v_reuseFailAlloc_3048_, 3, v___x_3042_);
                    lean_ctor_set(v_reuseFailAlloc_3048_, 4, v_r_2981_);
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
                v_size_3080_ = lean_ctor_get(v_l_3072_, 0);
                v___x_3081_ = lean_unsigned_to_nat(1);
                v___x_3082_ = lean_nat_add(v___x_3081_, v_size_3074_);
                lean_dec(v_size_3074_);
                v___x_3083_ = lean_nat_add(v___x_3081_, v_size_3080_);
                if v_isShared_3079_ == 0 {
                    lean_ctor_set(v___x_3078_, 4, v_l_3072_);
                    lean_ctor_set(v___x_3078_, 3, v_l_2791_);
                    lean_ctor_set(v___x_3078_, 2, v_v_2790_);
                    lean_ctor_set(v___x_3078_, 1, v_k_2789_);
                    lean_ctor_set(v___x_3078_, 0, v___x_3083_);
                    v___x_3085_ = v___x_3078_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3089_, 0, v___x_3083_);
                    lean_ctor_set(v_reuseFailAlloc_3089_, 1, v_k_2789_);
                    lean_ctor_set(v_reuseFailAlloc_3089_, 2, v_v_2790_);
                    lean_ctor_set(v_reuseFailAlloc_3089_, 3, v_l_2791_);
                    lean_ctor_set(v_reuseFailAlloc_3089_, 4, v_l_3072_);
                    v___x_3085_ = v_reuseFailAlloc_3089_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                if v_isShared_2795_ == 0 {
                    lean_ctor_set(v___x_2794_, 4, v_r_3073_);
                    lean_ctor_set(v___x_2794_, 3, v___x_3085_);
                    lean_ctor_set(v___x_2794_, 2, v_v_3076_);
                    lean_ctor_set(v___x_2794_, 1, v_k_3075_);
                    lean_ctor_set(v___x_2794_, 0, v___x_3082_);
                    v___x_3087_ = v___x_2794_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3082_);
                    lean_ctor_set(v_reuseFailAlloc_3088_, 1, v_k_3075_);
                    lean_ctor_set(v_reuseFailAlloc_3088_, 2, v_v_3076_);
                    lean_ctor_set(v_reuseFailAlloc_3088_, 3, v___x_3085_);
                    lean_ctor_set(v_reuseFailAlloc_3088_, 4, v_r_3073_);
                    v___x_3087_ = v_reuseFailAlloc_3088_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_3087_;
            }
            43 => {
                v_k_3098_ = lean_ctor_get(v_l_3072_, 1);
                v_v_3099_ = lean_ctor_get(v_l_3072_, 2);
                v_isSharedCheck_3114_ = (!lean_is_exclusive(v_l_3072_)) as u8;
                if v_isSharedCheck_3114_ == 0 {
                    v_unused_3115_ = lean_ctor_get(v_l_3072_, 4);
                    lean_dec(v_unused_3115_);
                    v_unused_3116_ = lean_ctor_get(v_l_3072_, 3);
                    lean_dec(v_unused_3116_);
                    v_unused_3117_ = lean_ctor_get(v_l_3072_, 0);
                    lean_dec(v_unused_3117_);
                    v___x_3101_ = v_l_3072_;
                    v_isShared_3102_ = v_isSharedCheck_3114_;
                    state = 44;
                    continue;
                } else {
                    lean_inc(v_v_3099_);
                    lean_inc(v_k_3098_);
                    lean_dec(v_l_3072_);
                    v___x_3101_ = lean_box(0);
                    v_isShared_3102_ = v_isSharedCheck_3114_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                v___x_3103_ = lean_unsigned_to_nat(3);
                v___x_3104_ = lean_unsigned_to_nat(1);
                if v_isShared_3102_ == 0 {
                    lean_ctor_set(v___x_3101_, 4, v_r_3073_);
                    lean_ctor_set(v___x_3101_, 3, v_r_3073_);
                    lean_ctor_set(v___x_3101_, 2, v_v_2790_);
                    lean_ctor_set(v___x_3101_, 1, v_k_2789_);
                    lean_ctor_set(v___x_3101_, 0, v___x_3104_);
                    v___x_3106_ = v___x_3101_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3104_);
                    lean_ctor_set(v_reuseFailAlloc_3113_, 1, v_k_2789_);
                    lean_ctor_set(v_reuseFailAlloc_3113_, 2, v_v_2790_);
                    lean_ctor_set(v_reuseFailAlloc_3113_, 3, v_r_3073_);
                    lean_ctor_set(v_reuseFailAlloc_3113_, 4, v_r_3073_);
                    v___x_3106_ = v_reuseFailAlloc_3113_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_3097_ == 0 {
                    lean_ctor_set(v___x_3096_, 3, v_r_3073_);
                    lean_ctor_set(v___x_3096_, 0, v___x_3104_);
                    v___x_3108_ = v___x_3096_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3112_, 0, v___x_3104_);
                    lean_ctor_set(v_reuseFailAlloc_3112_, 1, v_k_3093_);
                    lean_ctor_set(v_reuseFailAlloc_3112_, 2, v_v_3094_);
                    lean_ctor_set(v_reuseFailAlloc_3112_, 3, v_r_3073_);
                    lean_ctor_set(v_reuseFailAlloc_3112_, 4, v_r_3073_);
                    v___x_3108_ = v_reuseFailAlloc_3112_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                if v_isShared_2795_ == 0 {
                    lean_ctor_set(v___x_2794_, 4, v___x_3108_);
                    lean_ctor_set(v___x_2794_, 3, v___x_3106_);
                    lean_ctor_set(v___x_2794_, 2, v_v_3099_);
                    lean_ctor_set(v___x_2794_, 1, v_k_3098_);
                    lean_ctor_set(v___x_2794_, 0, v___x_3103_);
                    v___x_3110_ = v___x_2794_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3103_);
                    lean_ctor_set(v_reuseFailAlloc_3111_, 1, v_k_3098_);
                    lean_ctor_set(v_reuseFailAlloc_3111_, 2, v_v_3099_);
                    lean_ctor_set(v_reuseFailAlloc_3111_, 3, v___x_3106_);
                    lean_ctor_set(v_reuseFailAlloc_3111_, 4, v___x_3108_);
                    v___x_3110_ = v_reuseFailAlloc_3111_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_3110_;
            }
            48 => {
                v___x_3128_ = lean_unsigned_to_nat(3);
                v___x_3129_ = lean_unsigned_to_nat(1);
                if v_isShared_3127_ == 0 {
                    lean_ctor_set(v___x_3126_, 4, v_l_3072_);
                    lean_ctor_set(v___x_3126_, 2, v_v_2790_);
                    lean_ctor_set(v___x_3126_, 1, v_k_2789_);
                    lean_ctor_set(v___x_3126_, 0, v___x_3129_);
                    v___x_3131_ = v___x_3126_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3129_);
                    lean_ctor_set(v_reuseFailAlloc_3135_, 1, v_k_2789_);
                    lean_ctor_set(v_reuseFailAlloc_3135_, 2, v_v_2790_);
                    lean_ctor_set(v_reuseFailAlloc_3135_, 3, v_l_3072_);
                    lean_ctor_set(v_reuseFailAlloc_3135_, 4, v_l_3072_);
                    v___x_3131_ = v_reuseFailAlloc_3135_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                if v_isShared_2795_ == 0 {
                    lean_ctor_set(v___x_2794_, 4, v_r_3122_);
                    lean_ctor_set(v___x_2794_, 3, v___x_3131_);
                    lean_ctor_set(v___x_2794_, 2, v_v_3124_);
                    lean_ctor_set(v___x_2794_, 1, v_k_3123_);
                    lean_ctor_set(v___x_2794_, 0, v___x_3128_);
                    v___x_3133_ = v___x_2794_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3128_);
                    lean_ctor_set(v_reuseFailAlloc_3134_, 1, v_k_3123_);
                    lean_ctor_set(v_reuseFailAlloc_3134_, 2, v_v_3124_);
                    lean_ctor_set(v_reuseFailAlloc_3134_, 3, v___x_3131_);
                    lean_ctor_set(v_reuseFailAlloc_3134_, 4, v_r_3122_);
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
    mut v_init_3151_: *mut LeanObject,
    mut v_x_3152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: u8 = 0;
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3152_) == 0 {
                    v_k_3153_ = lean_ctor_get(v_x_3152_, 1);
                    lean_inc(v_k_3153_);
                    v_v_3154_ = lean_ctor_get(v_x_3152_, 2);
                    lean_inc(v_v_3154_);
                    v_l_3155_ = lean_ctor_get(v_x_3152_, 3);
                    lean_inc(v_l_3155_);
                    v_r_3156_ = lean_ctor_get(v_x_3152_, 4);
                    lean_inc(v_r_3156_);
                    lean_dec_ref_known(v_x_3152_, 5);
                    v___x_3157_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1_spec__5(v_init_3151_, v_l_3155_);
                    v___x_3158_ = 1;
                    v___x_3159_ = l_Lean_Name_toString(v_k_3153_, v___x_3158_);
                    v___x_3160_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_3160_, 0, v_v_3154_);
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
    mut v_m_3163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    v___x_3164_ = lean_box(1);
    v___x_3165_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1_spec__5(v___x_3164_, v_m_3163_);
    v___x_3166_ = lean_alloc_ctor(5, 1, (0) as u32);
    lean_ctor_set(v___x_3166_, 0, v___x_3165_);
    return v___x_3166_;
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson(
    mut v_x_3167_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3167_) == 0 {
        let mut v_name_3168_: *mut LeanObject = core::ptr::null_mut();
        let mut v_opts_3169_: *mut LeanObject = core::ptr::null_mut();
        let mut v_inherited_3170_: u8 = 0;
        let mut v_dir_3171_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3174_: u8 = 0;
        let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
        v_name_3168_ = lean_ctor_get(v_x_3167_, 0);
        lean_inc(v_name_3168_);
        v_opts_3169_ = lean_ctor_get(v_x_3167_, 1);
        lean_inc(v_opts_3169_);
        v_inherited_3170_ = lean_ctor_get_uint8(
            v_x_3167_,
            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        );
        v_dir_3171_ = lean_ctor_get(v_x_3167_, 2);
        lean_inc_ref(v_dir_3171_);
        lean_dec_ref_known(v_x_3167_, 3);
        v___x_3172_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__2;
        v___x_3173_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6;
        v___x_3174_ = 1;
        v___x_3175_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_name_3168_,
            v___x_3174_,
        );
        v___x_3176_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_3176_, 0, v___x_3175_);
        v___x_3177_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3177_, 0, v___x_3173_);
        lean_ctor_set(v___x_3177_, 1, v___x_3176_);
        v___x_3178_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__8;
        v___x_3179_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0(v_opts_3169_);
        v___x_3180_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3180_, 0, v___x_3178_);
        lean_ctor_set(v___x_3180_, 1, v___x_3179_);
        v___x_3181_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10;
        v___x_3182_ = lean_alloc_ctor(1, 0, (1) as u32);
        lean_ctor_set_uint8(v___x_3182_, 0 as u32, v_inherited_3170_);
        v___x_3183_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3183_, 0, v___x_3181_);
        lean_ctor_set(v___x_3183_, 1, v___x_3182_);
        v___x_3184_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22;
        v___x_3185_ = l_Lake_mkRelPathString(v_dir_3171_);
        v___x_3186_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_3186_, 0, v___x_3185_);
        v___x_3187_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3187_, 0, v___x_3184_);
        lean_ctor_set(v___x_3187_, 1, v___x_3186_);
        v___x_3188_ = lean_box(0);
        v___x_3189_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3189_, 0, v___x_3187_);
        lean_ctor_set(v___x_3189_, 1, v___x_3188_);
        v___x_3190_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3190_, 0, v___x_3183_);
        lean_ctor_set(v___x_3190_, 1, v___x_3189_);
        v___x_3191_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3191_, 0, v___x_3180_);
        lean_ctor_set(v___x_3191_, 1, v___x_3190_);
        v___x_3192_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3192_, 0, v___x_3177_);
        lean_ctor_set(v___x_3192_, 1, v___x_3191_);
        v___x_3193_ = l_Lean_Json_mkObj(v___x_3192_);
        lean_dec_ref_known(v___x_3192_, 2);
        v___x_3194_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3194_, 0, v___x_3172_);
        lean_ctor_set(v___x_3194_, 1, v___x_3193_);
        v___x_3195_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3195_, 0, v___x_3194_);
        lean_ctor_set(v___x_3195_, 1, v___x_3188_);
        v___x_3196_ = l_Lean_Json_mkObj(v___x_3195_);
        lean_dec_ref_known(v___x_3195_, 2);
        return v___x_3196_;
    } else {
        let mut v_name_3197_: *mut LeanObject = core::ptr::null_mut();
        let mut v_opts_3198_: *mut LeanObject = core::ptr::null_mut();
        let mut v_inherited_3199_: u8 = 0;
        let mut v_url_3200_: *mut LeanObject = core::ptr::null_mut();
        let mut v_rev_3201_: *mut LeanObject = core::ptr::null_mut();
        let mut v_inputRev_x3f_3202_: *mut LeanObject = core::ptr::null_mut();
        let mut v_subDir_x3f_3203_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3206_: u8 = 0;
        let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
        v_name_3197_ = lean_ctor_get(v_x_3167_, 0);
        lean_inc(v_name_3197_);
        v_opts_3198_ = lean_ctor_get(v_x_3167_, 1);
        lean_inc(v_opts_3198_);
        v_inherited_3199_ = lean_ctor_get_uint8(
            v_x_3167_,
            (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
        );
        v_url_3200_ = lean_ctor_get(v_x_3167_, 2);
        lean_inc_ref(v_url_3200_);
        v_rev_3201_ = lean_ctor_get(v_x_3167_, 3);
        lean_inc_ref(v_rev_3201_);
        v_inputRev_x3f_3202_ = lean_ctor_get(v_x_3167_, 4);
        lean_inc(v_inputRev_x3f_3202_);
        v_subDir_x3f_3203_ = lean_ctor_get(v_x_3167_, 5);
        lean_inc(v_subDir_x3f_3203_);
        lean_dec_ref_known(v_x_3167_, 6);
        v___x_3204_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__3;
        v___x_3205_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6;
        v___x_3206_ = 1;
        v___x_3207_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_name_3197_,
            v___x_3206_,
        );
        v___x_3208_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_3208_, 0, v___x_3207_);
        v___x_3209_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3209_, 0, v___x_3205_);
        lean_ctor_set(v___x_3209_, 1, v___x_3208_);
        v___x_3210_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__8;
        v___x_3211_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0(v_opts_3198_);
        v___x_3212_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3212_, 0, v___x_3210_);
        lean_ctor_set(v___x_3212_, 1, v___x_3211_);
        v___x_3213_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10;
        v___x_3214_ = lean_alloc_ctor(1, 0, (1) as u32);
        lean_ctor_set_uint8(v___x_3214_, 0 as u32, v_inherited_3199_);
        v___x_3215_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3215_, 0, v___x_3213_);
        lean_ctor_set(v___x_3215_, 1, v___x_3214_);
        v___x_3216_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12;
        v___x_3217_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_3217_, 0, v_url_3200_);
        v___x_3218_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3218_, 0, v___x_3216_);
        lean_ctor_set(v___x_3218_, 1, v___x_3217_);
        v___x_3219_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14;
        v___x_3220_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_3220_, 0, v_rev_3201_);
        v___x_3221_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3221_, 0, v___x_3219_);
        lean_ctor_set(v___x_3221_, 1, v___x_3220_);
        v___x_3222_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__16;
        v___x_3223_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__1(v_inputRev_x3f_3202_);
        v___x_3224_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3224_, 0, v___x_3222_);
        lean_ctor_set(v___x_3224_, 1, v___x_3223_);
        v___x_3225_ =
            l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__18;
        v___x_3226_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_subDir_x3f_3203_);
        v___x_3227_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3227_, 0, v___x_3225_);
        lean_ctor_set(v___x_3227_, 1, v___x_3226_);
        v___x_3228_ = lean_box(0);
        v___x_3229_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3229_, 0, v___x_3227_);
        lean_ctor_set(v___x_3229_, 1, v___x_3228_);
        v___x_3230_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3230_, 0, v___x_3224_);
        lean_ctor_set(v___x_3230_, 1, v___x_3229_);
        v___x_3231_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3231_, 0, v___x_3221_);
        lean_ctor_set(v___x_3231_, 1, v___x_3230_);
        v___x_3232_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3232_, 0, v___x_3218_);
        lean_ctor_set(v___x_3232_, 1, v___x_3231_);
        v___x_3233_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3233_, 0, v___x_3215_);
        lean_ctor_set(v___x_3233_, 1, v___x_3232_);
        v___x_3234_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3234_, 0, v___x_3212_);
        lean_ctor_set(v___x_3234_, 1, v___x_3233_);
        v___x_3235_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3235_, 0, v___x_3209_);
        lean_ctor_set(v___x_3235_, 1, v___x_3234_);
        v___x_3236_ = l_Lean_Json_mkObj(v___x_3235_);
        lean_dec_ref_known(v___x_3235_, 2);
        v___x_3237_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3237_, 0, v___x_3204_);
        lean_ctor_set(v___x_3237_, 1, v___x_3236_);
        v___x_3238_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3238_, 0, v___x_3237_);
        lean_ctor_set(v___x_3238_, 1, v___x_3228_);
        v___x_3239_ = l_Lean_Json_mkObj(v___x_3238_);
        lean_dec_ref_known(v___x_3238_, 2);
        return v___x_3239_;
    }
}
pub unsafe fn l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3(
    mut v_00_u03b2_3240_: *mut LeanObject,
    mut v_msg_3241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    v___x_3242_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0_spec__3___redArg(v_msg_3241_);
    return v___x_3242_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0(
    mut v_00_u03b2_3243_: *mut LeanObject,
    mut v_k_3244_: *mut LeanObject,
    mut v_v_3245_: *mut LeanObject,
    mut v_t_3246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    v___x_3247_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__0___redArg(v_k_3244_, v_v_3245_, v_t_3246_);
    return v___x_3247_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1(
    mut v_init_3248_: *mut LeanObject,
    mut v_t_3249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    v___x_3250_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__0_spec__1_spec__5(v_init_3248_, v_t_3249_);
    return v___x_3250_;
}
pub unsafe fn l_Lake_PackageEntrySrc_ctorIdx(mut v_x_3260_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_3260_) == 0 {
        let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
        v___x_3261_ = lean_unsigned_to_nat(0);
        return v___x_3261_;
    } else {
        let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
        v___x_3262_ = lean_unsigned_to_nat(1);
        return v___x_3262_;
    }
}
pub unsafe fn l_Lake_PackageEntrySrc_ctorIdx___boxed(
    mut v_x_3263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3264_: *mut LeanObject = core::ptr::null_mut();
    v_res_3264_ = l_Lake_PackageEntrySrc_ctorIdx(v_x_3263_);
    lean_dec_ref(v_x_3263_);
    return v_res_3264_;
}
pub unsafe fn l_Lake_PackageEntrySrc_ctorElim___redArg(
    mut v_t_3265_: *mut LeanObject,
    mut v_k_3266_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_3265_) == 0 {
        let mut v_dir_3267_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
        v_dir_3267_ = lean_ctor_get(v_t_3265_, 0);
        lean_inc_ref(v_dir_3267_);
        lean_dec_ref_known(v_t_3265_, 1);
        v___x_3268_ = lean_apply_1(v_k_3266_, v_dir_3267_);
        return v___x_3268_;
    } else {
        let mut v_url_3269_: *mut LeanObject = core::ptr::null_mut();
        let mut v_rev_3270_: *mut LeanObject = core::ptr::null_mut();
        let mut v_inputRev_x3f_3271_: *mut LeanObject = core::ptr::null_mut();
        let mut v_subDir_x3f_3272_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
        v_url_3269_ = lean_ctor_get(v_t_3265_, 0);
        lean_inc_ref(v_url_3269_);
        v_rev_3270_ = lean_ctor_get(v_t_3265_, 1);
        lean_inc_ref(v_rev_3270_);
        v_inputRev_x3f_3271_ = lean_ctor_get(v_t_3265_, 2);
        lean_inc(v_inputRev_x3f_3271_);
        v_subDir_x3f_3272_ = lean_ctor_get(v_t_3265_, 3);
        lean_inc(v_subDir_x3f_3272_);
        lean_dec_ref_known(v_t_3265_, 4);
        v___x_3273_ = lean_apply_4(
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
    mut v_motive_3274_: *mut LeanObject,
    mut v_ctorIdx_3275_: *mut LeanObject,
    mut v_t_3276_: *mut LeanObject,
    mut v_h_3277_: *mut LeanObject,
    mut v_k_3278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    v___x_3279_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_3276_, v_k_3278_);
    return v___x_3279_;
}
pub unsafe fn l_Lake_PackageEntrySrc_ctorElim___boxed(
    mut v_motive_3280_: *mut LeanObject,
    mut v_ctorIdx_3281_: *mut LeanObject,
    mut v_t_3282_: *mut LeanObject,
    mut v_h_3283_: *mut LeanObject,
    mut v_k_3284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3285_: *mut LeanObject = core::ptr::null_mut();
    v_res_3285_ = l_Lake_PackageEntrySrc_ctorElim(
        v_motive_3280_,
        v_ctorIdx_3281_,
        v_t_3282_,
        v_h_3283_,
        v_k_3284_,
    );
    lean_dec(v_ctorIdx_3281_);
    return v_res_3285_;
}
pub unsafe fn l_Lake_PackageEntrySrc_path_elim___redArg(
    mut v_t_3286_: *mut LeanObject,
    mut v_path_3287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    v___x_3288_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_3286_, v_path_3287_);
    return v___x_3288_;
}
pub unsafe fn l_Lake_PackageEntrySrc_path_elim(
    mut v_motive_3289_: *mut LeanObject,
    mut v_t_3290_: *mut LeanObject,
    mut v_h_3291_: *mut LeanObject,
    mut v_path_3292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    v___x_3293_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_3290_, v_path_3292_);
    return v___x_3293_;
}
pub unsafe fn l_Lake_PackageEntrySrc_git_elim___redArg(
    mut v_t_3294_: *mut LeanObject,
    mut v_git_3295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    v___x_3296_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_3294_, v_git_3295_);
    return v___x_3296_;
}
pub unsafe fn l_Lake_PackageEntrySrc_git_elim(
    mut v_motive_3297_: *mut LeanObject,
    mut v_t_3298_: *mut LeanObject,
    mut v_h_3299_: *mut LeanObject,
    mut v_git_3300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    v___x_3301_ = l_Lake_PackageEntrySrc_ctorElim___redArg(v_t_3298_, v_git_3300_);
    return v___x_3301_;
}
pub unsafe fn _init_l_Lake_instInhabitedPackageEntry_default___closed__0() -> *mut LeanObject {
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: u8 = 0;
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    v___x_3306_ = l_Lake_instInhabitedPackageEntrySrc_default;
    v___x_3307_ = lean_box(0);
    v___x_3308_ = l_Lake_defaultConfigFile;
    v___x_3309_ = 0;
    v___x_3310_ = l_Lake_Manifest_version___closed__1;
    v___x_3311_ = lean_box(0);
    v___x_3312_ = lean_alloc_ctor(0, 5, (1) as u32);
    lean_ctor_set(v___x_3312_, 0, v___x_3311_);
    lean_ctor_set(v___x_3312_, 1, v___x_3310_);
    lean_ctor_set(v___x_3312_, 2, v___x_3308_);
    lean_ctor_set(v___x_3312_, 3, v___x_3307_);
    lean_ctor_set(v___x_3312_, 4, v___x_3306_);
    lean_ctor_set_uint8(
        v___x_3312_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_3309_,
    );
    return v___x_3312_;
}
pub unsafe fn _init_l_Lake_instInhabitedPackageEntry_default() -> *mut LeanObject {
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    v___x_3313_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPackageEntry_default___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPackageEntry_default___closed__0_once),
        _init_l_Lake_instInhabitedPackageEntry_default___closed__0,
    );
    return v___x_3313_;
}
pub unsafe fn _init_l_Lake_instInhabitedPackageEntry() -> *mut LeanObject {
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    v___x_3314_ = l_Lake_instInhabitedPackageEntry_default;
    return v___x_3314_;
}
pub unsafe fn l_Lake_PackageEntry_prettyName(
    mut v_entry_3315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: u8 = 0;
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    v_name_3316_ = lean_ctor_get(v_entry_3315_, 0);
    lean_inc(v_name_3316_);
    lean_dec_ref(v_entry_3315_);
    v___x_3317_ = 0;
    v___x_3318_ = l_Lean_Name_toString(v_name_3316_, v___x_3317_);
    return v___x_3318_;
}
pub unsafe fn l_Lake_PackageEntry_toJson(mut v_entry_3335_: *mut LeanObject) -> *mut LeanObject {
    let mut v_name_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scope_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inherited_3338_: u8 = 0;
    let mut v_configFile_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_manifestFile_x3f_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_src_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: u8 = 0;
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fields_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dir_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3369_: u8 = 0;
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3381_: u8 = 0;
    let mut v_url_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rev_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inputRev_x3f_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subDir_x3f_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_3336_ = lean_ctor_get(v_entry_3335_, 0);
                lean_inc(v_name_3336_);
                v_scope_3337_ = lean_ctor_get(v_entry_3335_, 1);
                lean_inc_ref(v_scope_3337_);
                v_inherited_3338_ = lean_ctor_get_uint8(
                    v_entry_3335_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                );
                v_configFile_3339_ = lean_ctor_get(v_entry_3335_, 2);
                lean_inc_ref(v_configFile_3339_);
                v_manifestFile_x3f_3340_ = lean_ctor_get(v_entry_3335_, 3);
                lean_inc(v_manifestFile_x3f_3340_);
                v_src_3341_ = lean_ctor_get(v_entry_3335_, 4);
                lean_inc_ref(v_src_3341_);
                lean_dec_ref(v_entry_3335_);
                v___x_3342_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6;
                v___x_3343_ = 1;
                v___x_3344_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_name_3336_,
                    v___x_3343_,
                );
                v___x_3345_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3345_, 0, v___x_3344_);
                v___x_3346_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3346_, 0, v___x_3342_);
                lean_ctor_set(v___x_3346_, 1, v___x_3345_);
                v___x_3347_ = l_Lake_PackageEntry_toJson___closed__0;
                v___x_3348_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3348_, 0, v_scope_3337_);
                v___x_3349_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3349_, 0, v___x_3347_);
                lean_ctor_set(v___x_3349_, 1, v___x_3348_);
                v___x_3350_ = l_Lake_PackageEntry_toJson___closed__1;
                v___x_3351_ = l_Lake_mkRelPathString(v_configFile_3339_);
                v___x_3352_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3352_, 0, v___x_3351_);
                v___x_3353_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3353_, 0, v___x_3350_);
                lean_ctor_set(v___x_3353_, 1, v___x_3352_);
                v___x_3354_ = l_Lake_PackageEntry_toJson___closed__2;
                v___x_3355_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_manifestFile_x3f_3340_);
                v___x_3356_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3356_, 0, v___x_3354_);
                lean_ctor_set(v___x_3356_, 1, v___x_3355_);
                v___x_3357_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10;
                v___x_3358_ = lean_alloc_ctor(1, 0, (1) as u32);
                lean_ctor_set_uint8(v___x_3358_, 0 as u32, v_inherited_3338_);
                v___x_3359_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3359_, 0, v___x_3357_);
                lean_ctor_set(v___x_3359_, 1, v___x_3358_);
                v___x_3360_ = lean_box(0);
                v___x_3361_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3361_, 0, v___x_3359_);
                lean_ctor_set(v___x_3361_, 1, v___x_3360_);
                v___x_3362_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3362_, 0, v___x_3356_);
                lean_ctor_set(v___x_3362_, 1, v___x_3361_);
                v___x_3363_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3363_, 0, v___x_3353_);
                lean_ctor_set(v___x_3363_, 1, v___x_3362_);
                v___x_3364_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3364_, 0, v___x_3349_);
                lean_ctor_set(v___x_3364_, 1, v___x_3363_);
                v_fields_3365_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v_fields_3365_, 0, v___x_3346_);
                lean_ctor_set(v_fields_3365_, 1, v___x_3364_);
                if lean_obj_tag(v_src_3341_) == 0 {
                    v_dir_3366_ = lean_ctor_get(v_src_3341_, 0);
                    v_isSharedCheck_3381_ = (!lean_is_exclusive(v_src_3341_)) as u8;
                    if v_isSharedCheck_3381_ == 0 {
                        v___x_3368_ = v_src_3341_;
                        v_isShared_3369_ = v_isSharedCheck_3381_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_dir_3366_);
                        lean_dec(v_src_3341_);
                        v___x_3368_ = lean_box(0);
                        v_isShared_3369_ = v_isSharedCheck_3381_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_url_3382_ = lean_ctor_get(v_src_3341_, 0);
                    lean_inc_ref(v_url_3382_);
                    v_rev_3383_ = lean_ctor_get(v_src_3341_, 1);
                    lean_inc_ref(v_rev_3383_);
                    v_inputRev_x3f_3384_ = lean_ctor_get(v_src_3341_, 2);
                    lean_inc(v_inputRev_x3f_3384_);
                    v_subDir_x3f_3385_ = lean_ctor_get(v_src_3341_, 3);
                    lean_inc(v_subDir_x3f_3385_);
                    lean_dec_ref_known(v_src_3341_, 4);
                    v___x_3386_ = l_Lake_PackageEntry_toJson___closed__7;
                    v___x_3387_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12;
                    v___x_3388_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_3388_, 0, v_url_3382_);
                    v___x_3389_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3389_, 0, v___x_3387_);
                    lean_ctor_set(v___x_3389_, 1, v___x_3388_);
                    v___x_3390_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14;
                    v___x_3391_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_3391_, 0, v_rev_3383_);
                    v___x_3392_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3392_, 0, v___x_3390_);
                    lean_ctor_set(v___x_3392_, 1, v___x_3391_);
                    v___x_3393_ = l_Lake_PackageEntry_toJson___closed__8;
                    v___x_3394_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__1(v_inputRev_x3f_3384_);
                    v___x_3395_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3395_, 0, v___x_3393_);
                    lean_ctor_set(v___x_3395_, 1, v___x_3394_);
                    v___x_3396_ = l_Lake_PackageEntry_toJson___closed__9;
                    v___x_3397_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_subDir_x3f_3385_);
                    v___x_3398_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3398_, 0, v___x_3396_);
                    lean_ctor_set(v___x_3398_, 1, v___x_3397_);
                    v___x_3399_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3399_, 0, v___x_3398_);
                    lean_ctor_set(v___x_3399_, 1, v___x_3360_);
                    v___x_3400_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3400_, 0, v___x_3395_);
                    lean_ctor_set(v___x_3400_, 1, v___x_3399_);
                    v___x_3401_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3401_, 0, v___x_3392_);
                    lean_ctor_set(v___x_3401_, 1, v___x_3400_);
                    v___x_3402_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3402_, 0, v___x_3389_);
                    lean_ctor_set(v___x_3402_, 1, v___x_3401_);
                    v___x_3403_ = l_List_appendTR___redArg(v_fields_3365_, v___x_3402_);
                    v___x_3404_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3404_, 0, v___x_3386_);
                    lean_ctor_set(v___x_3404_, 1, v___x_3403_);
                    v___x_3405_ = l_Lean_Json_mkObj(v___x_3404_);
                    lean_dec_ref_known(v___x_3404_, 2);
                    return v___x_3405_;
                }
            }
            1 => {
                v___x_3370_ = l_Lake_PackageEntry_toJson___closed__5;
                v___x_3371_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22;
                v___x_3372_ = l_Lake_mkRelPathString(v_dir_3366_);
                if v_isShared_3369_ == 0 {
                    lean_ctor_set_tag(v___x_3368_, 3);
                    lean_ctor_set(v___x_3368_, 0, v___x_3372_);
                    v___x_3374_ = v___x_3368_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3380_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3372_);
                    v___x_3374_ = v_reuseFailAlloc_3380_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3375_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3375_, 0, v___x_3371_);
                lean_ctor_set(v___x_3375_, 1, v___x_3374_);
                v___x_3376_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3376_, 0, v___x_3375_);
                lean_ctor_set(v___x_3376_, 1, v___x_3360_);
                v___x_3377_ = l_List_appendTR___redArg(v_fields_3365_, v___x_3376_);
                v___x_3378_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3378_, 0, v___x_3370_);
                lean_ctor_set(v___x_3378_, 1, v___x_3377_);
                v___x_3379_ = l_Lean_Json_mkObj(v___x_3378_);
                lean_dec_ref_known(v___x_3378_, 2);
                return v___x_3379_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_PackageEntry_fromJson_x3f___lam__0(
    mut v_x_3409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    v___x_3410_ = l_Lake_PackageEntry_fromJson_x3f___lam__0___closed__0;
    v___x_3411_ = lean_string_append(v___x_3410_, v_x_3409_);
    return v___x_3411_;
}
pub unsafe fn l_Lake_PackageEntry_fromJson_x3f___lam__0___boxed(
    mut v_x_3412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3413_: *mut LeanObject = core::ptr::null_mut();
    v_res_3413_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_x_3412_);
    lean_dec_ref(v_x_3412_);
    return v_res_3413_;
}
pub unsafe fn l_Lake_PackageEntry_fromJson_x3f(
    mut v_json_3434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3443_: u8 = 0;
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3448_: u8 = 0;
    let mut v_a_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3452_: u8 = 0;
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3456_: u8 = 0;
    let mut v_a_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3460_: u8 = 0;
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3467_: u8 = 0;
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3476_: u8 = 0;
    let mut v_a_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: u8 = 0;
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3492_: u8 = 0;
    let mut v___y_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3506_: u8 = 0;
    let mut v___y_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3516_: u8 = 0;
    let mut v___y_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3533_: u8 = 0;
    let mut v___y_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: u8 = 0;
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: u8 = 0;
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3585_: u8 = 0;
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3589_: u8 = 0;
    let mut v___y_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3593_: u8 = 0;
    let mut v___y_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3598_: u8 = 0;
    let mut v___y_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3613_: u8 = 0;
    let mut v___y_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: u8 = 0;
    let mut v_val_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: u8 = 0;
    let mut v_val_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: u8 = 0;
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3660_: u8 = 0;
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3666_: u8 = 0;
    let mut v_a_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3670_: u8 = 0;
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3674_: u8 = 0;
    let mut v_a_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3677_: u8 = 0;
    let mut v_isSharedCheck_3678_: u8 = 0;
    let mut v_isSharedCheck_3679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3439_ = l_Lean_Json_getObj_x3f(v_json_3434_);
                if lean_obj_tag(v___x_3439_) == 0 {
                    v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
                    v_isSharedCheck_3448_ = (!lean_is_exclusive(v___x_3439_)) as u8;
                    if v_isSharedCheck_3448_ == 0 {
                        v___x_3442_ = v___x_3439_;
                        v_isShared_3443_ = v_isSharedCheck_3448_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3440_);
                        lean_dec(v___x_3439_);
                        v___x_3442_ = lean_box(0);
                        v_isShared_3443_ = v_isSharedCheck_3448_;
                        state = 2;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_3439_) == 0 {
                        v_a_3449_ = lean_ctor_get(v___x_3439_, 0);
                        v_isSharedCheck_3456_ = (!lean_is_exclusive(v___x_3439_)) as u8;
                        if v_isSharedCheck_3456_ == 0 {
                            v___x_3451_ = v___x_3439_;
                            v_isShared_3452_ = v_isSharedCheck_3456_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3449_);
                            lean_dec(v___x_3439_);
                            v___x_3451_ = lean_box(0);
                            v_isShared_3452_ = v_isSharedCheck_3456_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_3457_ = lean_ctor_get(v___x_3439_, 0);
                        v_isSharedCheck_3679_ = (!lean_is_exclusive(v___x_3439_)) as u8;
                        if v_isSharedCheck_3679_ == 0 {
                            v___x_3459_ = v___x_3439_;
                            v_isShared_3460_ = v_isSharedCheck_3679_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3457_);
                            lean_dec(v___x_3439_);
                            v___x_3459_ = lean_box(0);
                            v_isShared_3460_ = v_isSharedCheck_3679_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3437_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_a_3436_);
                lean_dec_ref(v_a_3436_);
                v___x_3438_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3438_, 0, v___x_3437_);
                return v___x_3438_;
            }
            2 => {
                v___x_3444_ = l_Lake_PackageEntry_fromJson_x3f___lam__0(v_a_3440_);
                lean_dec(v_a_3440_);
                if v_isShared_3443_ == 0 {
                    lean_ctor_set(v___x_3442_, 0, v___x_3444_);
                    v___x_3446_ = v___x_3442_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3444_);
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
                    lean_ctor_set_tag(v___x_3451_, 0);
                    v___x_3454_ = v___x_3451_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
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
                if lean_obj_tag(v___x_3462_) == 0 {
                    lean_del_object(v___x_3459_);
                    lean_dec(v_a_3457_);
                    v___x_3463_ = l_Lake_PackageEntry_fromJson_x3f___closed__0;
                    v_a_3436_ = v___x_3463_;
                    state = 1;
                    continue;
                } else {
                    v_val_3464_ = lean_ctor_get(v___x_3462_, 0);
                    v_isSharedCheck_3678_ = (!lean_is_exclusive(v___x_3462_)) as u8;
                    if v_isSharedCheck_3678_ == 0 {
                        v___x_3466_ = v___x_3462_;
                        v_isShared_3467_ = v_isSharedCheck_3678_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_val_3464_);
                        lean_dec(v___x_3462_);
                        v___x_3466_ = lean_box(0);
                        v_isShared_3467_ = v_isSharedCheck_3678_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                v___x_3468_ = l_Lean_Name_fromJson_x3f(v_val_3464_);
                if lean_obj_tag(v___x_3468_) == 0 {
                    lean_del_object(v___x_3466_);
                    lean_del_object(v___x_3459_);
                    lean_dec(v_a_3457_);
                    v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
                    lean_inc(v_a_3469_);
                    lean_dec_ref_known(v___x_3468_, 1);
                    v___x_3470_ = l_Lake_PackageEntry_fromJson_x3f___closed__1;
                    v___x_3471_ = lean_string_append(v___x_3470_, v_a_3469_);
                    lean_dec(v_a_3469_);
                    v_a_3436_ = v___x_3471_;
                    state = 1;
                    continue;
                } else {
                    if lean_obj_tag(v___x_3468_) == 0 {
                        lean_del_object(v___x_3466_);
                        lean_del_object(v___x_3459_);
                        lean_dec(v_a_3457_);
                        v_a_3472_ = lean_ctor_get(v___x_3468_, 0);
                        lean_inc(v_a_3472_);
                        lean_dec_ref_known(v___x_3468_, 1);
                        v_a_3436_ = v_a_3472_;
                        state = 1;
                        continue;
                    } else {
                        v_a_3473_ = lean_ctor_get(v___x_3468_, 0);
                        v_isSharedCheck_3677_ = (!lean_is_exclusive(v___x_3468_)) as u8;
                        if v_isSharedCheck_3677_ == 0 {
                            v___x_3475_ = v___x_3468_;
                            v_isShared_3476_ = v_isSharedCheck_3677_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_3473_);
                            lean_dec(v___x_3468_);
                            v___x_3475_ = lean_box(0);
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
                if lean_obj_tag(v___x_3654_) == 0 {
                    state = 23;
                    continue;
                } else {
                    v_val_3655_ = lean_ctor_get(v___x_3654_, 0);
                    lean_inc(v_val_3655_);
                    lean_dec_ref_known(v___x_3654_, 1);
                    v___x_3656_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(v_val_3655_);
                    if lean_obj_tag(v___x_3656_) == 0 {
                        lean_del_object(v___x_3475_);
                        lean_dec(v_a_3473_);
                        lean_del_object(v___x_3466_);
                        lean_del_object(v___x_3459_);
                        lean_dec(v_a_3457_);
                        v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
                        v_isSharedCheck_3666_ = (!lean_is_exclusive(v___x_3656_)) as u8;
                        if v_isSharedCheck_3666_ == 0 {
                            v___x_3659_ = v___x_3656_;
                            v_isShared_3660_ = v_isSharedCheck_3666_;
                            state = 24;
                            continue;
                        } else {
                            lean_inc(v_a_3657_);
                            lean_dec(v___x_3656_);
                            v___x_3659_ = lean_box(0);
                            v_isShared_3660_ = v_isSharedCheck_3666_;
                            state = 24;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v___x_3656_) == 0 {
                            lean_del_object(v___x_3475_);
                            lean_dec(v_a_3473_);
                            lean_del_object(v___x_3466_);
                            lean_del_object(v___x_3459_);
                            lean_dec(v_a_3457_);
                            v_a_3667_ = lean_ctor_get(v___x_3656_, 0);
                            v_isSharedCheck_3674_ = (!lean_is_exclusive(v___x_3656_)) as u8;
                            if v_isSharedCheck_3674_ == 0 {
                                v___x_3669_ = v___x_3656_;
                                v_isShared_3670_ = v_isSharedCheck_3674_;
                                state = 26;
                                continue;
                            } else {
                                lean_inc(v_a_3667_);
                                lean_dec(v___x_3656_);
                                v___x_3669_ = lean_box(0);
                                v_isShared_3670_ = v_isSharedCheck_3674_;
                                state = 26;
                                continue;
                            }
                        } else {
                            v_a_3675_ = lean_ctor_get(v___x_3656_, 0);
                            lean_inc(v_a_3675_);
                            lean_dec_ref_known(v___x_3656_, 1);
                            if lean_obj_tag(v_a_3675_) == 0 {
                                state = 23;
                                continue;
                            } else {
                                v_val_3676_ = lean_ctor_get(v_a_3675_, 0);
                                lean_inc(v_val_3676_);
                                lean_dec_ref_known(v_a_3675_, 1);
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
                lean_dec_ref(v___x_3481_);
                v___x_3483_ = l_Lake_PackageEntry_fromJson_x3f___closed__3;
                v___x_3484_ = lean_string_append(v___x_3482_, v___x_3483_);
                v___x_3485_ = lean_string_append(v___x_3484_, v_a_3478_);
                lean_dec_ref(v_a_3478_);
                if v_isShared_3476_ == 0 {
                    lean_ctor_set_tag(v___x_3475_, 0);
                    lean_ctor_set(v___x_3475_, 0, v___x_3485_);
                    v___x_3487_ = v___x_3475_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3485_);
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
                    lean_ctor_set(v___x_3466_, 0, v___y_3493_);
                    v___x_3496_ = v___x_3466_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___y_3493_);
                    v___x_3496_ = v_reuseFailAlloc_3501_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_3497_ = lean_alloc_ctor(0, 5, (1) as u32);
                lean_ctor_set(v___x_3497_, 0, v_a_3473_);
                lean_ctor_set(v___x_3497_, 1, v___y_3491_);
                lean_ctor_set(v___x_3497_, 2, v___y_3490_);
                lean_ctor_set(v___x_3497_, 3, v___x_3496_);
                lean_ctor_set(v___x_3497_, 4, v_a_3494_);
                lean_ctor_set_uint8(
                    v___x_3497_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_3492_,
                );
                if v_isShared_3460_ == 0 {
                    lean_ctor_set(v___x_3459_, 0, v___x_3497_);
                    v___x_3499_ = v___x_3459_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3500_, 0, v___x_3497_);
                    v___x_3499_ = v_reuseFailAlloc_3500_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3499_;
            }
            14 => {
                v___x_3511_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_3511_, 0, v___y_3508_);
                lean_ctor_set(v___x_3511_, 1, v___y_3505_);
                lean_ctor_set(v___x_3511_, 2, v___y_3509_);
                lean_ctor_set(v___x_3511_, 3, v_a_3510_);
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
                lean_dec(v_a_3457_);
                if lean_obj_tag(v___x_3521_) == 0 {
                    lean_del_object(v___x_3475_);
                    v___x_3522_ = lean_box(0);
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
                    v_val_3523_ = lean_ctor_get(v___x_3521_, 0);
                    lean_inc(v_val_3523_);
                    lean_dec_ref_known(v___x_3521_, 1);
                    v___x_3524_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_3523_);
                    if lean_obj_tag(v___x_3524_) == 0 {
                        lean_dec(v_a_3519_);
                        lean_dec_ref(v___y_3518_);
                        lean_dec_ref(v___y_3517_);
                        lean_dec_ref(v___y_3515_);
                        lean_dec_ref(v___y_3514_);
                        lean_dec_ref(v___y_3513_);
                        lean_del_object(v___x_3466_);
                        lean_del_object(v___x_3459_);
                        v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
                        lean_inc(v_a_3525_);
                        lean_dec_ref_known(v___x_3524_, 1);
                        v___x_3526_ = l_Lake_PackageEntry_fromJson_x3f___closed__4;
                        v___x_3527_ = lean_string_append(v___x_3526_, v_a_3525_);
                        lean_dec(v_a_3525_);
                        v_a_3478_ = v___x_3527_;
                        state = 9;
                        continue;
                    } else {
                        if lean_obj_tag(v___x_3524_) == 0 {
                            lean_dec(v_a_3519_);
                            lean_dec_ref(v___y_3518_);
                            lean_dec_ref(v___y_3517_);
                            lean_dec_ref(v___y_3515_);
                            lean_dec_ref(v___y_3514_);
                            lean_dec_ref(v___y_3513_);
                            lean_del_object(v___x_3466_);
                            lean_del_object(v___x_3459_);
                            v_a_3528_ = lean_ctor_get(v___x_3524_, 0);
                            lean_inc(v_a_3528_);
                            lean_dec_ref_known(v___x_3524_, 1);
                            v_a_3478_ = v_a_3528_;
                            state = 9;
                            continue;
                        } else {
                            lean_del_object(v___x_3475_);
                            v_a_3529_ = lean_ctor_get(v___x_3524_, 0);
                            lean_inc(v_a_3529_);
                            lean_dec_ref_known(v___x_3524_, 1);
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
                        lean_dec_ref(v_a_3535_);
                        lean_dec_ref(v___y_3532_);
                        lean_dec_ref(v___y_3531_);
                        lean_del_object(v___x_3466_);
                        lean_del_object(v___x_3459_);
                        lean_dec(v_a_3457_);
                        v___x_3540_ = l_Lake_PackageEntry_fromJson_x3f___closed__5;
                        v___x_3541_ = lean_string_append(v___x_3540_, v___y_3534_);
                        lean_dec_ref(v___y_3534_);
                        v___x_3542_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2;
                        v___x_3543_ = lean_string_append(v___x_3541_, v___x_3542_);
                        v_a_3478_ = v___x_3543_;
                        state = 9;
                        continue;
                    } else {
                        lean_dec_ref(v___y_3534_);
                        v___x_3544_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__12;
                        v___x_3545_ = l_Lake_JsonObject_getJson_x3f(v_a_3457_, v___x_3544_);
                        if lean_obj_tag(v___x_3545_) == 0 {
                            lean_dec_ref(v_a_3535_);
                            lean_dec_ref(v___y_3532_);
                            lean_dec_ref(v___y_3531_);
                            lean_del_object(v___x_3466_);
                            lean_del_object(v___x_3459_);
                            lean_dec(v_a_3457_);
                            v___x_3546_ = l_Lake_PackageEntry_fromJson_x3f___closed__6;
                            v_a_3478_ = v___x_3546_;
                            state = 9;
                            continue;
                        } else {
                            v_val_3547_ = lean_ctor_get(v___x_3545_, 0);
                            lean_inc(v_val_3547_);
                            lean_dec_ref_known(v___x_3545_, 1);
                            v___x_3548_ = l_Lean_Json_getStr_x3f(v_val_3547_);
                            if lean_obj_tag(v___x_3548_) == 0 {
                                lean_dec_ref(v_a_3535_);
                                lean_dec_ref(v___y_3532_);
                                lean_dec_ref(v___y_3531_);
                                lean_del_object(v___x_3466_);
                                lean_del_object(v___x_3459_);
                                lean_dec(v_a_3457_);
                                v_a_3549_ = lean_ctor_get(v___x_3548_, 0);
                                lean_inc(v_a_3549_);
                                lean_dec_ref_known(v___x_3548_, 1);
                                v___x_3550_ = l_Lake_PackageEntry_fromJson_x3f___closed__7;
                                v___x_3551_ = lean_string_append(v___x_3550_, v_a_3549_);
                                lean_dec(v_a_3549_);
                                v_a_3478_ = v___x_3551_;
                                state = 9;
                                continue;
                            } else {
                                if lean_obj_tag(v___x_3548_) == 0 {
                                    lean_dec_ref(v_a_3535_);
                                    lean_dec_ref(v___y_3532_);
                                    lean_dec_ref(v___y_3531_);
                                    lean_del_object(v___x_3466_);
                                    lean_del_object(v___x_3459_);
                                    lean_dec(v_a_3457_);
                                    v_a_3552_ = lean_ctor_get(v___x_3548_, 0);
                                    lean_inc(v_a_3552_);
                                    lean_dec_ref_known(v___x_3548_, 1);
                                    v_a_3478_ = v_a_3552_;
                                    state = 9;
                                    continue;
                                } else {
                                    v_a_3553_ = lean_ctor_get(v___x_3548_, 0);
                                    lean_inc(v_a_3553_);
                                    lean_dec_ref_known(v___x_3548_, 1);
                                    v___x_3554_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__14;
                                    v___x_3555_ =
                                        l_Lake_JsonObject_getJson_x3f(v_a_3457_, v___x_3554_);
                                    if lean_obj_tag(v___x_3555_) == 0 {
                                        lean_dec(v_a_3553_);
                                        lean_dec_ref(v_a_3535_);
                                        lean_dec_ref(v___y_3532_);
                                        lean_dec_ref(v___y_3531_);
                                        lean_del_object(v___x_3466_);
                                        lean_del_object(v___x_3459_);
                                        lean_dec(v_a_3457_);
                                        v___x_3556_ = l_Lake_PackageEntry_fromJson_x3f___closed__8;
                                        v_a_3478_ = v___x_3556_;
                                        state = 9;
                                        continue;
                                    } else {
                                        v_val_3557_ = lean_ctor_get(v___x_3555_, 0);
                                        lean_inc(v_val_3557_);
                                        lean_dec_ref_known(v___x_3555_, 1);
                                        v___x_3558_ = l_Lean_Json_getStr_x3f(v_val_3557_);
                                        if lean_obj_tag(v___x_3558_) == 0 {
                                            lean_dec(v_a_3553_);
                                            lean_dec_ref(v_a_3535_);
                                            lean_dec_ref(v___y_3532_);
                                            lean_dec_ref(v___y_3531_);
                                            lean_del_object(v___x_3466_);
                                            lean_del_object(v___x_3459_);
                                            lean_dec(v_a_3457_);
                                            v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
                                            lean_inc(v_a_3559_);
                                            lean_dec_ref_known(v___x_3558_, 1);
                                            v___x_3560_ =
                                                l_Lake_PackageEntry_fromJson_x3f___closed__9;
                                            v___x_3561_ =
                                                lean_string_append(v___x_3560_, v_a_3559_);
                                            lean_dec(v_a_3559_);
                                            v_a_3478_ = v___x_3561_;
                                            state = 9;
                                            continue;
                                        } else {
                                            if lean_obj_tag(v___x_3558_) == 0 {
                                                lean_dec(v_a_3553_);
                                                lean_dec_ref(v_a_3535_);
                                                lean_dec_ref(v___y_3532_);
                                                lean_dec_ref(v___y_3531_);
                                                lean_del_object(v___x_3466_);
                                                lean_del_object(v___x_3459_);
                                                lean_dec(v_a_3457_);
                                                v_a_3562_ = lean_ctor_get(v___x_3558_, 0);
                                                lean_inc(v_a_3562_);
                                                lean_dec_ref_known(v___x_3558_, 1);
                                                v_a_3478_ = v_a_3562_;
                                                state = 9;
                                                continue;
                                            } else {
                                                v_a_3563_ = lean_ctor_get(v___x_3558_, 0);
                                                lean_inc(v_a_3563_);
                                                lean_dec_ref_known(v___x_3558_, 1);
                                                v___x_3564_ =
                                                    l_Lake_PackageEntry_toJson___closed__8;
                                                v___x_3565_ = l_Lake_JsonObject_getJson_x3f(
                                                    v_a_3457_,
                                                    v___x_3564_,
                                                );
                                                if lean_obj_tag(v___x_3565_) == 0 {
                                                    v___x_3566_ = lean_box(0);
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
                                                    v_val_3567_ = lean_ctor_get(v___x_3565_, 0);
                                                    lean_inc(v_val_3567_);
                                                    lean_dec_ref_known(v___x_3565_, 1);
                                                    v___x_3568_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__1(v_val_3567_);
                                                    if lean_obj_tag(v___x_3568_) == 0 {
                                                        lean_dec(v_a_3563_);
                                                        lean_dec(v_a_3553_);
                                                        lean_dec_ref(v_a_3535_);
                                                        lean_dec_ref(v___y_3532_);
                                                        lean_dec_ref(v___y_3531_);
                                                        lean_del_object(v___x_3466_);
                                                        lean_del_object(v___x_3459_);
                                                        lean_dec(v_a_3457_);
                                                        v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
                                                        lean_inc(v_a_3569_);
                                                        lean_dec_ref_known(v___x_3568_, 1);
                                                        v___x_3570_ = l_Lake_PackageEntry_fromJson_x3f___closed__10;
                                                        v___x_3571_ = lean_string_append(
                                                            v___x_3570_,
                                                            v_a_3569_,
                                                        );
                                                        lean_dec(v_a_3569_);
                                                        v_a_3478_ = v___x_3571_;
                                                        state = 9;
                                                        continue;
                                                    } else {
                                                        if lean_obj_tag(v___x_3568_) == 0 {
                                                            lean_dec(v_a_3563_);
                                                            lean_dec(v_a_3553_);
                                                            lean_dec_ref(v_a_3535_);
                                                            lean_dec_ref(v___y_3532_);
                                                            lean_dec_ref(v___y_3531_);
                                                            lean_del_object(v___x_3466_);
                                                            lean_del_object(v___x_3459_);
                                                            lean_dec(v_a_3457_);
                                                            v_a_3572_ =
                                                                lean_ctor_get(v___x_3568_, 0);
                                                            lean_inc(v_a_3572_);
                                                            lean_dec_ref_known(v___x_3568_, 1);
                                                            v_a_3478_ = v_a_3572_;
                                                            state = 9;
                                                            continue;
                                                        } else {
                                                            v_a_3573_ =
                                                                lean_ctor_get(v___x_3568_, 0);
                                                            lean_inc(v_a_3573_);
                                                            lean_dec_ref_known(v___x_3568_, 1);
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
                    lean_dec_ref(v___y_3534_);
                    v___x_3574_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__22;
                    v___x_3575_ = l_Lake_JsonObject_getJson_x3f(v_a_3457_, v___x_3574_);
                    lean_dec(v_a_3457_);
                    if lean_obj_tag(v___x_3575_) == 0 {
                        lean_dec_ref(v_a_3535_);
                        lean_dec_ref(v___y_3532_);
                        lean_dec_ref(v___y_3531_);
                        lean_del_object(v___x_3466_);
                        lean_del_object(v___x_3459_);
                        v___x_3576_ = l_Lake_PackageEntry_fromJson_x3f___closed__11;
                        v_a_3478_ = v___x_3576_;
                        state = 9;
                        continue;
                    } else {
                        v_val_3577_ = lean_ctor_get(v___x_3575_, 0);
                        lean_inc(v_val_3577_);
                        lean_dec_ref_known(v___x_3575_, 1);
                        v___x_3578_ = l_Lean_Json_getStr_x3f(v_val_3577_);
                        if lean_obj_tag(v___x_3578_) == 0 {
                            lean_dec_ref(v_a_3535_);
                            lean_dec_ref(v___y_3532_);
                            lean_dec_ref(v___y_3531_);
                            lean_del_object(v___x_3466_);
                            lean_del_object(v___x_3459_);
                            v_a_3579_ = lean_ctor_get(v___x_3578_, 0);
                            lean_inc(v_a_3579_);
                            lean_dec_ref_known(v___x_3578_, 1);
                            v___x_3580_ = l_Lake_PackageEntry_fromJson_x3f___closed__12;
                            v___x_3581_ = lean_string_append(v___x_3580_, v_a_3579_);
                            lean_dec(v_a_3579_);
                            v_a_3478_ = v___x_3581_;
                            state = 9;
                            continue;
                        } else {
                            lean_del_object(v___x_3475_);
                            v_a_3582_ = lean_ctor_get(v___x_3578_, 0);
                            v_isSharedCheck_3589_ = (!lean_is_exclusive(v___x_3578_)) as u8;
                            if v_isSharedCheck_3589_ == 0 {
                                v___x_3584_ = v___x_3578_;
                                v_isShared_3585_ = v_isSharedCheck_3589_;
                                state = 17;
                                continue;
                            } else {
                                lean_inc(v_a_3582_);
                                lean_dec(v___x_3578_);
                                v___x_3584_ = lean_box(0);
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
                    lean_ctor_set_tag(v___x_3584_, 0);
                    v___x_3587_ = v___x_3584_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3582_);
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
                if lean_obj_tag(v___x_3602_) == 0 {
                    v___y_3591_ = v_a_3600_;
                    v___y_3592_ = v___y_3597_;
                    v___y_3593_ = v___y_3598_;
                    v___y_3594_ = v___y_3599_;
                    state = 19;
                    continue;
                } else {
                    v_val_3603_ = lean_ctor_get(v___x_3602_, 0);
                    lean_inc(v_val_3603_);
                    lean_dec_ref_known(v___x_3602_, 1);
                    v___x_3604_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_3603_);
                    if lean_obj_tag(v___x_3604_) == 0 {
                        lean_dec_ref(v_a_3600_);
                        lean_dec_ref(v___y_3599_);
                        lean_dec_ref(v___y_3597_);
                        lean_del_object(v___x_3466_);
                        lean_del_object(v___x_3459_);
                        lean_dec(v_a_3457_);
                        v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
                        lean_inc(v_a_3605_);
                        lean_dec_ref_known(v___x_3604_, 1);
                        v___x_3606_ = l_Lake_PackageEntry_fromJson_x3f___closed__13;
                        v___x_3607_ = lean_string_append(v___x_3606_, v_a_3605_);
                        lean_dec(v_a_3605_);
                        v_a_3478_ = v___x_3607_;
                        state = 9;
                        continue;
                    } else {
                        if lean_obj_tag(v___x_3604_) == 0 {
                            lean_dec_ref(v_a_3600_);
                            lean_dec_ref(v___y_3599_);
                            lean_dec_ref(v___y_3597_);
                            lean_del_object(v___x_3466_);
                            lean_del_object(v___x_3459_);
                            lean_dec(v_a_3457_);
                            v_a_3608_ = lean_ctor_get(v___x_3604_, 0);
                            lean_inc(v_a_3608_);
                            lean_dec_ref_known(v___x_3604_, 1);
                            v_a_3478_ = v_a_3608_;
                            state = 9;
                            continue;
                        } else {
                            v_a_3609_ = lean_ctor_get(v___x_3604_, 0);
                            lean_inc(v_a_3609_);
                            lean_dec_ref_known(v___x_3604_, 1);
                            if lean_obj_tag(v_a_3609_) == 0 {
                                v___y_3591_ = v_a_3600_;
                                v___y_3592_ = v___y_3597_;
                                v___y_3593_ = v___y_3598_;
                                v___y_3594_ = v___y_3599_;
                                state = 19;
                                continue;
                            } else {
                                v_val_3610_ = lean_ctor_get(v_a_3609_, 0);
                                lean_inc(v_val_3610_);
                                lean_dec_ref_known(v_a_3609_, 1);
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
                if lean_obj_tag(v___x_3619_) == 0 {
                    lean_dec_ref(v_a_3617_);
                    lean_del_object(v___x_3466_);
                    lean_del_object(v___x_3459_);
                    lean_dec(v_a_3457_);
                    v___x_3620_ = l_Lake_PackageEntry_fromJson_x3f___closed__14;
                    v_a_3478_ = v___x_3620_;
                    state = 9;
                    continue;
                } else {
                    v_val_3621_ = lean_ctor_get(v___x_3619_, 0);
                    lean_inc(v_val_3621_);
                    lean_dec_ref_known(v___x_3619_, 1);
                    v___x_3622_ = l_Lean_Json_getStr_x3f(v_val_3621_);
                    if lean_obj_tag(v___x_3622_) == 0 {
                        lean_dec_ref(v_a_3617_);
                        lean_del_object(v___x_3466_);
                        lean_del_object(v___x_3459_);
                        lean_dec(v_a_3457_);
                        v_a_3623_ = lean_ctor_get(v___x_3622_, 0);
                        lean_inc(v_a_3623_);
                        lean_dec_ref_known(v___x_3622_, 1);
                        v___x_3624_ = l_Lake_PackageEntry_fromJson_x3f___closed__15;
                        v___x_3625_ = lean_string_append(v___x_3624_, v_a_3623_);
                        lean_dec(v_a_3623_);
                        v_a_3478_ = v___x_3625_;
                        state = 9;
                        continue;
                    } else {
                        if lean_obj_tag(v___x_3622_) == 0 {
                            lean_dec_ref(v_a_3617_);
                            lean_del_object(v___x_3466_);
                            lean_del_object(v___x_3459_);
                            lean_dec(v_a_3457_);
                            v_a_3626_ = lean_ctor_get(v___x_3622_, 0);
                            lean_inc(v_a_3626_);
                            lean_dec_ref_known(v___x_3622_, 1);
                            v_a_3478_ = v_a_3626_;
                            state = 9;
                            continue;
                        } else {
                            v_a_3627_ = lean_ctor_get(v___x_3622_, 0);
                            lean_inc(v_a_3627_);
                            lean_dec_ref_known(v___x_3622_, 1);
                            v___x_3628_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__10;
                            v___x_3629_ = l_Lake_JsonObject_getJson_x3f(v_a_3457_, v___x_3628_);
                            if lean_obj_tag(v___x_3629_) == 0 {
                                lean_dec(v_a_3627_);
                                lean_dec_ref(v_a_3617_);
                                lean_del_object(v___x_3466_);
                                lean_del_object(v___x_3459_);
                                lean_dec(v_a_3457_);
                                v___x_3630_ = l_Lake_PackageEntry_fromJson_x3f___closed__16;
                                v_a_3478_ = v___x_3630_;
                                state = 9;
                                continue;
                            } else {
                                v_val_3631_ = lean_ctor_get(v___x_3629_, 0);
                                lean_inc(v_val_3631_);
                                lean_dec_ref_known(v___x_3629_, 1);
                                v___x_3632_ = l_Lean_Json_getBool_x3f(v_val_3631_);
                                lean_dec(v_val_3631_);
                                if lean_obj_tag(v___x_3632_) == 0 {
                                    lean_dec(v_a_3627_);
                                    lean_dec_ref(v_a_3617_);
                                    lean_del_object(v___x_3466_);
                                    lean_del_object(v___x_3459_);
                                    lean_dec(v_a_3457_);
                                    v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
                                    lean_inc(v_a_3633_);
                                    lean_dec_ref_known(v___x_3632_, 1);
                                    v___x_3634_ = l_Lake_PackageEntry_fromJson_x3f___closed__17;
                                    v___x_3635_ = lean_string_append(v___x_3634_, v_a_3633_);
                                    lean_dec(v_a_3633_);
                                    v_a_3478_ = v___x_3635_;
                                    state = 9;
                                    continue;
                                } else {
                                    if lean_obj_tag(v___x_3632_) == 0 {
                                        lean_dec(v_a_3627_);
                                        lean_dec_ref(v_a_3617_);
                                        lean_del_object(v___x_3466_);
                                        lean_del_object(v___x_3459_);
                                        lean_dec(v_a_3457_);
                                        v_a_3636_ = lean_ctor_get(v___x_3632_, 0);
                                        lean_inc(v_a_3636_);
                                        lean_dec_ref_known(v___x_3632_, 1);
                                        v_a_3478_ = v_a_3636_;
                                        state = 9;
                                        continue;
                                    } else {
                                        v_a_3637_ = lean_ctor_get(v___x_3632_, 0);
                                        lean_inc(v_a_3637_);
                                        lean_dec_ref_known(v___x_3632_, 1);
                                        v___x_3638_ = l_Lake_PackageEntry_toJson___closed__1;
                                        v___x_3639_ =
                                            l_Lake_JsonObject_getJson_x3f(v_a_3457_, v___x_3638_);
                                        if lean_obj_tag(v___x_3639_) == 0 {
                                            v___x_3640_ = (lean_unbox(v_a_3637_) as u8);
                                            lean_dec(v_a_3637_);
                                            v___y_3612_ = v_a_3617_;
                                            v___y_3613_ = v___x_3640_;
                                            v___y_3614_ = v_a_3627_;
                                            state = 21;
                                            continue;
                                        } else {
                                            v_val_3641_ = lean_ctor_get(v___x_3639_, 0);
                                            lean_inc(v_val_3641_);
                                            lean_dec_ref_known(v___x_3639_, 1);
                                            v___x_3642_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_3641_);
                                            if lean_obj_tag(v___x_3642_) == 0 {
                                                lean_dec(v_a_3637_);
                                                lean_dec(v_a_3627_);
                                                lean_dec_ref(v_a_3617_);
                                                lean_del_object(v___x_3466_);
                                                lean_del_object(v___x_3459_);
                                                lean_dec(v_a_3457_);
                                                v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
                                                lean_inc(v_a_3643_);
                                                lean_dec_ref_known(v___x_3642_, 1);
                                                v___x_3644_ =
                                                    l_Lake_PackageEntry_fromJson_x3f___closed__18;
                                                v___x_3645_ =
                                                    lean_string_append(v___x_3644_, v_a_3643_);
                                                lean_dec(v_a_3643_);
                                                v_a_3478_ = v___x_3645_;
                                                state = 9;
                                                continue;
                                            } else {
                                                if lean_obj_tag(v___x_3642_) == 0 {
                                                    lean_dec(v_a_3637_);
                                                    lean_dec(v_a_3627_);
                                                    lean_dec_ref(v_a_3617_);
                                                    lean_del_object(v___x_3466_);
                                                    lean_del_object(v___x_3459_);
                                                    lean_dec(v_a_3457_);
                                                    v_a_3646_ = lean_ctor_get(v___x_3642_, 0);
                                                    lean_inc(v_a_3646_);
                                                    lean_dec_ref_known(v___x_3642_, 1);
                                                    v_a_3478_ = v_a_3646_;
                                                    state = 9;
                                                    continue;
                                                } else {
                                                    v_a_3647_ = lean_ctor_get(v___x_3642_, 0);
                                                    lean_inc(v_a_3647_);
                                                    lean_dec_ref_known(v___x_3642_, 1);
                                                    if lean_obj_tag(v_a_3647_) == 0 {
                                                        v___x_3648_ = (lean_unbox(v_a_3637_) as u8);
                                                        lean_dec(v_a_3637_);
                                                        v___y_3612_ = v_a_3617_;
                                                        v___y_3613_ = v___x_3648_;
                                                        v___y_3614_ = v_a_3627_;
                                                        state = 21;
                                                        continue;
                                                    } else {
                                                        v_val_3649_ = lean_ctor_get(v_a_3647_, 0);
                                                        lean_inc(v_val_3649_);
                                                        lean_dec_ref_known(v_a_3647_, 1);
                                                        v___x_3650_ = (lean_unbox(v_a_3637_) as u8);
                                                        lean_dec(v_a_3637_);
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
                lean_dec(v_a_3657_);
                if v_isShared_3660_ == 0 {
                    lean_ctor_set(v___x_3659_, 0, v___x_3662_);
                    v___x_3664_ = v___x_3659_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3662_);
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
                    lean_ctor_set_tag(v___x_3669_, 0);
                    v___x_3672_ = v___x_3669_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3667_);
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
    mut v_entry_3682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scope_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_configFile_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_manifestFile_x3f_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_src_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3690_: u8 = 0;
    let mut v___x_3691_: u8 = 0;
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3695_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_3683_ = lean_ctor_get(v_entry_3682_, 0);
                v_scope_3684_ = lean_ctor_get(v_entry_3682_, 1);
                v_configFile_3685_ = lean_ctor_get(v_entry_3682_, 2);
                v_manifestFile_x3f_3686_ = lean_ctor_get(v_entry_3682_, 3);
                v_src_3687_ = lean_ctor_get(v_entry_3682_, 4);
                v_isSharedCheck_3695_ = (!lean_is_exclusive(v_entry_3682_)) as u8;
                if v_isSharedCheck_3695_ == 0 {
                    v___x_3689_ = v_entry_3682_;
                    v_isShared_3690_ = v_isSharedCheck_3695_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_src_3687_);
                    lean_inc(v_manifestFile_x3f_3686_);
                    lean_inc(v_configFile_3685_);
                    lean_inc(v_scope_3684_);
                    lean_inc(v_name_3683_);
                    lean_dec(v_entry_3682_);
                    v___x_3689_ = lean_box(0);
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
                    v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 5, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_name_3683_);
                    lean_ctor_set(v_reuseFailAlloc_3694_, 1, v_scope_3684_);
                    lean_ctor_set(v_reuseFailAlloc_3694_, 2, v_configFile_3685_);
                    lean_ctor_set(v_reuseFailAlloc_3694_, 3, v_manifestFile_x3f_3686_);
                    lean_ctor_set(v_reuseFailAlloc_3694_, 4, v_src_3687_);
                    v___x_3693_ = v_reuseFailAlloc_3694_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_3693_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___x_3691_,
                );
                return v___x_3693_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_PackageEntry_setConfigFile(
    mut v_path_3696_: *mut LeanObject,
    mut v_entry_3697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scope_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inherited_3700_: u8 = 0;
    let mut v_manifestFile_x3f_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_src_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3705_: u8 = 0;
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3709_: u8 = 0;
    let mut v_unused_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_3698_ = lean_ctor_get(v_entry_3697_, 0);
                v_scope_3699_ = lean_ctor_get(v_entry_3697_, 1);
                v_inherited_3700_ = lean_ctor_get_uint8(
                    v_entry_3697_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                );
                v_manifestFile_x3f_3701_ = lean_ctor_get(v_entry_3697_, 3);
                v_src_3702_ = lean_ctor_get(v_entry_3697_, 4);
                v_isSharedCheck_3709_ = (!lean_is_exclusive(v_entry_3697_)) as u8;
                if v_isSharedCheck_3709_ == 0 {
                    v_unused_3710_ = lean_ctor_get(v_entry_3697_, 2);
                    lean_dec(v_unused_3710_);
                    v___x_3704_ = v_entry_3697_;
                    v_isShared_3705_ = v_isSharedCheck_3709_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_src_3702_);
                    lean_inc(v_manifestFile_x3f_3701_);
                    lean_inc(v_scope_3699_);
                    lean_inc(v_name_3698_);
                    lean_dec(v_entry_3697_);
                    v___x_3704_ = lean_box(0);
                    v_isShared_3705_ = v_isSharedCheck_3709_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3705_ == 0 {
                    lean_ctor_set(v___x_3704_, 2, v_path_3696_);
                    v___x_3707_ = v___x_3704_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 5, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_name_3698_);
                    lean_ctor_set(v_reuseFailAlloc_3708_, 1, v_scope_3699_);
                    lean_ctor_set(v_reuseFailAlloc_3708_, 2, v_path_3696_);
                    lean_ctor_set(v_reuseFailAlloc_3708_, 3, v_manifestFile_x3f_3701_);
                    lean_ctor_set(v_reuseFailAlloc_3708_, 4, v_src_3702_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3708_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
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
    mut v_path_x3f_3711_: *mut LeanObject,
    mut v_entry_3712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scope_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inherited_3715_: u8 = 0;
    let mut v_configFile_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_src_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3720_: u8 = 0;
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3724_: u8 = 0;
    let mut v_unused_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_3713_ = lean_ctor_get(v_entry_3712_, 0);
                v_scope_3714_ = lean_ctor_get(v_entry_3712_, 1);
                v_inherited_3715_ = lean_ctor_get_uint8(
                    v_entry_3712_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                );
                v_configFile_3716_ = lean_ctor_get(v_entry_3712_, 2);
                v_src_3717_ = lean_ctor_get(v_entry_3712_, 4);
                v_isSharedCheck_3724_ = (!lean_is_exclusive(v_entry_3712_)) as u8;
                if v_isSharedCheck_3724_ == 0 {
                    v_unused_3725_ = lean_ctor_get(v_entry_3712_, 3);
                    lean_dec(v_unused_3725_);
                    v___x_3719_ = v_entry_3712_;
                    v_isShared_3720_ = v_isSharedCheck_3724_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_src_3717_);
                    lean_inc(v_configFile_3716_);
                    lean_inc(v_scope_3714_);
                    lean_inc(v_name_3713_);
                    lean_dec(v_entry_3712_);
                    v___x_3719_ = lean_box(0);
                    v_isShared_3720_ = v_isSharedCheck_3724_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3720_ == 0 {
                    lean_ctor_set(v___x_3719_, 3, v_path_x3f_3711_);
                    v___x_3722_ = v___x_3719_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 5, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_name_3713_);
                    lean_ctor_set(v_reuseFailAlloc_3723_, 1, v_scope_3714_);
                    lean_ctor_set(v_reuseFailAlloc_3723_, 2, v_configFile_3716_);
                    lean_ctor_set(v_reuseFailAlloc_3723_, 3, v_path_x3f_3711_);
                    lean_ctor_set(v_reuseFailAlloc_3723_, 4, v_src_3717_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3723_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
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
    mut v_pkgDir_3726_: *mut LeanObject,
    mut v_entry_3727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_src_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scope_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inherited_3731_: u8 = 0;
    let mut v_configFile_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_manifestFile_x3f_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3736_: u8 = 0;
    let mut v_dir_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3740_: u8 = 0;
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3748_: u8 = 0;
    let mut v_isSharedCheck_3749_: u8 = 0;
    let mut v_unused_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_src_3728_ = lean_ctor_get(v_entry_3727_, 4);
                lean_inc_ref(v_src_3728_);
                if lean_obj_tag(v_src_3728_) == 0 {
                    v_name_3729_ = lean_ctor_get(v_entry_3727_, 0);
                    v_scope_3730_ = lean_ctor_get(v_entry_3727_, 1);
                    v_inherited_3731_ = lean_ctor_get_uint8(
                        v_entry_3727_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    );
                    v_configFile_3732_ = lean_ctor_get(v_entry_3727_, 2);
                    v_manifestFile_x3f_3733_ = lean_ctor_get(v_entry_3727_, 3);
                    v_isSharedCheck_3749_ = (!lean_is_exclusive(v_entry_3727_)) as u8;
                    if v_isSharedCheck_3749_ == 0 {
                        v_unused_3750_ = lean_ctor_get(v_entry_3727_, 4);
                        lean_dec(v_unused_3750_);
                        v___x_3735_ = v_entry_3727_;
                        v_isShared_3736_ = v_isSharedCheck_3749_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_manifestFile_x3f_3733_);
                        lean_inc(v_configFile_3732_);
                        lean_inc(v_scope_3730_);
                        lean_inc(v_name_3729_);
                        lean_dec(v_entry_3727_);
                        v___x_3735_ = lean_box(0);
                        v_isShared_3736_ = v_isSharedCheck_3749_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_src_3728_);
                    lean_dec_ref(v_pkgDir_3726_);
                    return v_entry_3727_;
                }
            }
            1 => {
                v_dir_3737_ = lean_ctor_get(v_src_3728_, 0);
                v_isSharedCheck_3748_ = (!lean_is_exclusive(v_src_3728_)) as u8;
                if v_isSharedCheck_3748_ == 0 {
                    v___x_3739_ = v_src_3728_;
                    v_isShared_3740_ = v_isSharedCheck_3748_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dir_3737_);
                    lean_dec(v_src_3728_);
                    v___x_3739_ = lean_box(0);
                    v_isShared_3740_ = v_isSharedCheck_3748_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3741_ = l_Lake_joinRelative(v_pkgDir_3726_, v_dir_3737_);
                if v_isShared_3740_ == 0 {
                    lean_ctor_set(v___x_3739_, 0, v___x_3741_);
                    v___x_3743_ = v___x_3739_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3741_);
                    v___x_3743_ = v_reuseFailAlloc_3747_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3736_ == 0 {
                    lean_ctor_set(v___x_3735_, 4, v___x_3743_);
                    v___x_3745_ = v___x_3735_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 5, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_name_3729_);
                    lean_ctor_set(v_reuseFailAlloc_3746_, 1, v_scope_3730_);
                    lean_ctor_set(v_reuseFailAlloc_3746_, 2, v_configFile_3732_);
                    lean_ctor_set(v_reuseFailAlloc_3746_, 3, v_manifestFile_x3f_3733_);
                    lean_ctor_set(v_reuseFailAlloc_3746_, 4, v___x_3743_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3746_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
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
    mut v_x_3751_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3751_) == 0 {
        let mut v_name_3752_: *mut LeanObject = core::ptr::null_mut();
        let mut v_inherited_3753_: u8 = 0;
        let mut v_dir_3754_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
        v_name_3752_ = lean_ctor_get(v_x_3751_, 0);
        v_inherited_3753_ = lean_ctor_get_uint8(
            v_x_3751_,
            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        );
        v_dir_3754_ = lean_ctor_get(v_x_3751_, 2);
        v___x_3755_ = l_Lake_Manifest_version___closed__1;
        v___x_3756_ = l_Lake_defaultConfigFile;
        v___x_3757_ = lean_box(0);
        lean_inc_ref(v_dir_3754_);
        v___x_3758_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3758_, 0, v_dir_3754_);
        lean_inc(v_name_3752_);
        v___x_3759_ = lean_alloc_ctor(0, 5, (1) as u32);
        lean_ctor_set(v___x_3759_, 0, v_name_3752_);
        lean_ctor_set(v___x_3759_, 1, v___x_3755_);
        lean_ctor_set(v___x_3759_, 2, v___x_3756_);
        lean_ctor_set(v___x_3759_, 3, v___x_3757_);
        lean_ctor_set(v___x_3759_, 4, v___x_3758_);
        lean_ctor_set_uint8(
            v___x_3759_,
            (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
            v_inherited_3753_,
        );
        return v___x_3759_;
    } else {
        let mut v_name_3760_: *mut LeanObject = core::ptr::null_mut();
        let mut v_inherited_3761_: u8 = 0;
        let mut v_url_3762_: *mut LeanObject = core::ptr::null_mut();
        let mut v_rev_3763_: *mut LeanObject = core::ptr::null_mut();
        let mut v_inputRev_x3f_3764_: *mut LeanObject = core::ptr::null_mut();
        let mut v_subDir_x3f_3765_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3767_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
        v_name_3760_ = lean_ctor_get(v_x_3751_, 0);
        v_inherited_3761_ = lean_ctor_get_uint8(
            v_x_3751_,
            (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
        );
        v_url_3762_ = lean_ctor_get(v_x_3751_, 2);
        v_rev_3763_ = lean_ctor_get(v_x_3751_, 3);
        v_inputRev_x3f_3764_ = lean_ctor_get(v_x_3751_, 4);
        v_subDir_x3f_3765_ = lean_ctor_get(v_x_3751_, 5);
        v___x_3766_ = l_Lake_Manifest_version___closed__1;
        v___x_3767_ = l_Lake_defaultConfigFile;
        v___x_3768_ = lean_box(0);
        lean_inc(v_subDir_x3f_3765_);
        lean_inc(v_inputRev_x3f_3764_);
        lean_inc_ref(v_rev_3763_);
        lean_inc_ref(v_url_3762_);
        v___x_3769_ = lean_alloc_ctor(1, 4, (0) as u32);
        lean_ctor_set(v___x_3769_, 0, v_url_3762_);
        lean_ctor_set(v___x_3769_, 1, v_rev_3763_);
        lean_ctor_set(v___x_3769_, 2, v_inputRev_x3f_3764_);
        lean_ctor_set(v___x_3769_, 3, v_subDir_x3f_3765_);
        lean_inc(v_name_3760_);
        v___x_3770_ = lean_alloc_ctor(0, 5, (1) as u32);
        lean_ctor_set(v___x_3770_, 0, v_name_3760_);
        lean_ctor_set(v___x_3770_, 1, v___x_3766_);
        lean_ctor_set(v___x_3770_, 2, v___x_3767_);
        lean_ctor_set(v___x_3770_, 3, v___x_3768_);
        lean_ctor_set(v___x_3770_, 4, v___x_3769_);
        lean_ctor_set_uint8(
            v___x_3770_,
            (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
            v_inherited_3761_,
        );
        return v___x_3770_;
    }
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6___boxed(
    mut v_x_3771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3772_: *mut LeanObject = core::ptr::null_mut();
    v_res_3772_ = l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(v_x_3771_);
    lean_dec_ref(v_x_3771_);
    return v_res_3772_;
}
pub unsafe fn l_Lake_Manifest_addPackage(
    mut v_entry_3773_: *mut LeanObject,
    mut v_self_3774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lakeDir_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fixedToolchain_3777_: u8 = 0;
    let mut v_packagesDir_x3f_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_packages_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3782_: u8 = 0;
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3787_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_3775_ = lean_ctor_get(v_self_3774_, 0);
                v_lakeDir_3776_ = lean_ctor_get(v_self_3774_, 1);
                v_fixedToolchain_3777_ = lean_ctor_get_uint8(
                    v_self_3774_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_packagesDir_x3f_3778_ = lean_ctor_get(v_self_3774_, 2);
                v_packages_3779_ = lean_ctor_get(v_self_3774_, 3);
                v_isSharedCheck_3787_ = (!lean_is_exclusive(v_self_3774_)) as u8;
                if v_isSharedCheck_3787_ == 0 {
                    v___x_3781_ = v_self_3774_;
                    v_isShared_3782_ = v_isSharedCheck_3787_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_packages_3779_);
                    lean_inc(v_packagesDir_x3f_3778_);
                    lean_inc(v_lakeDir_3776_);
                    lean_inc(v_name_3775_);
                    lean_dec(v_self_3774_);
                    v___x_3781_ = lean_box(0);
                    v_isShared_3782_ = v_isSharedCheck_3787_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3783_ = lean_array_push(v_packages_3779_, v_entry_3773_);
                if v_isShared_3782_ == 0 {
                    lean_ctor_set(v___x_3781_, 3, v___x_3783_);
                    v___x_3785_ = v___x_3781_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_name_3775_);
                    lean_ctor_set(v_reuseFailAlloc_3786_, 1, v_lakeDir_3776_);
                    lean_ctor_set(v_reuseFailAlloc_3786_, 2, v_packagesDir_x3f_3778_);
                    lean_ctor_set(v_reuseFailAlloc_3786_, 3, v___x_3783_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3786_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
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
    mut v_bs_3790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3791_: u8 = 0;
    let mut v_v_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: usize = 0;
    let mut v___x_3797_: usize = 0;
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3791_ = lean_usize_dec_lt(v_i_3789_, v_sz_3788_);
                if v___x_3791_ == 0 {
                    return v_bs_3790_;
                } else {
                    v_v_3792_ = lean_array_uget(v_bs_3790_, v_i_3789_);
                    v___x_3793_ = lean_unsigned_to_nat(0);
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
    mut v_sz_3800_: *mut LeanObject,
    mut v_i_3801_: *mut LeanObject,
    mut v_bs_3802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3803_: usize = 0;
    let mut v_i_boxed_3804_: usize = 0;
    let mut v_res_3805_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3803_ = lean_unbox_usize(v_sz_3800_);
    lean_dec(v_sz_3800_);
    v_i_boxed_3804_ = lean_unbox_usize(v_i_3801_);
    lean_dec(v_i_3801_);
    v_res_3805_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(v_sz_boxed_3803_, v_i_boxed_3804_, v_bs_3802_);
    return v_res_3805_;
}
pub unsafe fn l_Array_toJson___at___00Lake_Manifest_toJson_spec__0(
    mut v_a_3806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_3807_: usize = 0;
    let mut v___x_3808_: usize = 0;
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    v_sz_3807_ = lean_array_size(v_a_3806_);
    v___x_3808_ = 0usize;
    v___x_3809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_Manifest_toJson_spec__0_spec__0(v_sz_3807_, v___x_3808_, v_a_3806_);
    v___x_3810_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_3810_, 0, v___x_3809_);
    return v___x_3810_;
}
pub unsafe fn _init_l_Lake_Manifest_toJson___closed__1() -> *mut LeanObject {
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
    v___x_3812_ = l_Lake_Manifest_version___closed__2;
    v___x_3813_ = l_Lake_StdVer_toString(v___x_3812_);
    return v___x_3813_;
}
pub unsafe fn _init_l_Lake_Manifest_toJson___closed__2() -> *mut LeanObject {
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    v___x_3814_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Manifest_toJson___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Manifest_toJson___closed__1_once),
        _init_l_Lake_Manifest_toJson___closed__1,
    );
    v___x_3815_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_3815_, 0, v___x_3814_);
    return v___x_3815_;
}
pub unsafe fn _init_l_Lake_Manifest_toJson___closed__3() -> *mut LeanObject {
    let mut v___x_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    v___x_3816_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Manifest_toJson___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Manifest_toJson___closed__2_once),
        _init_l_Lake_Manifest_toJson___closed__2,
    );
    v___x_3817_ = l_Lake_Manifest_toJson___closed__0;
    v___x_3818_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3818_, 0, v___x_3817_);
    lean_ctor_set(v___x_3818_, 1, v___x_3816_);
    return v___x_3818_;
}
pub unsafe fn l_Lake_Manifest_toJson(mut v_self_3823_: *mut LeanObject) -> *mut LeanObject {
    let mut v_name_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lakeDir_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fixedToolchain_3826_: u8 = 0;
    let mut v_packagesDir_x3f_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_packages_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: u8 = 0;
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    v_name_3824_ = lean_ctor_get(v_self_3823_, 0);
    lean_inc(v_name_3824_);
    v_lakeDir_3825_ = lean_ctor_get(v_self_3823_, 1);
    lean_inc_ref(v_lakeDir_3825_);
    v_fixedToolchain_3826_ = lean_ctor_get_uint8(
        v_self_3823_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
    );
    v_packagesDir_x3f_3827_ = lean_ctor_get(v_self_3823_, 2);
    lean_inc(v_packagesDir_x3f_3827_);
    v_packages_3828_ = lean_ctor_get(v_self_3823_, 3);
    lean_inc_ref(v_packages_3828_);
    lean_dec_ref(v_self_3823_);
    v___x_3829_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Manifest_toJson___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Manifest_toJson___closed__3_once),
        _init_l_Lake_Manifest_toJson___closed__3,
    );
    v___x_3830_ = l_Lake_Manifest_toJson___closed__4;
    v___x_3831_ = lean_alloc_ctor(1, 0, (1) as u32);
    lean_ctor_set_uint8(v___x_3831_, 0 as u32, v_fixedToolchain_3826_);
    v___x_3832_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3832_, 0, v___x_3830_);
    lean_ctor_set(v___x_3832_, 1, v___x_3831_);
    v___x_3833_ =
        l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6;
    v___x_3834_ = 1;
    v___x_3835_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_name_3824_,
        v___x_3834_,
    );
    v___x_3836_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_3836_, 0, v___x_3835_);
    v___x_3837_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3837_, 0, v___x_3833_);
    lean_ctor_set(v___x_3837_, 1, v___x_3836_);
    v___x_3838_ = l_Lake_Manifest_toJson___closed__5;
    v___x_3839_ = l_Lake_mkRelPathString(v_lakeDir_3825_);
    v___x_3840_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_3840_, 0, v___x_3839_);
    v___x_3841_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3841_, 0, v___x_3838_);
    lean_ctor_set(v___x_3841_, 1, v___x_3840_);
    v___x_3842_ = l_Lake_Manifest_toJson___closed__6;
    v___x_3843_ = l_Option_toJson___at___00__private_Lake_Load_Manifest_0__Lake_instToJsonPackageEntryV6_toJson_spec__2(v_packagesDir_x3f_3827_);
    v___x_3844_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3844_, 0, v___x_3842_);
    lean_ctor_set(v___x_3844_, 1, v___x_3843_);
    v___x_3845_ = l_Lake_Manifest_toJson___closed__7;
    v___x_3846_ = l_Array_toJson___at___00Lake_Manifest_toJson_spec__0(v_packages_3828_);
    v___x_3847_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3847_, 0, v___x_3845_);
    lean_ctor_set(v___x_3847_, 1, v___x_3846_);
    v___x_3848_ = lean_box(0);
    v___x_3849_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3849_, 0, v___x_3847_);
    lean_ctor_set(v___x_3849_, 1, v___x_3848_);
    v___x_3850_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3850_, 0, v___x_3844_);
    lean_ctor_set(v___x_3850_, 1, v___x_3849_);
    v___x_3851_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3851_, 0, v___x_3841_);
    lean_ctor_set(v___x_3851_, 1, v___x_3850_);
    v___x_3852_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3852_, 0, v___x_3837_);
    lean_ctor_set(v___x_3852_, 1, v___x_3851_);
    v___x_3853_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3853_, 0, v___x_3832_);
    lean_ctor_set(v___x_3853_, 1, v___x_3852_);
    v___x_3854_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3854_, 0, v___x_3829_);
    lean_ctor_set(v___x_3854_, 1, v___x_3853_);
    v___x_3855_ = l_Lean_Json_mkObj(v___x_3854_);
    lean_dec_ref_known(v___x_3854_, 2);
    return v___x_3855_;
}
pub unsafe fn _init_l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6()
-> *mut LeanObject {
    let mut v_natZero_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_3867_: *mut LeanObject = core::ptr::null_mut();
    v_natZero_3866_ = lean_unsigned_to_nat(0);
    v_intZero_3867_ = lean_nat_to_int(v_natZero_3866_);
    return v_intZero_3867_;
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(
    mut v_obj_3872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ver_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_major_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: u8 = 0;
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: u8 = 0;
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ver_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mantissa_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exponent_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natZero_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_3915_: u8 = 0;
    let mut v___x_3916_: u8 = 0;
    let mut v_a_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3924_: u8 = 0;
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3928_: u8 = 0;
    let mut v_a_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSemVerCore_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_major_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3932_ = l_Lake_Manifest_toJson___closed__0;
                v___x_3933_ = l_Lake_JsonObject_getJson_x3f(v_obj_3872_, v___x_3932_);
                if lean_obj_tag(v___x_3933_) == 0 {
                    v___x_3934_ =
                        l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7;
                    v___x_3935_ = l_Lake_JsonObject_getJson_x3f(v_obj_3872_, v___x_3934_);
                    if lean_obj_tag(v___x_3935_) == 0 {
                        v___x_3936_ =
                            l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__9;
                        return v___x_3936_;
                    } else {
                        v_val_3937_ = lean_ctor_get(v___x_3935_, 0);
                        lean_inc(v_val_3937_);
                        lean_dec_ref_known(v___x_3935_, 1);
                        v_a_3909_ = v_val_3937_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_val_3938_ = lean_ctor_get(v___x_3933_, 0);
                    lean_inc(v_val_3938_);
                    lean_dec_ref_known(v___x_3933_, 1);
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
                lean_dec_ref(v___x_3876_);
                v___x_3878_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2;
                v___x_3879_ = lean_string_append(v___x_3877_, v___x_3878_);
                v___x_3880_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3880_, 0, v___x_3879_);
                return v___x_3880_;
            }
            2 => {
                v___x_3884_ = lean_unsigned_to_nat(1);
                v___x_3885_ = lean_nat_dec_lt(v___x_3884_, v_major_3883_);
                lean_dec(v_major_3883_);
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
                            v___x_3888_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_3888_, 0, v_ver_3882_);
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
                    lean_dec_ref(v___x_3890_);
                    v___x_3892_ =
                        l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__3;
                    v___x_3893_ = lean_string_append(v___x_3891_, v___x_3892_);
                    v___x_3894_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_Manifest_toJson___closed__1),
                        core::ptr::addr_of_mut!(l_Lake_Manifest_toJson___closed__1_once),
                        _init_l_Lake_Manifest_toJson___closed__1,
                    );
                    v___x_3895_ = lean_string_append(v___x_3893_, v___x_3894_);
                    v___x_3896_ =
                        l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4;
                    v___x_3897_ = lean_string_append(v___x_3895_, v___x_3896_);
                    v___x_3898_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3898_, 0, v___x_3897_);
                    return v___x_3898_;
                }
            }
            3 => {
                v___x_3901_ =
                    l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__5;
                v___x_3902_ = lean_unsigned_to_nat(80);
                v___x_3903_ = l_Lean_Json_pretty(v_ver_3900_, v___x_3902_);
                v___x_3904_ = lean_string_append(v___x_3901_, v___x_3903_);
                lean_dec_ref(v___x_3903_);
                v___x_3905_ =
                    l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__4;
                v___x_3906_ = lean_string_append(v___x_3904_, v___x_3905_);
                v___x_3907_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3907_, 0, v___x_3906_);
                return v___x_3907_;
            }
            4 => match lean_obj_tag(v_a_3909_) {
                2 => {
                    v_n_3910_ = lean_ctor_get(v_a_3909_, 0);
                    v_mantissa_3911_ = lean_ctor_get(v_n_3910_, 0);
                    v_exponent_3912_ = lean_ctor_get(v_n_3910_, 1);
                    v_natZero_3913_ = lean_unsigned_to_nat(0);
                    v_intZero_3914_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6_once), _init_l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__6);
                    v_isNeg_3915_ = lean_int_dec_lt(v_mantissa_3911_, v_intZero_3914_);
                    if v_isNeg_3915_ == 0 {
                        v___x_3916_ = lean_nat_dec_eq(v_exponent_3912_, v_natZero_3913_);
                        if v___x_3916_ == 0 {
                            v_ver_3900_ = v_a_3909_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_mantissa_3911_);
                            lean_dec_ref_known(v_a_3909_, 1);
                            v_a_3917_ = lean_nat_abs(v_mantissa_3911_);
                            lean_dec(v_mantissa_3911_);
                            v___x_3918_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v___x_3918_, 0, v_natZero_3913_);
                            lean_ctor_set(v___x_3918_, 1, v_a_3917_);
                            lean_ctor_set(v___x_3918_, 2, v_natZero_3913_);
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
                    v_s_3919_ = lean_ctor_get(v_a_3909_, 0);
                    lean_inc_ref(v_s_3919_);
                    lean_dec_ref_known(v_a_3909_, 1);
                    v___x_3920_ = l_Lake_StdVer_parse(v_s_3919_);
                    if lean_obj_tag(v___x_3920_) == 0 {
                        v_a_3921_ = lean_ctor_get(v___x_3920_, 0);
                        v_isSharedCheck_3928_ = (!lean_is_exclusive(v___x_3920_)) as u8;
                        if v_isSharedCheck_3928_ == 0 {
                            v___x_3923_ = v___x_3920_;
                            v_isShared_3924_ = v_isSharedCheck_3928_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3921_);
                            lean_dec(v___x_3920_);
                            v___x_3923_ = lean_box(0);
                            v_isShared_3924_ = v_isSharedCheck_3928_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_3929_ = lean_ctor_get(v___x_3920_, 0);
                        lean_inc(v_a_3929_);
                        lean_dec_ref_known(v___x_3920_, 1);
                        v_toSemVerCore_3930_ = lean_ctor_get(v_a_3929_, 0);
                        lean_inc_ref(v_toSemVerCore_3930_);
                        lean_dec(v_a_3929_);
                        v_major_3931_ = lean_ctor_get(v_toSemVerCore_3930_, 0);
                        lean_inc(v_major_3931_);
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
                    v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3921_);
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
    mut v_obj_3939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3940_: *mut LeanObject = core::ptr::null_mut();
    v_res_3940_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_obj_3939_);
    lean_dec(v_obj_3939_);
    return v_res_3940_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(
    mut v_sz_3941_: usize,
    mut v_i_3942_: usize,
    mut v_bs_3943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3944_: u8 = 0;
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3951_: u8 = 0;
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3955_: u8 = 0;
    let mut v_a_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: usize = 0;
    let mut v___x_3960_: usize = 0;
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3944_ = lean_usize_dec_lt(v_i_3942_, v_sz_3941_);
                if v___x_3944_ == 0 {
                    v___x_3945_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3945_, 0, v_bs_3943_);
                    return v___x_3945_;
                } else {
                    v_v_3946_ = lean_array_uget_borrowed(v_bs_3943_, v_i_3942_);
                    lean_inc(v_v_3946_);
                    v___x_3947_ = l_Lake_PackageEntry_fromJson_x3f(v_v_3946_);
                    if lean_obj_tag(v___x_3947_) == 0 {
                        lean_dec_ref(v_bs_3943_);
                        v_a_3948_ = lean_ctor_get(v___x_3947_, 0);
                        v_isSharedCheck_3955_ = (!lean_is_exclusive(v___x_3947_)) as u8;
                        if v_isSharedCheck_3955_ == 0 {
                            v___x_3950_ = v___x_3947_;
                            v_isShared_3951_ = v_isSharedCheck_3955_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3948_);
                            lean_dec(v___x_3947_);
                            v___x_3950_ = lean_box(0);
                            v_isShared_3951_ = v_isSharedCheck_3955_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3956_ = lean_ctor_get(v___x_3947_, 0);
                        lean_inc(v_a_3956_);
                        lean_dec_ref_known(v___x_3947_, 1);
                        v___x_3957_ = lean_unsigned_to_nat(0);
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
                    v_reuseFailAlloc_3954_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_a_3948_);
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
    mut v_sz_3963_: *mut LeanObject,
    mut v_i_3964_: *mut LeanObject,
    mut v_bs_3965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3966_: usize = 0;
    let mut v_i_boxed_3967_: usize = 0;
    let mut v_res_3968_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3966_ = lean_unbox_usize(v_sz_3963_);
    lean_dec(v_sz_3963_);
    v_i_boxed_3967_ = lean_unbox_usize(v_i_3964_);
    lean_dec(v_i_3964_);
    v_res_3968_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(v_sz_boxed_3966_, v_i_boxed_3967_, v_bs_3965_);
    return v_res_3968_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1(
    mut v_x_3970_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3970_) == 4 {
        let mut v_elems_3971_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_3972_: usize = 0;
        let mut v___x_3973_: usize = 0;
        let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
        v_elems_3971_ = lean_ctor_get(v_x_3970_, 0);
        lean_inc_ref(v_elems_3971_);
        lean_dec_ref_known(v_x_3970_, 1);
        v_sz_3972_ = lean_array_size(v_elems_3971_);
        v___x_3973_ = 0usize;
        v___x_3974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1_spec__2(v_sz_3972_, v___x_3973_, v_elems_3971_);
        return v___x_3974_;
    } else {
        let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3979_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
        v___x_3975_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1___closed__0;
        v___x_3976_ = lean_unsigned_to_nat(80);
        v___x_3977_ = l_Lean_Json_pretty(v_x_3970_, v___x_3976_);
        v___x_3978_ = lean_string_append(v___x_3975_, v___x_3977_);
        lean_dec_ref(v___x_3977_);
        v___x_3979_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2;
        v___x_3980_ = lean_string_append(v___x_3978_, v___x_3979_);
        v___x_3981_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3981_, 0, v___x_3980_);
        return v___x_3981_;
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1(
    mut v_x_3984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3990_: u8 = 0;
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3994_: u8 = 0;
    let mut v_a_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3998_: u8 = 0;
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4003_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3984_) == 0 {
                    v___x_3985_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1___closed__0;
                    return v___x_3985_;
                } else {
                    v___x_3986_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1(v_x_3984_);
                    if lean_obj_tag(v___x_3986_) == 0 {
                        v_a_3987_ = lean_ctor_get(v___x_3986_, 0);
                        v_isSharedCheck_3994_ = (!lean_is_exclusive(v___x_3986_)) as u8;
                        if v_isSharedCheck_3994_ == 0 {
                            v___x_3989_ = v___x_3986_;
                            v_isShared_3990_ = v_isSharedCheck_3994_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3987_);
                            lean_dec(v___x_3986_);
                            v___x_3989_ = lean_box(0);
                            v_isShared_3990_ = v_isSharedCheck_3994_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3995_ = lean_ctor_get(v___x_3986_, 0);
                        v_isSharedCheck_4003_ = (!lean_is_exclusive(v___x_3986_)) as u8;
                        if v_isSharedCheck_4003_ == 0 {
                            v___x_3997_ = v___x_3986_;
                            v_isShared_3998_ = v_isSharedCheck_4003_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3995_);
                            lean_dec(v___x_3986_);
                            v___x_3997_ = lean_box(0);
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
                    v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3987_);
                    v___x_3992_ = v_reuseFailAlloc_3993_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3992_;
            }
            3 => {
                v___x_3999_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3999_, 0, v_a_3995_);
                if v_isShared_3998_ == 0 {
                    lean_ctor_set(v___x_3997_, 0, v___x_3999_);
                    v___x_4001_ = v___x_3997_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___x_3999_);
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
    mut v_bs_4006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4007_: u8 = 0;
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4014_: u8 = 0;
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4018_: u8 = 0;
    let mut v_a_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: usize = 0;
    let mut v___x_4023_: usize = 0;
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4007_ = lean_usize_dec_lt(v_i_4005_, v_sz_4004_);
                if v___x_4007_ == 0 {
                    v___x_4008_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4008_, 0, v_bs_4006_);
                    return v___x_4008_;
                } else {
                    v_v_4009_ = lean_array_uget_borrowed(v_bs_4006_, v_i_4005_);
                    lean_inc(v_v_4009_);
                    v___x_4010_ =
                        l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson(
                            v_v_4009_,
                        );
                    if lean_obj_tag(v___x_4010_) == 0 {
                        lean_dec_ref(v_bs_4006_);
                        v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
                        v_isSharedCheck_4018_ = (!lean_is_exclusive(v___x_4010_)) as u8;
                        if v_isSharedCheck_4018_ == 0 {
                            v___x_4013_ = v___x_4010_;
                            v_isShared_4014_ = v_isSharedCheck_4018_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4011_);
                            lean_dec(v___x_4010_);
                            v___x_4013_ = lean_box(0);
                            v_isShared_4014_ = v_isSharedCheck_4018_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4019_ = lean_ctor_get(v___x_4010_, 0);
                        lean_inc(v_a_4019_);
                        lean_dec_ref_known(v___x_4010_, 1);
                        v___x_4020_ = lean_unsigned_to_nat(0);
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
                    v_reuseFailAlloc_4017_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_a_4011_);
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
    mut v_sz_4026_: *mut LeanObject,
    mut v_i_4027_: *mut LeanObject,
    mut v_bs_4028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4029_: usize = 0;
    let mut v_i_boxed_4030_: usize = 0;
    let mut v_res_4031_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4029_ = lean_unbox_usize(v_sz_4026_);
    lean_dec(v_sz_4026_);
    v_i_boxed_4030_ = lean_unbox_usize(v_i_4027_);
    lean_dec(v_i_4027_);
    v_res_4031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(v_sz_boxed_4029_, v_i_boxed_4030_, v_bs_4028_);
    return v_res_4031_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3(
    mut v_x_4032_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4032_) == 4 {
        let mut v_elems_4033_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_4034_: usize = 0;
        let mut v___x_4035_: usize = 0;
        let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
        v_elems_4033_ = lean_ctor_get(v_x_4032_, 0);
        lean_inc_ref(v_elems_4033_);
        lean_dec_ref_known(v_x_4032_, 1);
        v_sz_4034_ = lean_array_size(v_elems_4033_);
        v___x_4035_ = 0usize;
        v___x_4036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3_spec__5(v_sz_4034_, v___x_4035_, v_elems_4033_);
        return v___x_4036_;
    } else {
        let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4041_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
        v___x_4037_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1_spec__1___closed__0;
        v___x_4038_ = lean_unsigned_to_nat(80);
        v___x_4039_ = l_Lean_Json_pretty(v_x_4032_, v___x_4038_);
        v___x_4040_ = lean_string_append(v___x_4037_, v___x_4039_);
        lean_dec_ref(v___x_4039_);
        v___x_4041_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__0_spec__0___closed__2;
        v___x_4042_ = lean_string_append(v___x_4040_, v___x_4041_);
        v___x_4043_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4043_, 0, v___x_4042_);
        return v___x_4043_;
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2(
    mut v_x_4046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4052_: u8 = 0;
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4056_: u8 = 0;
    let mut v_a_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4060_: u8 = 0;
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4065_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4046_) == 0 {
                    v___x_4047_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2___closed__0;
                    return v___x_4047_;
                } else {
                    v___x_4048_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2_spec__3(v_x_4046_);
                    if lean_obj_tag(v___x_4048_) == 0 {
                        v_a_4049_ = lean_ctor_get(v___x_4048_, 0);
                        v_isSharedCheck_4056_ = (!lean_is_exclusive(v___x_4048_)) as u8;
                        if v_isSharedCheck_4056_ == 0 {
                            v___x_4051_ = v___x_4048_;
                            v_isShared_4052_ = v_isSharedCheck_4056_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4049_);
                            lean_dec(v___x_4048_);
                            v___x_4051_ = lean_box(0);
                            v_isShared_4052_ = v_isSharedCheck_4056_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4057_ = lean_ctor_get(v___x_4048_, 0);
                        v_isSharedCheck_4065_ = (!lean_is_exclusive(v___x_4048_)) as u8;
                        if v_isSharedCheck_4065_ == 0 {
                            v___x_4059_ = v___x_4048_;
                            v_isShared_4060_ = v_isSharedCheck_4065_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4057_);
                            lean_dec(v___x_4048_);
                            v___x_4059_ = lean_box(0);
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
                    v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
                    v___x_4054_ = v_reuseFailAlloc_4055_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4054_;
            }
            3 => {
                v___x_4061_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4061_, 0, v_a_4057_);
                if v_isShared_4060_ == 0 {
                    lean_ctor_set(v___x_4059_, 0, v___x_4061_);
                    v___x_4063_ = v___x_4059_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4061_);
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
    mut v_bs_4068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4069_: u8 = 0;
    let mut v_v_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: usize = 0;
    let mut v___x_4075_: usize = 0;
    let mut v___x_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4069_ = lean_usize_dec_lt(v_i_4067_, v_sz_4066_);
                if v___x_4069_ == 0 {
                    return v_bs_4068_;
                } else {
                    v_v_4070_ = lean_array_uget(v_bs_4068_, v_i_4067_);
                    v___x_4071_ = lean_unsigned_to_nat(0);
                    v_bs_x27_4072_ = lean_array_uset(v_bs_4068_, v_i_4067_, v___x_4071_);
                    v___x_4073_ =
                        l___private_Lake_Load_Manifest_0__Lake_PackageEntry_ofV6(v_v_4070_);
                    lean_dec(v_v_4070_);
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
    mut v_sz_4078_: *mut LeanObject,
    mut v_i_4079_: *mut LeanObject,
    mut v_bs_4080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4081_: usize = 0;
    let mut v_i_boxed_4082_: usize = 0;
    let mut v_res_4083_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4081_ = lean_unbox_usize(v_sz_4078_);
    lean_dec(v_sz_4078_);
    v_i_boxed_4082_ = lean_unbox_usize(v_i_4079_);
    lean_dec(v_i_4079_);
    v_res_4083_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__0(v_sz_boxed_4081_, v_i_boxed_4082_, v_bs_4080_);
    return v_res_4083_;
}
pub unsafe fn l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(
    mut v_ver_4097_: *mut LeanObject,
    mut v_obj_4098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4101_: usize = 0;
    let mut v___x_4102_: usize = 0;
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: u8 = 0;
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4118_: u8 = 0;
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4124_: u8 = 0;
    let mut v_a_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4128_: u8 = 0;
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4132_: u8 = 0;
    let mut v_a_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4142_: u8 = 0;
    let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4148_: u8 = 0;
    let mut v_a_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4152_: u8 = 0;
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4156_: u8 = 0;
    let mut v_a_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4160_: u8 = 0;
    let mut v_val_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4164_: *mut LeanObject = core::ptr::null_mut();
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
                    if lean_obj_tag(v___x_4112_) == 0 {
                        state = 2;
                        continue;
                    } else {
                        v_val_4113_ = lean_ctor_get(v___x_4112_, 0);
                        lean_inc(v_val_4113_);
                        lean_dec_ref_known(v___x_4112_, 1);
                        v___x_4114_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__2(v_val_4113_);
                        if lean_obj_tag(v___x_4114_) == 0 {
                            v_a_4115_ = lean_ctor_get(v___x_4114_, 0);
                            v_isSharedCheck_4124_ = (!lean_is_exclusive(v___x_4114_)) as u8;
                            if v_isSharedCheck_4124_ == 0 {
                                v___x_4117_ = v___x_4114_;
                                v_isShared_4118_ = v_isSharedCheck_4124_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_4115_);
                                lean_dec(v___x_4114_);
                                v___x_4117_ = lean_box(0);
                                v_isShared_4118_ = v_isSharedCheck_4124_;
                                state = 4;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_4114_) == 0 {
                                v_a_4125_ = lean_ctor_get(v___x_4114_, 0);
                                v_isSharedCheck_4132_ = (!lean_is_exclusive(v___x_4114_)) as u8;
                                if v_isSharedCheck_4132_ == 0 {
                                    v___x_4127_ = v___x_4114_;
                                    v_isShared_4128_ = v_isSharedCheck_4132_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_4125_);
                                    lean_dec(v___x_4114_);
                                    v___x_4127_ = lean_box(0);
                                    v_isShared_4128_ = v_isSharedCheck_4132_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                v_a_4133_ = lean_ctor_get(v___x_4114_, 0);
                                lean_inc(v_a_4133_);
                                lean_dec_ref_known(v___x_4114_, 1);
                                if lean_obj_tag(v_a_4133_) == 0 {
                                    state = 2;
                                    continue;
                                } else {
                                    v_val_4134_ = lean_ctor_get(v_a_4133_, 0);
                                    lean_inc(v_val_4134_);
                                    lean_dec_ref_known(v_a_4133_, 1);
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
                    if lean_obj_tag(v___x_4136_) == 0 {
                        state = 3;
                        continue;
                    } else {
                        v_val_4137_ = lean_ctor_get(v___x_4136_, 0);
                        lean_inc(v_val_4137_);
                        lean_dec_ref_known(v___x_4136_, 1);
                        v___x_4138_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_Manifest_getPackages_spec__1(v_val_4137_);
                        if lean_obj_tag(v___x_4138_) == 0 {
                            v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
                            v_isSharedCheck_4148_ = (!lean_is_exclusive(v___x_4138_)) as u8;
                            if v_isSharedCheck_4148_ == 0 {
                                v___x_4141_ = v___x_4138_;
                                v_isShared_4142_ = v_isSharedCheck_4148_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_4139_);
                                lean_dec(v___x_4138_);
                                v___x_4141_ = lean_box(0);
                                v_isShared_4142_ = v_isSharedCheck_4148_;
                                state = 8;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_4138_) == 0 {
                                v_a_4149_ = lean_ctor_get(v___x_4138_, 0);
                                v_isSharedCheck_4156_ = (!lean_is_exclusive(v___x_4138_)) as u8;
                                if v_isSharedCheck_4156_ == 0 {
                                    v___x_4151_ = v___x_4138_;
                                    v_isShared_4152_ = v_isSharedCheck_4156_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_inc(v_a_4149_);
                                    lean_dec(v___x_4138_);
                                    v___x_4151_ = lean_box(0);
                                    v_isShared_4152_ = v_isSharedCheck_4156_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                v_a_4157_ = lean_ctor_get(v___x_4138_, 0);
                                v_isSharedCheck_4165_ = (!lean_is_exclusive(v___x_4138_)) as u8;
                                if v_isSharedCheck_4165_ == 0 {
                                    v___x_4159_ = v___x_4138_;
                                    v_isShared_4160_ = v_isSharedCheck_4165_;
                                    state = 12;
                                    continue;
                                } else {
                                    lean_inc(v_a_4157_);
                                    lean_dec(v___x_4138_);
                                    v___x_4159_ = lean_box(0);
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
                v___x_4104_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4104_, 0, v___x_4103_);
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
                lean_dec(v_a_4115_);
                if v_isShared_4118_ == 0 {
                    lean_ctor_set(v___x_4117_, 0, v___x_4120_);
                    v___x_4122_ = v___x_4117_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4123_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4123_, 0, v___x_4120_);
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
                    lean_ctor_set_tag(v___x_4127_, 0);
                    v___x_4130_ = v___x_4127_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_a_4125_);
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
                lean_dec(v_a_4139_);
                if v_isShared_4142_ == 0 {
                    lean_ctor_set(v___x_4141_, 0, v___x_4144_);
                    v___x_4146_ = v___x_4141_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4147_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4147_, 0, v___x_4144_);
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
                    lean_ctor_set_tag(v___x_4151_, 0);
                    v___x_4154_ = v___x_4151_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4155_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
                    v___x_4154_ = v_reuseFailAlloc_4155_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4154_;
            }
            12 => {
                if lean_obj_tag(v_a_4157_) == 0 {
                    lean_del_object(v___x_4159_);
                    state = 3;
                    continue;
                } else {
                    v_val_4161_ = lean_ctor_get(v_a_4157_, 0);
                    lean_inc(v_val_4161_);
                    lean_dec_ref_known(v_a_4157_, 1);
                    if v_isShared_4160_ == 0 {
                        lean_ctor_set(v___x_4159_, 0, v_val_4161_);
                        v___x_4163_ = v___x_4159_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_val_4161_);
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
    mut v_ver_4166_: *mut LeanObject,
    mut v_obj_4167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4168_: *mut LeanObject = core::ptr::null_mut();
    v_res_4168_ =
        l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(v_ver_4166_, v_obj_4167_);
    lean_dec(v_obj_4167_);
    lean_dec_ref(v_ver_4166_);
    return v_res_4168_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0(
    mut v_x_4171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4177_: u8 = 0;
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4181_: u8 = 0;
    let mut v_a_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4185_: u8 = 0;
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4190_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4171_) == 0 {
                    v___x_4172_ = l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0___closed__0;
                    return v___x_4172_;
                } else {
                    v___x_4173_ = l_Lean_Name_fromJson_x3f(v_x_4171_);
                    if lean_obj_tag(v___x_4173_) == 0 {
                        v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
                        v_isSharedCheck_4181_ = (!lean_is_exclusive(v___x_4173_)) as u8;
                        if v_isSharedCheck_4181_ == 0 {
                            v___x_4176_ = v___x_4173_;
                            v_isShared_4177_ = v_isSharedCheck_4181_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4174_);
                            lean_dec(v___x_4173_);
                            v___x_4176_ = lean_box(0);
                            v_isShared_4177_ = v_isSharedCheck_4181_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4182_ = lean_ctor_get(v___x_4173_, 0);
                        v_isSharedCheck_4190_ = (!lean_is_exclusive(v___x_4173_)) as u8;
                        if v_isSharedCheck_4190_ == 0 {
                            v___x_4184_ = v___x_4173_;
                            v_isShared_4185_ = v_isSharedCheck_4190_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4182_);
                            lean_dec(v___x_4173_);
                            v___x_4184_ = lean_box(0);
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
                    v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_a_4174_);
                    v___x_4179_ = v_reuseFailAlloc_4180_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4179_;
            }
            3 => {
                v___x_4186_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4186_, 0, v_a_4182_);
                if v_isShared_4185_ == 0 {
                    lean_ctor_set(v___x_4184_, 0, v___x_4186_);
                    v___x_4188_ = v___x_4184_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4189_, 0, v___x_4186_);
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
    mut v_x_4193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4199_: u8 = 0;
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4203_: u8 = 0;
    let mut v_a_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4207_: u8 = 0;
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4212_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4193_) == 0 {
                    v___x_4194_ = l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1___closed__0;
                    return v___x_4194_;
                } else {
                    v___x_4195_ = l_Lean_Json_getBool_x3f(v_x_4193_);
                    if lean_obj_tag(v___x_4195_) == 0 {
                        v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
                        v_isSharedCheck_4203_ = (!lean_is_exclusive(v___x_4195_)) as u8;
                        if v_isSharedCheck_4203_ == 0 {
                            v___x_4198_ = v___x_4195_;
                            v_isShared_4199_ = v_isSharedCheck_4203_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4196_);
                            lean_dec(v___x_4195_);
                            v___x_4198_ = lean_box(0);
                            v_isShared_4199_ = v_isSharedCheck_4203_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4204_ = lean_ctor_get(v___x_4195_, 0);
                        v_isSharedCheck_4212_ = (!lean_is_exclusive(v___x_4195_)) as u8;
                        if v_isSharedCheck_4212_ == 0 {
                            v___x_4206_ = v___x_4195_;
                            v_isShared_4207_ = v_isSharedCheck_4212_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4204_);
                            lean_dec(v___x_4195_);
                            v___x_4206_ = lean_box(0);
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
                    v_reuseFailAlloc_4202_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_a_4196_);
                    v___x_4201_ = v_reuseFailAlloc_4202_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4201_;
            }
            3 => {
                v___x_4208_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4208_, 0, v_a_4204_);
                if v_isShared_4207_ == 0 {
                    lean_ctor_set(v___x_4206_, 0, v___x_4208_);
                    v___x_4210_ = v___x_4206_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4211_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4211_, 0, v___x_4208_);
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
    mut v_x_4213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4214_: *mut LeanObject = core::ptr::null_mut();
    v_res_4214_ = l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1(v_x_4213_);
    lean_dec(v_x_4213_);
    return v_res_4214_;
}
pub unsafe fn l_Lake_Manifest_fromJson_x3f(mut v_json_4218_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4223_: u8 = 0;
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4227_: u8 = 0;
    let mut v_a_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4233_: u8 = 0;
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4237_: u8 = 0;
    let mut v_a_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4240_: u8 = 0;
    let mut v___y_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4250_: u8 = 0;
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4254_: u8 = 0;
    let mut v_a_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4258_: u8 = 0;
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4263_: u8 = 0;
    let mut v___y_4265_: u8 = 0;
    let mut v___y_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4276_: u8 = 0;
    let mut v___x_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4282_: u8 = 0;
    let mut v_a_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4286_: u8 = 0;
    let mut v___x_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4290_: u8 = 0;
    let mut v_a_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4293_: u8 = 0;
    let mut v___y_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4297_: u8 = 0;
    let mut v_a_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4306_: u8 = 0;
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4312_: u8 = 0;
    let mut v_a_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4316_: u8 = 0;
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4320_: u8 = 0;
    let mut v_a_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4324_: u8 = 0;
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4327_: u8 = 0;
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4335_: u8 = 0;
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4341_: u8 = 0;
    let mut v_a_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4345_: u8 = 0;
    let mut v___x_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4349_: u8 = 0;
    let mut v_a_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: u8 = 0;
    let mut v___x_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4361_: u8 = 0;
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4367_: u8 = 0;
    let mut v_a_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4371_: u8 = 0;
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4375_: u8 = 0;
    let mut v_a_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4219_ = l_Lean_Json_getObj_x3f(v_json_4218_);
                if lean_obj_tag(v___x_4219_) == 0 {
                    v_a_4220_ = lean_ctor_get(v___x_4219_, 0);
                    v_isSharedCheck_4227_ = (!lean_is_exclusive(v___x_4219_)) as u8;
                    if v_isSharedCheck_4227_ == 0 {
                        v___x_4222_ = v___x_4219_;
                        v_isShared_4223_ = v_isSharedCheck_4227_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4220_);
                        lean_dec(v___x_4219_);
                        v___x_4222_ = lean_box(0);
                        v_isShared_4223_ = v_isSharedCheck_4227_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4228_ = lean_ctor_get(v___x_4219_, 0);
                    lean_inc(v_a_4228_);
                    lean_dec_ref_known(v___x_4219_, 1);
                    v___x_4229_ =
                        l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_a_4228_);
                    if lean_obj_tag(v___x_4229_) == 0 {
                        lean_dec(v_a_4228_);
                        v_a_4230_ = lean_ctor_get(v___x_4229_, 0);
                        v_isSharedCheck_4237_ = (!lean_is_exclusive(v___x_4229_)) as u8;
                        if v_isSharedCheck_4237_ == 0 {
                            v___x_4232_ = v___x_4229_;
                            v_isShared_4233_ = v_isSharedCheck_4237_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4230_);
                            lean_dec(v___x_4229_);
                            v___x_4232_ = lean_box(0);
                            v_isShared_4233_ = v_isSharedCheck_4237_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4238_ = lean_ctor_get(v___x_4229_, 0);
                        lean_inc(v_a_4238_);
                        lean_dec_ref_known(v___x_4229_, 1);
                        v___x_4354_ = l_Lake_Manifest_toJson___closed__4;
                        v___x_4355_ = l_Lake_JsonObject_getJson_x3f(v_a_4228_, v___x_4354_);
                        if lean_obj_tag(v___x_4355_) == 0 {
                            state = 27;
                            continue;
                        } else {
                            v_val_4356_ = lean_ctor_get(v___x_4355_, 0);
                            lean_inc(v_val_4356_);
                            lean_dec_ref_known(v___x_4355_, 1);
                            v___x_4357_ =
                                l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__1(
                                    v_val_4356_,
                                );
                            lean_dec(v_val_4356_);
                            if lean_obj_tag(v___x_4357_) == 0 {
                                lean_dec(v_a_4238_);
                                lean_dec(v_a_4228_);
                                v_a_4358_ = lean_ctor_get(v___x_4357_, 0);
                                v_isSharedCheck_4367_ = (!lean_is_exclusive(v___x_4357_)) as u8;
                                if v_isSharedCheck_4367_ == 0 {
                                    v___x_4360_ = v___x_4357_;
                                    v_isShared_4361_ = v_isSharedCheck_4367_;
                                    state = 28;
                                    continue;
                                } else {
                                    lean_inc(v_a_4358_);
                                    lean_dec(v___x_4357_);
                                    v___x_4360_ = lean_box(0);
                                    v_isShared_4361_ = v_isSharedCheck_4367_;
                                    state = 28;
                                    continue;
                                }
                            } else {
                                if lean_obj_tag(v___x_4357_) == 0 {
                                    lean_dec(v_a_4238_);
                                    lean_dec(v_a_4228_);
                                    v_a_4368_ = lean_ctor_get(v___x_4357_, 0);
                                    v_isSharedCheck_4375_ = (!lean_is_exclusive(v___x_4357_)) as u8;
                                    if v_isSharedCheck_4375_ == 0 {
                                        v___x_4370_ = v___x_4357_;
                                        v_isShared_4371_ = v_isSharedCheck_4375_;
                                        state = 30;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4368_);
                                        lean_dec(v___x_4357_);
                                        v___x_4370_ = lean_box(0);
                                        v_isShared_4371_ = v_isSharedCheck_4375_;
                                        state = 30;
                                        continue;
                                    }
                                } else {
                                    v_a_4376_ = lean_ctor_get(v___x_4357_, 0);
                                    lean_inc(v_a_4376_);
                                    lean_dec_ref_known(v___x_4357_, 1);
                                    if lean_obj_tag(v_a_4376_) == 0 {
                                        state = 27;
                                        continue;
                                    } else {
                                        v_val_4377_ = lean_ctor_get(v_a_4376_, 0);
                                        lean_inc(v_val_4377_);
                                        lean_dec_ref_known(v_a_4376_, 1);
                                        v___x_4378_ = (lean_unbox(v_val_4377_) as u8);
                                        lean_dec(v_val_4377_);
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
                    v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_a_4220_);
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
                    v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4230_);
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
                v___x_4245_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4245_, 0, v_a_4238_);
                lean_ctor_set(v___x_4245_, 1, v___x_4244_);
                v___x_4246_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(
                    v___x_4245_,
                    v_a_4228_,
                );
                lean_dec(v_a_4228_);
                lean_dec_ref_known(v___x_4245_, 2);
                if lean_obj_tag(v___x_4246_) == 0 {
                    lean_dec(v_a_4243_);
                    lean_dec(v___y_4242_);
                    lean_dec_ref(v___y_4241_);
                    v_a_4247_ = lean_ctor_get(v___x_4246_, 0);
                    v_isSharedCheck_4254_ = (!lean_is_exclusive(v___x_4246_)) as u8;
                    if v_isSharedCheck_4254_ == 0 {
                        v___x_4249_ = v___x_4246_;
                        v_isShared_4250_ = v_isSharedCheck_4254_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4247_);
                        lean_dec(v___x_4246_);
                        v___x_4249_ = lean_box(0);
                        v_isShared_4250_ = v_isSharedCheck_4254_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_a_4255_ = lean_ctor_get(v___x_4246_, 0);
                    v_isSharedCheck_4263_ = (!lean_is_exclusive(v___x_4246_)) as u8;
                    if v_isSharedCheck_4263_ == 0 {
                        v___x_4257_ = v___x_4246_;
                        v_isShared_4258_ = v_isSharedCheck_4263_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_4255_);
                        lean_dec(v___x_4246_);
                        v___x_4257_ = lean_box(0);
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
                    v_reuseFailAlloc_4253_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_a_4247_);
                    v___x_4252_ = v_reuseFailAlloc_4253_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4252_;
            }
            8 => {
                v___x_4259_ = lean_alloc_ctor(0, 4, (1) as u32);
                lean_ctor_set(v___x_4259_, 0, v___y_4242_);
                lean_ctor_set(v___x_4259_, 1, v___y_4241_);
                lean_ctor_set(v___x_4259_, 2, v_a_4243_);
                lean_ctor_set(v___x_4259_, 3, v_a_4255_);
                lean_ctor_set_uint8(
                    v___x_4259_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v___y_4240_,
                );
                if v_isShared_4258_ == 0 {
                    lean_ctor_set(v___x_4257_, 0, v___x_4259_);
                    v___x_4261_ = v___x_4257_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4262_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4262_, 0, v___x_4259_);
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
                if lean_obj_tag(v___x_4269_) == 0 {
                    v___x_4270_ = lean_box(0);
                    v___y_4240_ = v___y_4265_;
                    v___y_4241_ = v_a_4267_;
                    v___y_4242_ = v___y_4266_;
                    v_a_4243_ = v___x_4270_;
                    state = 5;
                    continue;
                } else {
                    v_val_4271_ = lean_ctor_get(v___x_4269_, 0);
                    lean_inc(v_val_4271_);
                    lean_dec_ref_known(v___x_4269_, 1);
                    v___x_4272_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_4271_);
                    if lean_obj_tag(v___x_4272_) == 0 {
                        lean_dec_ref(v_a_4267_);
                        lean_dec(v___y_4266_);
                        lean_dec(v_a_4238_);
                        lean_dec(v_a_4228_);
                        v_a_4273_ = lean_ctor_get(v___x_4272_, 0);
                        v_isSharedCheck_4282_ = (!lean_is_exclusive(v___x_4272_)) as u8;
                        if v_isSharedCheck_4282_ == 0 {
                            v___x_4275_ = v___x_4272_;
                            v_isShared_4276_ = v_isSharedCheck_4282_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_4273_);
                            lean_dec(v___x_4272_);
                            v___x_4275_ = lean_box(0);
                            v_isShared_4276_ = v_isSharedCheck_4282_;
                            state = 11;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v___x_4272_) == 0 {
                            lean_dec_ref(v_a_4267_);
                            lean_dec(v___y_4266_);
                            lean_dec(v_a_4238_);
                            lean_dec(v_a_4228_);
                            v_a_4283_ = lean_ctor_get(v___x_4272_, 0);
                            v_isSharedCheck_4290_ = (!lean_is_exclusive(v___x_4272_)) as u8;
                            if v_isSharedCheck_4290_ == 0 {
                                v___x_4285_ = v___x_4272_;
                                v_isShared_4286_ = v_isSharedCheck_4290_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_4283_);
                                lean_dec(v___x_4272_);
                                v___x_4285_ = lean_box(0);
                                v_isShared_4286_ = v_isSharedCheck_4290_;
                                state = 13;
                                continue;
                            }
                        } else {
                            v_a_4291_ = lean_ctor_get(v___x_4272_, 0);
                            lean_inc(v_a_4291_);
                            lean_dec_ref_known(v___x_4272_, 1);
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
                lean_dec(v_a_4273_);
                if v_isShared_4276_ == 0 {
                    lean_ctor_set(v___x_4275_, 0, v___x_4278_);
                    v___x_4280_ = v___x_4275_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4281_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4281_, 0, v___x_4278_);
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
                    lean_ctor_set_tag(v___x_4285_, 0);
                    v___x_4288_ = v___x_4285_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4289_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4283_);
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
                if lean_obj_tag(v___x_4300_) == 0 {
                    v___y_4293_ = v___y_4297_;
                    v___y_4294_ = v_a_4298_;
                    state = 15;
                    continue;
                } else {
                    v_val_4301_ = lean_ctor_get(v___x_4300_, 0);
                    lean_inc(v_val_4301_);
                    lean_dec_ref_known(v___x_4300_, 1);
                    v___x_4302_ = l_Option_fromJson_x3f___at___00__private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson_spec__2(v_val_4301_);
                    if lean_obj_tag(v___x_4302_) == 0 {
                        lean_dec(v_a_4298_);
                        lean_dec(v_a_4238_);
                        lean_dec(v_a_4228_);
                        v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
                        v_isSharedCheck_4312_ = (!lean_is_exclusive(v___x_4302_)) as u8;
                        if v_isSharedCheck_4312_ == 0 {
                            v___x_4305_ = v___x_4302_;
                            v_isShared_4306_ = v_isSharedCheck_4312_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_4303_);
                            lean_dec(v___x_4302_);
                            v___x_4305_ = lean_box(0);
                            v_isShared_4306_ = v_isSharedCheck_4312_;
                            state = 17;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v___x_4302_) == 0 {
                            lean_dec(v_a_4298_);
                            lean_dec(v_a_4238_);
                            lean_dec(v_a_4228_);
                            v_a_4313_ = lean_ctor_get(v___x_4302_, 0);
                            v_isSharedCheck_4320_ = (!lean_is_exclusive(v___x_4302_)) as u8;
                            if v_isSharedCheck_4320_ == 0 {
                                v___x_4315_ = v___x_4302_;
                                v_isShared_4316_ = v_isSharedCheck_4320_;
                                state = 19;
                                continue;
                            } else {
                                lean_inc(v_a_4313_);
                                lean_dec(v___x_4302_);
                                v___x_4315_ = lean_box(0);
                                v_isShared_4316_ = v_isSharedCheck_4320_;
                                state = 19;
                                continue;
                            }
                        } else {
                            v_a_4321_ = lean_ctor_get(v___x_4302_, 0);
                            lean_inc(v_a_4321_);
                            lean_dec_ref_known(v___x_4302_, 1);
                            if lean_obj_tag(v_a_4321_) == 0 {
                                v___y_4293_ = v___y_4297_;
                                v___y_4294_ = v_a_4298_;
                                state = 15;
                                continue;
                            } else {
                                v_val_4322_ = lean_ctor_get(v_a_4321_, 0);
                                lean_inc(v_val_4322_);
                                lean_dec_ref_known(v_a_4321_, 1);
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
                lean_dec(v_a_4303_);
                if v_isShared_4306_ == 0 {
                    lean_ctor_set(v___x_4305_, 0, v___x_4308_);
                    v___x_4310_ = v___x_4305_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4311_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4311_, 0, v___x_4308_);
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
                    lean_ctor_set_tag(v___x_4315_, 0);
                    v___x_4318_ = v___x_4315_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4319_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4313_);
                    v___x_4318_ = v_reuseFailAlloc_4319_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4318_;
            }
            21 => {
                v___x_4325_ = lean_box(0);
                v___y_4297_ = v___y_4324_;
                v_a_4298_ = v___x_4325_;
                state = 16;
                continue;
            }
            22 => {
                v___x_4328_ = l___private_Lake_Load_Manifest_0__Lake_instFromJsonPackageEntryV6_fromJson___closed__6;
                v___x_4329_ = l_Lake_JsonObject_getJson_x3f(v_a_4228_, v___x_4328_);
                if lean_obj_tag(v___x_4329_) == 0 {
                    v___y_4324_ = v_a_4327_;
                    state = 21;
                    continue;
                } else {
                    v_val_4330_ = lean_ctor_get(v___x_4329_, 0);
                    lean_inc(v_val_4330_);
                    lean_dec_ref_known(v___x_4329_, 1);
                    v___x_4331_ = l_Option_fromJson_x3f___at___00Lake_Manifest_fromJson_x3f_spec__0(
                        v_val_4330_,
                    );
                    if lean_obj_tag(v___x_4331_) == 0 {
                        lean_dec(v_a_4238_);
                        lean_dec(v_a_4228_);
                        v_a_4332_ = lean_ctor_get(v___x_4331_, 0);
                        v_isSharedCheck_4341_ = (!lean_is_exclusive(v___x_4331_)) as u8;
                        if v_isSharedCheck_4341_ == 0 {
                            v___x_4334_ = v___x_4331_;
                            v_isShared_4335_ = v_isSharedCheck_4341_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_4332_);
                            lean_dec(v___x_4331_);
                            v___x_4334_ = lean_box(0);
                            v_isShared_4335_ = v_isSharedCheck_4341_;
                            state = 23;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v___x_4331_) == 0 {
                            lean_dec(v_a_4238_);
                            lean_dec(v_a_4228_);
                            v_a_4342_ = lean_ctor_get(v___x_4331_, 0);
                            v_isSharedCheck_4349_ = (!lean_is_exclusive(v___x_4331_)) as u8;
                            if v_isSharedCheck_4349_ == 0 {
                                v___x_4344_ = v___x_4331_;
                                v_isShared_4345_ = v_isSharedCheck_4349_;
                                state = 25;
                                continue;
                            } else {
                                lean_inc(v_a_4342_);
                                lean_dec(v___x_4331_);
                                v___x_4344_ = lean_box(0);
                                v_isShared_4345_ = v_isSharedCheck_4349_;
                                state = 25;
                                continue;
                            }
                        } else {
                            v_a_4350_ = lean_ctor_get(v___x_4331_, 0);
                            lean_inc(v_a_4350_);
                            lean_dec_ref_known(v___x_4331_, 1);
                            if lean_obj_tag(v_a_4350_) == 0 {
                                v___y_4324_ = v_a_4327_;
                                state = 21;
                                continue;
                            } else {
                                v_val_4351_ = lean_ctor_get(v_a_4350_, 0);
                                lean_inc(v_val_4351_);
                                lean_dec_ref_known(v_a_4350_, 1);
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
                lean_dec(v_a_4332_);
                if v_isShared_4335_ == 0 {
                    lean_ctor_set(v___x_4334_, 0, v___x_4337_);
                    v___x_4339_ = v___x_4334_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4340_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4340_, 0, v___x_4337_);
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
                    lean_ctor_set_tag(v___x_4344_, 0);
                    v___x_4347_ = v___x_4344_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4348_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_a_4342_);
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
                lean_dec(v_a_4358_);
                if v_isShared_4361_ == 0 {
                    lean_ctor_set(v___x_4360_, 0, v___x_4363_);
                    v___x_4365_ = v___x_4360_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4366_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4366_, 0, v___x_4363_);
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
                    lean_ctor_set_tag(v___x_4370_, 0);
                    v___x_4373_ = v___x_4370_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4374_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_a_4368_);
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
pub unsafe fn l_Lake_Manifest_parse(mut v_data_4382_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4387_: u8 = 0;
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4393_: u8 = 0;
    let mut v_a_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4383_ = l_Lean_Json_parse(v_data_4382_);
                if lean_obj_tag(v___x_4383_) == 0 {
                    v_a_4384_ = lean_ctor_get(v___x_4383_, 0);
                    v_isSharedCheck_4393_ = (!lean_is_exclusive(v___x_4383_)) as u8;
                    if v_isSharedCheck_4393_ == 0 {
                        v___x_4386_ = v___x_4383_;
                        v_isShared_4387_ = v_isSharedCheck_4393_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4384_);
                        lean_dec(v___x_4383_);
                        v___x_4386_ = lean_box(0);
                        v_isShared_4387_ = v_isSharedCheck_4393_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4394_ = lean_ctor_get(v___x_4383_, 0);
                    lean_inc(v_a_4394_);
                    lean_dec_ref_known(v___x_4383_, 1);
                    v___x_4395_ = l_Lake_Manifest_fromJson_x3f(v_a_4394_);
                    return v___x_4395_;
                }
            }
            1 => {
                v___x_4388_ = l_Lake_Manifest_parse___closed__0;
                v___x_4389_ = lean_string_append(v___x_4388_, v_a_4384_);
                lean_dec(v_a_4384_);
                if v_isShared_4387_ == 0 {
                    lean_ctor_set(v___x_4386_, 0, v___x_4389_);
                    v___x_4391_ = v___x_4386_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4392_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4392_, 0, v___x_4389_);
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
pub unsafe fn l_Lake_Manifest_load(mut v_file_4397_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4403_: u8 = 0;
    let mut v_a_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4423_: u8 = 0;
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4427_: u8 = 0;
    let mut v_isSharedCheck_4428_: u8 = 0;
    let mut v_a_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4432_: u8 = 0;
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4436_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4399_ = l_IO_FS_readFile(v_file_4397_);
                if lean_obj_tag(v___x_4399_) == 0 {
                    v_a_4400_ = lean_ctor_get(v___x_4399_, 0);
                    v_isSharedCheck_4428_ = (!lean_is_exclusive(v___x_4399_)) as u8;
                    if v_isSharedCheck_4428_ == 0 {
                        v___x_4402_ = v___x_4399_;
                        v_isShared_4403_ = v_isSharedCheck_4428_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4400_);
                        lean_dec(v___x_4399_);
                        v___x_4402_ = lean_box(0);
                        v_isShared_4403_ = v_isSharedCheck_4428_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_file_4397_);
                    v_a_4429_ = lean_ctor_get(v___x_4399_, 0);
                    v_isSharedCheck_4436_ = (!lean_is_exclusive(v___x_4399_)) as u8;
                    if v_isSharedCheck_4436_ == 0 {
                        v___x_4431_ = v___x_4399_;
                        v_isShared_4432_ = v_isSharedCheck_4436_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4429_);
                        lean_dec(v___x_4399_);
                        v___x_4431_ = lean_box(0);
                        v_isShared_4432_ = v_isSharedCheck_4436_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4413_ = l_Lean_Json_parse(v_a_4400_);
                if lean_obj_tag(v___x_4413_) == 0 {
                    v_a_4414_ = lean_ctor_get(v___x_4413_, 0);
                    lean_inc(v_a_4414_);
                    lean_dec_ref_known(v___x_4413_, 1);
                    v___x_4415_ = l_Lake_Manifest_parse___closed__0;
                    v___x_4416_ = lean_string_append(v___x_4415_, v_a_4414_);
                    lean_dec(v_a_4414_);
                    v_a_4405_ = v___x_4416_;
                    state = 2;
                    continue;
                } else {
                    v_a_4417_ = lean_ctor_get(v___x_4413_, 0);
                    lean_inc(v_a_4417_);
                    lean_dec_ref_known(v___x_4413_, 1);
                    v___x_4418_ = l_Lake_Manifest_fromJson_x3f(v_a_4417_);
                    if lean_obj_tag(v___x_4418_) == 0 {
                        v_a_4419_ = lean_ctor_get(v___x_4418_, 0);
                        lean_inc(v_a_4419_);
                        lean_dec_ref_known(v___x_4418_, 1);
                        v_a_4405_ = v_a_4419_;
                        state = 2;
                        continue;
                    } else {
                        lean_del_object(v___x_4402_);
                        lean_dec_ref(v_file_4397_);
                        v_a_4420_ = lean_ctor_get(v___x_4418_, 0);
                        v_isSharedCheck_4427_ = (!lean_is_exclusive(v___x_4418_)) as u8;
                        if v_isSharedCheck_4427_ == 0 {
                            v___x_4422_ = v___x_4418_;
                            v_isShared_4423_ = v_isSharedCheck_4427_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_4420_);
                            lean_dec(v___x_4418_);
                            v___x_4422_ = lean_box(0);
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
                lean_dec_ref(v_a_4405_);
                v___x_4409_ = lean_mk_io_user_error(v___x_4408_);
                if v_isShared_4403_ == 0 {
                    lean_ctor_set_tag(v___x_4402_, 1);
                    lean_ctor_set(v___x_4402_, 0, v___x_4409_);
                    v___x_4411_ = v___x_4402_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4412_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4412_, 0, v___x_4409_);
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
                    lean_ctor_set_tag(v___x_4422_, 0);
                    v___x_4425_ = v___x_4422_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4426_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_a_4420_);
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
                    v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4429_);
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
    mut v_file_4437_: *mut LeanObject,
    mut v_a_4438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4439_: *mut LeanObject = core::ptr::null_mut();
    v_res_4439_ = l_Lake_Manifest_load(v_file_4437_);
    return v_res_4439_;
}
pub unsafe fn l_Lake_Manifest_load_x3f(mut v_file_4440_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4451_: u8 = 0;
    let mut v_a_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4468_: u8 = 0;
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4475_: u8 = 0;
    let mut v_isSharedCheck_4476_: u8 = 0;
    let mut v_a_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4447_ = l_IO_FS_readFile(v_file_4440_);
                if lean_obj_tag(v___x_4447_) == 0 {
                    v_a_4448_ = lean_ctor_get(v___x_4447_, 0);
                    v_isSharedCheck_4476_ = (!lean_is_exclusive(v___x_4447_)) as u8;
                    if v_isSharedCheck_4476_ == 0 {
                        v___x_4450_ = v___x_4447_;
                        v_isShared_4451_ = v_isSharedCheck_4476_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4448_);
                        lean_dec(v___x_4447_);
                        v___x_4450_ = lean_box(0);
                        v_isShared_4451_ = v_isSharedCheck_4476_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_file_4440_);
                    v_a_4477_ = lean_ctor_get(v___x_4447_, 0);
                    lean_inc(v_a_4477_);
                    lean_dec_ref_known(v___x_4447_, 1);
                    v_a_4443_ = v_a_4477_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v_a_4443_) == 11 {
                    lean_dec_ref_known(v_a_4443_, 2);
                    v___x_4444_ = lean_box(0);
                    v___x_4445_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4445_, 0, v___x_4444_);
                    return v___x_4445_;
                } else {
                    v___x_4446_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4446_, 0, v_a_4443_);
                    return v___x_4446_;
                }
            }
            2 => {
                v___x_4458_ = l_Lean_Json_parse(v_a_4448_);
                if lean_obj_tag(v___x_4458_) == 0 {
                    lean_del_object(v___x_4450_);
                    v_a_4459_ = lean_ctor_get(v___x_4458_, 0);
                    lean_inc(v_a_4459_);
                    lean_dec_ref_known(v___x_4458_, 1);
                    v___x_4460_ = l_Lake_Manifest_parse___closed__0;
                    v___x_4461_ = lean_string_append(v___x_4460_, v_a_4459_);
                    lean_dec(v_a_4459_);
                    v_a_4453_ = v___x_4461_;
                    state = 3;
                    continue;
                } else {
                    v_a_4462_ = lean_ctor_get(v___x_4458_, 0);
                    lean_inc(v_a_4462_);
                    lean_dec_ref_known(v___x_4458_, 1);
                    v___x_4463_ = l_Lake_Manifest_fromJson_x3f(v_a_4462_);
                    if lean_obj_tag(v___x_4463_) == 0 {
                        lean_del_object(v___x_4450_);
                        v_a_4464_ = lean_ctor_get(v___x_4463_, 0);
                        lean_inc(v_a_4464_);
                        lean_dec_ref_known(v___x_4463_, 1);
                        v_a_4453_ = v_a_4464_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec_ref(v_file_4440_);
                        v_a_4465_ = lean_ctor_get(v___x_4463_, 0);
                        v_isSharedCheck_4475_ = (!lean_is_exclusive(v___x_4463_)) as u8;
                        if v_isSharedCheck_4475_ == 0 {
                            v___x_4467_ = v___x_4463_;
                            v_isShared_4468_ = v_isSharedCheck_4475_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_4465_);
                            lean_dec(v___x_4463_);
                            v___x_4467_ = lean_box(0);
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
                lean_dec_ref(v_a_4453_);
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
                    v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4465_);
                    v___x_4470_ = v_reuseFailAlloc_4474_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4451_ == 0 {
                    lean_ctor_set(v___x_4450_, 0, v___x_4470_);
                    v___x_4472_ = v___x_4450_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4473_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4473_, 0, v___x_4470_);
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
    mut v_file_4478_: *mut LeanObject,
    mut v_a_4479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4480_: *mut LeanObject = core::ptr::null_mut();
    v_res_4480_ = l_Lake_Manifest_load_x3f(v_file_4478_);
    return v_res_4480_;
}
pub unsafe fn l_Lake_Manifest_save(
    mut v_self_4481_: *mut LeanObject,
    mut v_manifestFile_4482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contents_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: u32 = 0;
    let mut v___x_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    v___x_4484_ = l_Lake_Manifest_toJson(v_self_4481_);
    v___x_4485_ = lean_unsigned_to_nat(80);
    v_contents_4486_ = l_Lean_Json_pretty(v___x_4484_, v___x_4485_);
    v___x_4487_ = 10;
    v___x_4488_ = lean_string_push(v_contents_4486_, v___x_4487_);
    v___x_4489_ = l_IO_FS_writeFile(v_manifestFile_4482_, v___x_4488_);
    lean_dec_ref(v___x_4488_);
    return v___x_4489_;
}
pub unsafe fn l_Lake_Manifest_save___boxed(
    mut v_self_4490_: *mut LeanObject,
    mut v_manifestFile_4491_: *mut LeanObject,
    mut v_a_4492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4493_: *mut LeanObject = core::ptr::null_mut();
    v_res_4493_ = l_Lake_Manifest_save(v_self_4490_, v_manifestFile_4491_);
    lean_dec_ref(v_manifestFile_4491_);
    return v_res_4493_;
}
pub unsafe fn l_Lake_Manifest_decodeEntries(mut v_data_4494_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4499_: u8 = 0;
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4503_: u8 = 0;
    let mut v_a_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4509_: u8 = 0;
    let mut v___x_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4513_: u8 = 0;
    let mut v_a_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4495_ = l_Lean_Json_getObj_x3f(v_data_4494_);
                if lean_obj_tag(v___x_4495_) == 0 {
                    v_a_4496_ = lean_ctor_get(v___x_4495_, 0);
                    v_isSharedCheck_4503_ = (!lean_is_exclusive(v___x_4495_)) as u8;
                    if v_isSharedCheck_4503_ == 0 {
                        v___x_4498_ = v___x_4495_;
                        v_isShared_4499_ = v_isSharedCheck_4503_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4496_);
                        lean_dec(v___x_4495_);
                        v___x_4498_ = lean_box(0);
                        v_isShared_4499_ = v_isSharedCheck_4503_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4504_ = lean_ctor_get(v___x_4495_, 0);
                    lean_inc(v_a_4504_);
                    lean_dec_ref_known(v___x_4495_, 1);
                    v___x_4505_ =
                        l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion(v_a_4504_);
                    if lean_obj_tag(v___x_4505_) == 0 {
                        lean_dec(v_a_4504_);
                        v_a_4506_ = lean_ctor_get(v___x_4505_, 0);
                        v_isSharedCheck_4513_ = (!lean_is_exclusive(v___x_4505_)) as u8;
                        if v_isSharedCheck_4513_ == 0 {
                            v___x_4508_ = v___x_4505_;
                            v_isShared_4509_ = v_isSharedCheck_4513_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4506_);
                            lean_dec(v___x_4505_);
                            v___x_4508_ = lean_box(0);
                            v_isShared_4509_ = v_isSharedCheck_4513_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4514_ = lean_ctor_get(v___x_4505_, 0);
                        lean_inc(v_a_4514_);
                        lean_dec_ref_known(v___x_4505_, 1);
                        v___x_4515_ = l_Lake_Manifest_version___closed__1;
                        v___x_4516_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4516_, 0, v_a_4514_);
                        lean_ctor_set(v___x_4516_, 1, v___x_4515_);
                        v___x_4517_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages(
                            v___x_4516_,
                            v_a_4504_,
                        );
                        lean_dec(v_a_4504_);
                        lean_dec_ref_known(v___x_4516_, 2);
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
                    v_reuseFailAlloc_4502_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_a_4496_);
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
                    v_reuseFailAlloc_4512_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4506_);
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
pub unsafe fn l_Lake_Manifest_parseEntries(mut v_data_4518_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4523_: u8 = 0;
    let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4529_: u8 = 0;
    let mut v_a_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4519_ = l_Lean_Json_parse(v_data_4518_);
                if lean_obj_tag(v___x_4519_) == 0 {
                    v_a_4520_ = lean_ctor_get(v___x_4519_, 0);
                    v_isSharedCheck_4529_ = (!lean_is_exclusive(v___x_4519_)) as u8;
                    if v_isSharedCheck_4529_ == 0 {
                        v___x_4522_ = v___x_4519_;
                        v_isShared_4523_ = v_isSharedCheck_4529_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4520_);
                        lean_dec(v___x_4519_);
                        v___x_4522_ = lean_box(0);
                        v_isShared_4523_ = v_isSharedCheck_4529_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4530_ = lean_ctor_get(v___x_4519_, 0);
                    lean_inc(v_a_4530_);
                    lean_dec_ref_known(v___x_4519_, 1);
                    v___x_4531_ = l_Lake_Manifest_decodeEntries(v_a_4530_);
                    return v___x_4531_;
                }
            }
            1 => {
                v___x_4524_ = l_Lake_Manifest_parse___closed__0;
                v___x_4525_ = lean_string_append(v___x_4524_, v_a_4520_);
                lean_dec(v_a_4520_);
                if v_isShared_4523_ == 0 {
                    lean_ctor_set(v___x_4522_, 0, v___x_4525_);
                    v___x_4527_ = v___x_4522_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4528_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4528_, 0, v___x_4525_);
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
pub unsafe fn l_Lake_Manifest_loadEntries(mut v_file_4532_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4538_: u8 = 0;
    let mut v_a_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4558_: u8 = 0;
    let mut v___x_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4562_: u8 = 0;
    let mut v_isSharedCheck_4563_: u8 = 0;
    let mut v_a_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4567_: u8 = 0;
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4571_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4534_ = l_IO_FS_readFile(v_file_4532_);
                if lean_obj_tag(v___x_4534_) == 0 {
                    v_a_4535_ = lean_ctor_get(v___x_4534_, 0);
                    v_isSharedCheck_4563_ = (!lean_is_exclusive(v___x_4534_)) as u8;
                    if v_isSharedCheck_4563_ == 0 {
                        v___x_4537_ = v___x_4534_;
                        v_isShared_4538_ = v_isSharedCheck_4563_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4535_);
                        lean_dec(v___x_4534_);
                        v___x_4537_ = lean_box(0);
                        v_isShared_4538_ = v_isSharedCheck_4563_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_file_4532_);
                    v_a_4564_ = lean_ctor_get(v___x_4534_, 0);
                    v_isSharedCheck_4571_ = (!lean_is_exclusive(v___x_4534_)) as u8;
                    if v_isSharedCheck_4571_ == 0 {
                        v___x_4566_ = v___x_4534_;
                        v_isShared_4567_ = v_isSharedCheck_4571_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4564_);
                        lean_dec(v___x_4534_);
                        v___x_4566_ = lean_box(0);
                        v_isShared_4567_ = v_isSharedCheck_4571_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4548_ = l_Lean_Json_parse(v_a_4535_);
                if lean_obj_tag(v___x_4548_) == 0 {
                    v_a_4549_ = lean_ctor_get(v___x_4548_, 0);
                    lean_inc(v_a_4549_);
                    lean_dec_ref_known(v___x_4548_, 1);
                    v___x_4550_ = l_Lake_Manifest_parse___closed__0;
                    v___x_4551_ = lean_string_append(v___x_4550_, v_a_4549_);
                    lean_dec(v_a_4549_);
                    v_a_4540_ = v___x_4551_;
                    state = 2;
                    continue;
                } else {
                    v_a_4552_ = lean_ctor_get(v___x_4548_, 0);
                    lean_inc(v_a_4552_);
                    lean_dec_ref_known(v___x_4548_, 1);
                    v___x_4553_ = l_Lake_Manifest_decodeEntries(v_a_4552_);
                    if lean_obj_tag(v___x_4553_) == 0 {
                        v_a_4554_ = lean_ctor_get(v___x_4553_, 0);
                        lean_inc(v_a_4554_);
                        lean_dec_ref_known(v___x_4553_, 1);
                        v_a_4540_ = v_a_4554_;
                        state = 2;
                        continue;
                    } else {
                        lean_del_object(v___x_4537_);
                        lean_dec_ref(v_file_4532_);
                        v_a_4555_ = lean_ctor_get(v___x_4553_, 0);
                        v_isSharedCheck_4562_ = (!lean_is_exclusive(v___x_4553_)) as u8;
                        if v_isSharedCheck_4562_ == 0 {
                            v___x_4557_ = v___x_4553_;
                            v_isShared_4558_ = v_isSharedCheck_4562_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_4555_);
                            lean_dec(v___x_4553_);
                            v___x_4557_ = lean_box(0);
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
                lean_dec_ref(v_a_4540_);
                v___x_4544_ = lean_mk_io_user_error(v___x_4543_);
                if v_isShared_4538_ == 0 {
                    lean_ctor_set_tag(v___x_4537_, 1);
                    lean_ctor_set(v___x_4537_, 0, v___x_4544_);
                    v___x_4546_ = v___x_4537_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4547_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4547_, 0, v___x_4544_);
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
                    lean_ctor_set_tag(v___x_4557_, 0);
                    v___x_4560_ = v___x_4557_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4561_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4555_);
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
                    v_reuseFailAlloc_4570_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_a_4564_);
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
    mut v_file_4572_: *mut LeanObject,
    mut v_a_4573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4574_: *mut LeanObject = core::ptr::null_mut();
    v_res_4574_ = l_Lake_Manifest_loadEntries(v_file_4572_);
    return v_res_4574_;
}
pub unsafe fn l_Lake_Manifest_tryLoadEntries(mut v_file_4575_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4591_: u8 = 0;
    let mut v_a_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4609_: u8 = 0;
    let mut v_a_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4587_ = l_IO_FS_readFile(v_file_4575_);
                if lean_obj_tag(v___x_4587_) == 0 {
                    v_a_4588_ = lean_ctor_get(v___x_4587_, 0);
                    v_isSharedCheck_4609_ = (!lean_is_exclusive(v___x_4587_)) as u8;
                    if v_isSharedCheck_4609_ == 0 {
                        v___x_4590_ = v___x_4587_;
                        v_isShared_4591_ = v_isSharedCheck_4609_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4588_);
                        lean_dec(v___x_4587_);
                        v___x_4590_ = lean_box(0);
                        v_isShared_4591_ = v_isSharedCheck_4609_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4610_ = lean_ctor_get(v___x_4587_, 0);
                    lean_inc(v_a_4610_);
                    lean_dec_ref_known(v___x_4587_, 1);
                    v_a_4578_ = v_a_4610_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v_a_4578_) == 11 {
                    lean_dec_ref_known(v_a_4578_, 2);
                    lean_dec_ref(v_file_4575_);
                    v___x_4579_ =
                        l___private_Lake_Load_Manifest_0__Lake_Manifest_getPackages___closed__1;
                    v___x_4580_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4580_, 0, v___x_4579_);
                    return v___x_4580_;
                } else {
                    v___x_4581_ = l_Lake_Manifest_load___closed__0;
                    v___x_4582_ = lean_string_append(v_file_4575_, v___x_4581_);
                    v___x_4583_ = lean_io_error_to_string(v_a_4578_);
                    v___x_4584_ = lean_string_append(v___x_4582_, v___x_4583_);
                    lean_dec_ref(v___x_4583_);
                    v___x_4585_ = lean_mk_io_user_error(v___x_4584_);
                    v___x_4586_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4586_, 0, v___x_4585_);
                    return v___x_4586_;
                }
            }
            2 => {
                v___x_4598_ = l_Lean_Json_parse(v_a_4588_);
                if lean_obj_tag(v___x_4598_) == 0 {
                    lean_del_object(v___x_4590_);
                    v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
                    lean_inc(v_a_4599_);
                    lean_dec_ref_known(v___x_4598_, 1);
                    v___x_4600_ = l_Lake_Manifest_parse___closed__0;
                    v___x_4601_ = lean_string_append(v___x_4600_, v_a_4599_);
                    lean_dec(v_a_4599_);
                    v_a_4593_ = v___x_4601_;
                    state = 3;
                    continue;
                } else {
                    v_a_4602_ = lean_ctor_get(v___x_4598_, 0);
                    lean_inc(v_a_4602_);
                    lean_dec_ref_known(v___x_4598_, 1);
                    v___x_4603_ = l_Lake_Manifest_decodeEntries(v_a_4602_);
                    if lean_obj_tag(v___x_4603_) == 0 {
                        lean_del_object(v___x_4590_);
                        v_a_4604_ = lean_ctor_get(v___x_4603_, 0);
                        lean_inc(v_a_4604_);
                        lean_dec_ref_known(v___x_4603_, 1);
                        v_a_4593_ = v_a_4604_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec_ref(v_file_4575_);
                        v_a_4605_ = lean_ctor_get(v___x_4603_, 0);
                        lean_inc(v_a_4605_);
                        lean_dec_ref_known(v___x_4603_, 1);
                        if v_isShared_4591_ == 0 {
                            lean_ctor_set(v___x_4590_, 0, v_a_4605_);
                            v___x_4607_ = v___x_4590_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4608_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4608_, 0, v_a_4605_);
                            v___x_4607_ = v_reuseFailAlloc_4608_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_4594_ = l_Lake_Manifest_load___closed__0;
                lean_inc_ref(v_file_4575_);
                v___x_4595_ = lean_string_append(v_file_4575_, v___x_4594_);
                v___x_4596_ = lean_string_append(v___x_4595_, v_a_4593_);
                lean_dec_ref(v_a_4593_);
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
    mut v_file_4611_: *mut LeanObject,
    mut v_a_4612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4613_: *mut LeanObject = core::ptr::null_mut();
    v_res_4613_ = l_Lake_Manifest_tryLoadEntries(v_file_4611_);
    return v_res_4613_;
}
pub unsafe fn _init_l_Lake_Manifest_saveEntries___closed__0() -> *mut LeanObject {
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    v___x_4614_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Manifest_toJson___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Manifest_toJson___closed__2_once),
        _init_l_Lake_Manifest_toJson___closed__2,
    );
    v___x_4615_ = l___private_Lake_Load_Manifest_0__Lake_Manifest_getVersion___closed__7;
    v___x_4616_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4616_, 0, v___x_4615_);
    lean_ctor_set(v___x_4616_, 1, v___x_4614_);
    return v___x_4616_;
}
pub unsafe fn l_Lake_Manifest_saveEntries(
    mut v_file_4617_: *mut LeanObject,
    mut v_entries_4618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contents_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: u32 = 0;
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
    v___x_4620_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Manifest_saveEntries___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Manifest_saveEntries___closed__0_once),
        _init_l_Lake_Manifest_saveEntries___closed__0,
    );
    v___x_4621_ = l_Lake_Manifest_toJson___closed__7;
    v___x_4622_ = l_Array_toJson___at___00Lake_Manifest_toJson_spec__0(v_entries_4618_);
    v___x_4623_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4623_, 0, v___x_4621_);
    lean_ctor_set(v___x_4623_, 1, v___x_4622_);
    v___x_4624_ = lean_box(0);
    v___x_4625_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4625_, 0, v___x_4623_);
    lean_ctor_set(v___x_4625_, 1, v___x_4624_);
    v___x_4626_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4626_, 0, v___x_4620_);
    lean_ctor_set(v___x_4626_, 1, v___x_4625_);
    v___x_4627_ = l_Lean_Json_mkObj(v___x_4626_);
    lean_dec_ref_known(v___x_4626_, 2);
    v___x_4628_ = lean_unsigned_to_nat(80);
    v_contents_4629_ = l_Lean_Json_pretty(v___x_4627_, v___x_4628_);
    v___x_4630_ = 10;
    v___x_4631_ = lean_string_push(v_contents_4629_, v___x_4630_);
    v___x_4632_ = l_IO_FS_writeFile(v_file_4617_, v___x_4631_);
    lean_dec_ref(v___x_4631_);
    return v___x_4632_;
}
pub unsafe fn l_Lake_Manifest_saveEntries___boxed(
    mut v_file_4633_: *mut LeanObject,
    mut v_entries_4634_: *mut LeanObject,
    mut v_a_4635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4636_: *mut LeanObject = core::ptr::null_mut();
    v_res_4636_ = l_Lake_Manifest_saveEntries(v_file_4633_, v_entries_4634_);
    lean_dec_ref(v_file_4633_);
    return v_res_4636_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Load_Manifest(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Util_Version(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Defaults(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Git(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Error(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_FilePath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_JsonObject(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Coe(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_instInhabitedPackageEntry_default = _init_l_Lake_instInhabitedPackageEntry_default();
    lean_mark_persistent(l_Lake_instInhabitedPackageEntry_default);
    l_Lake_instInhabitedPackageEntry = _init_l_Lake_instInhabitedPackageEntry();
    lean_mark_persistent(l_Lake_instInhabitedPackageEntry);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Load_Manifest(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Load_Manifest(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Util_Version(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Defaults(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Git(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Error(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_FilePath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_JsonObject(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Coe(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Manifest(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Load_Manifest(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Load_Manifest(builtin);
}
