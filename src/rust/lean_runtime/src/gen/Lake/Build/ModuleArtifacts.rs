// Lean compiler output
// Module: Lake.Build.ModuleArtifacts
// Imports: Lake.Config.Artifact Lake.Util.JsonObject
use crate::r#gen::Lake::Config::Artifact::{
    initialize_Lake_Config_Artifact, l_Lake_ArtifactDescr_fromJson_x3f,
    runtime_initialize_Lake_Config_Artifact,
};
use crate::r#gen::Lake::Util::JsonObject::{
    initialize_Lake_Util_JsonObject, l_Lake_JsonObject_getJson_x3f, l_Lake_JsonObject_insertJson,
    runtime_initialize_Lake_Util_JsonObject,
};
use crate::r#gen::Lake::Util::String::l_Lake_lowerHexUInt64;
use crate::r#gen::Lean::Data::Json::Basic::{l_Lean_Json_getBool_x3f, l_Lean_Json_getObj_x3f};
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_pretty;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_dec_lt,
    lean_string_utf8_byte_size,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lake_ModuleOutputDescrs_toJson___closed__0_value: LeanStringObject<2> =
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
        m_data: [108, 0],
    };
static mut l_Lake_ModuleOutputDescrs_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_toJson___closed__0_value) as *mut LeanObject;
pub static l_Lake_ModuleOutputDescrs_toJson___closed__1_value: LeanStringObject<2> =
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
        m_data: [98, 0],
    };
static mut l_Lake_ModuleOutputDescrs_toJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_toJson___closed__1_value) as *mut LeanObject;
pub static l_Lake_ModuleOutputDescrs_toJson___closed__2_value: LeanStringObject<2> =
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
static mut l_Lake_ModuleOutputDescrs_toJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_toJson___closed__2_value) as *mut LeanObject;
pub static l_Lake_ModuleOutputDescrs_toJson___closed__3_value: LeanStringObject<2> =
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
        m_data: [109, 0],
    };
static mut l_Lake_ModuleOutputDescrs_toJson___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_toJson___closed__3_value) as *mut LeanObject;
pub static l_Lake_ModuleOutputDescrs_toJson___closed__4_value: LeanStringObject<2> =
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
        m_data: [111, 0],
    };
static mut l_Lake_ModuleOutputDescrs_toJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_toJson___closed__4_value) as *mut LeanObject;
pub static l_Lake_ModuleOutputDescrs_toJson___closed__5_value: LeanStringObject<2> =
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
        m_data: [105, 0],
    };
static mut l_Lake_ModuleOutputDescrs_toJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_toJson___closed__5_value) as *mut LeanObject;
pub static l_Lake_ModuleOutputDescrs_toJson___closed__6_value: LeanStringObject<2> =
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
        m_data: [114, 0],
    };
static mut l_Lake_ModuleOutputDescrs_toJson___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_toJson___closed__6_value) as *mut LeanObject;
pub static l_Lake_instToJsonModuleOutputDescrs___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_ModuleOutputDescrs_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToJsonModuleOutputDescrs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonModuleOutputDescrs___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instToJsonModuleOutputDescrs: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonModuleOutputDescrs___closed__0_value) as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___closed__0_value) as *mut LeanObject;
pub static l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__0_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__1_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__0_value: LeanStringObject<22> =
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
            112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
            58, 32, 111, 0,
        ],
    };
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__2_value: LeanStringObject<4> =
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
        m_data: [111, 58, 32, 0],
    };
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__3_value: LeanStringObject<39> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 39,
        m_capacity: 39,
        m_length: 38,
        m_data: [
            101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 108, 101, 97, 115, 116, 32, 111,
            110, 101, 32, 39, 111, 39, 32, 40, 46, 111, 108, 101, 97, 110, 41, 32, 104, 97, 115,
            104, 0,
        ],
    };
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__4_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__4_value)
        as *mut LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__5_value: LeanStringObject<4> =
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
        m_data: [108, 58, 32, 0],
    };
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__5_value)
        as *mut LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__6_value: LeanStringObject<22> =
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
            112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
            58, 32, 99, 0,
        ],
    };
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__6_value)
        as *mut LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__7_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__7_value)
        as *mut LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__8_value: LeanStringObject<4> =
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
        m_data: [99, 58, 32, 0],
    };
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__8_value)
        as *mut LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__9_value: LeanStringObject<4> =
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
        m_data: [98, 58, 32, 0],
    };
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__9_value)
        as *mut LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10_value: LeanStringObject<22> =
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
            112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
            58, 32, 105, 0,
        ],
    };
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10_value)
        as *mut LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11_value)
        as *mut LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12_value: LeanStringObject<4> =
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
        m_data: [105, 58, 32, 0],
    };
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12_value)
        as *mut LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__13_value: LeanStringObject<4> =
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
        m_data: [114, 58, 32, 0],
    };
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__13_value)
        as *mut LeanObject;
pub static l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__14_value: LeanStringObject<4> =
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
        m_data: [109, 58, 32, 0],
    };
static mut l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__14_value)
        as *mut LeanObject;
pub static l_Lake_instFromJsonModuleOutputDescrs___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_ModuleOutputDescrs_fromJson_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instFromJsonModuleOutputDescrs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonModuleOutputDescrs___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instFromJsonModuleOutputDescrs: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instFromJsonModuleOutputDescrs___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lake_ModuleOutputDescrs_oleanParts(
    mut v_self_621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_olean_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_oleanServer_x3f_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_oleanPrivate_x3f_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descrs_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descrs_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descrs_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descrs_633_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_olean_622_ = lean_ctor_get(v_self_621_, 0);
                lean_inc_ref(v_olean_622_);
                v_oleanServer_x3f_623_ = lean_ctor_get(v_self_621_, 1);
                lean_inc(v_oleanServer_x3f_623_);
                v_oleanPrivate_x3f_624_ = lean_ctor_get(v_self_621_, 2);
                lean_inc(v_oleanPrivate_x3f_624_);
                lean_dec_ref(v_self_621_);
                v___x_629_ = lean_unsigned_to_nat(1);
                v___x_630_ = lean_mk_empty_array_with_capacity(v___x_629_);
                v_descrs_631_ = lean_array_push(v___x_630_, v_olean_622_);
                if lean_obj_tag(v_oleanServer_x3f_623_) == 1 {
                    v_val_632_ = lean_ctor_get(v_oleanServer_x3f_623_, 0);
                    lean_inc(v_val_632_);
                    lean_dec_ref_known(v_oleanServer_x3f_623_, 1);
                    v_descrs_633_ = lean_array_push(v_descrs_631_, v_val_632_);
                    v_descrs_626_ = v_descrs_633_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_oleanServer_x3f_623_);
                    v_descrs_626_ = v_descrs_631_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v_oleanPrivate_x3f_624_) == 1 {
                    v_val_627_ = lean_ctor_get(v_oleanPrivate_x3f_624_, 0);
                    lean_inc(v_val_627_);
                    lean_dec_ref_known(v_oleanPrivate_x3f_624_, 1);
                    v_descrs_628_ = lean_array_push(v_descrs_626_, v_val_627_);
                    return v_descrs_628_;
                } else {
                    lean_dec(v_oleanPrivate_x3f_624_);
                    return v_descrs_626_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0(
    mut v_sz_635_: usize,
    mut v_i_636_: usize,
    mut v_bs_637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_638_: u8 = 0;
    let mut v_v_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hash_640_: u64 = 0;
    let mut v_ext_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: usize = 0;
    let mut v___x_648_: usize = 0;
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: u8 = 0;
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_638_ = lean_usize_dec_lt(v_i_636_, v_sz_635_);
                if v___x_638_ == 0 {
                    return v_bs_637_;
                } else {
                    v_v_639_ = lean_array_uget_borrowed(v_bs_637_, v_i_636_);
                    v_hash_640_ = lean_ctor_get_uint64(
                        v_v_639_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_ext_641_ = lean_ctor_get(v_v_639_, 0);
                    lean_inc_ref(v_ext_641_);
                    v___x_642_ = lean_unsigned_to_nat(0);
                    v_bs_x27_643_ = lean_array_uset(v_bs_637_, v_i_636_, v___x_642_);
                    v___x_651_ = lean_string_utf8_byte_size(v_ext_641_);
                    v___x_652_ = lean_nat_dec_eq(v___x_651_, v___x_642_);
                    if v___x_652_ == 0 {
                        v___x_653_ = l_Lake_lowerHexUInt64(v_hash_640_);
                        v___x_654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0;
                        v___x_655_ = lean_string_append(v___x_653_, v___x_654_);
                        v___x_656_ = lean_string_append(v___x_655_, v_ext_641_);
                        lean_dec_ref(v_ext_641_);
                        v___y_645_ = v___x_656_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_ext_641_);
                        v___x_657_ = l_Lake_lowerHexUInt64(v_hash_640_);
                        v___y_645_ = v___x_657_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_646_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_646_, 0, v___y_645_);
                v___x_647_ = 1usize;
                v___x_648_ = lean_usize_add(v_i_636_, v___x_647_);
                v___x_649_ = lean_array_uset(v_bs_x27_643_, v_i_636_, v___x_646_);
                v_i_636_ = v___x_648_;
                v_bs_637_ = v___x_649_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___boxed(
    mut v_sz_658_: *mut LeanObject,
    mut v_i_659_: *mut LeanObject,
    mut v_bs_660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_661_: usize = 0;
    let mut v_i_boxed_662_: usize = 0;
    let mut v_res_663_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_661_ = lean_unbox_usize(v_sz_658_);
    lean_dec(v_sz_658_);
    v_i_boxed_662_ = lean_unbox_usize(v_i_659_);
    lean_dec(v_i_659_);
    v_res_663_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0(v_sz_boxed_661_, v_i_boxed_662_, v_bs_660_);
    return v_res_663_;
}
pub unsafe fn l_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0(
    mut v_a_664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_665_: usize = 0;
    let mut v___x_666_: usize = 0;
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    v_sz_665_ = lean_array_size(v_a_664_);
    v___x_666_ = 0usize;
    v___x_667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0(v_sz_665_, v___x_666_, v_a_664_);
    v___x_668_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_668_, 0, v___x_667_);
    return v___x_668_;
}
pub unsafe fn l_Lake_ModuleOutputDescrs_toJson(
    mut v_self_676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_684_: u8 = 0;
    let mut v_ilean_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ir_x3f_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bc_x3f_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltar_x3f_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_obj_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hash_693_: u64 = 0;
    let mut v_ext_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: u8 = 0;
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hash_718_: u64 = 0;
    let mut v_ext_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_723_: u8 = 0;
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_obj_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hash_731_: u64 = 0;
    let mut v_ext_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_736_: u8 = 0;
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hash_748_: u64 = 0;
    let mut v_ext_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_obj_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_obj_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_obj_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hash_764_: u64 = 0;
    let mut v_ext_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_769_: u8 = 0;
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: u8 = 0;
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isModule_684_ = lean_ctor_get_uint8(
                    v_self_676_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                v_ilean_685_ = lean_ctor_get(v_self_676_, 3);
                v_ir_x3f_686_ = lean_ctor_get(v_self_676_, 4);
                lean_inc(v_ir_x3f_686_);
                v_c_687_ = lean_ctor_get(v_self_676_, 5);
                lean_inc_ref(v_c_687_);
                v_bc_x3f_688_ = lean_ctor_get(v_self_676_, 6);
                lean_inc(v_bc_x3f_688_);
                v_ltar_x3f_689_ = lean_ctor_get(v_self_676_, 7);
                lean_inc(v_ltar_x3f_689_);
                v_hash_748_ = lean_ctor_get_uint64(
                    v_ilean_685_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_ext_749_ = lean_ctor_get(v_ilean_685_, 0);
                lean_inc_ref(v_ext_749_);
                v_obj_750_ = lean_box(1);
                v___x_751_ = l_Lake_ModuleOutputDescrs_toJson___closed__3;
                v___x_752_ = lean_alloc_ctor(1, 0, (1) as u32);
                lean_ctor_set_uint8(v___x_752_, 0 as u32, v_isModule_684_);
                v_obj_753_ = l_Lake_JsonObject_insertJson(v_obj_750_, v___x_751_, v___x_752_);
                v___x_754_ = l_Lake_ModuleOutputDescrs_toJson___closed__4;
                v___x_755_ = l_Lake_ModuleOutputDescrs_oleanParts(v_self_676_);
                v___x_756_ =
                    l_Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0(v___x_755_);
                v_obj_757_ = l_Lake_JsonObject_insertJson(v_obj_753_, v___x_754_, v___x_756_);
                v___x_758_ = l_Lake_ModuleOutputDescrs_toJson___closed__5;
                v___x_775_ = lean_string_utf8_byte_size(v_ext_749_);
                v___x_776_ = lean_unsigned_to_nat(0);
                v___x_777_ = lean_nat_dec_eq(v___x_775_, v___x_776_);
                if v___x_777_ == 0 {
                    v___x_778_ = l_Lake_lowerHexUInt64(v_hash_748_);
                    v___x_779_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0;
                    v___x_780_ = lean_string_append(v___x_778_, v___x_779_);
                    v___x_781_ = lean_string_append(v___x_780_, v_ext_749_);
                    lean_dec_ref(v_ext_749_);
                    v___y_760_ = v___x_781_;
                    state = 7;
                    continue;
                } else {
                    lean_dec_ref(v_ext_749_);
                    v___x_782_ = l_Lake_lowerHexUInt64(v_hash_748_);
                    v___y_760_ = v___x_782_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                v___x_681_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_681_, 0, v___y_680_);
                lean_inc_ref(v___y_678_);
                v___x_682_ = l_Lake_JsonObject_insertJson(v___y_679_, v___y_678_, v___x_681_);
                v___x_683_ = lean_alloc_ctor(5, 1, (0) as u32);
                lean_ctor_set(v___x_683_, 0, v___x_682_);
                return v___x_683_;
            }
            2 => {
                if lean_obj_tag(v_ltar_x3f_689_) == 1 {
                    v_val_692_ = lean_ctor_get(v_ltar_x3f_689_, 0);
                    lean_inc(v_val_692_);
                    lean_dec_ref_known(v_ltar_x3f_689_, 1);
                    v_hash_693_ = lean_ctor_get_uint64(
                        v_val_692_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_ext_694_ = lean_ctor_get(v_val_692_, 0);
                    lean_inc_ref(v_ext_694_);
                    lean_dec(v_val_692_);
                    v___x_695_ = l_Lake_ModuleOutputDescrs_toJson___closed__0;
                    v___x_696_ = lean_string_utf8_byte_size(v_ext_694_);
                    v___x_697_ = lean_unsigned_to_nat(0);
                    v___x_698_ = lean_nat_dec_eq(v___x_696_, v___x_697_);
                    if v___x_698_ == 0 {
                        v___x_699_ = l_Lake_lowerHexUInt64(v_hash_693_);
                        v___x_700_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0;
                        v___x_701_ = lean_string_append(v___x_699_, v___x_700_);
                        v___x_702_ = lean_string_append(v___x_701_, v_ext_694_);
                        lean_dec_ref(v_ext_694_);
                        v___y_678_ = v___x_695_;
                        v___y_679_ = v_obj_691_;
                        v___y_680_ = v___x_702_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_ext_694_);
                        v___x_703_ = l_Lake_lowerHexUInt64(v_hash_693_);
                        v___y_678_ = v___x_695_;
                        v___y_679_ = v_obj_691_;
                        v___y_680_ = v___x_703_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_ltar_x3f_689_);
                    v___x_704_ = lean_alloc_ctor(5, 1, (0) as u32);
                    lean_ctor_set(v___x_704_, 0, v_obj_691_);
                    return v___x_704_;
                }
            }
            3 => {
                v___x_709_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_709_, 0, v___y_708_);
                lean_inc_ref(v___y_707_);
                v___x_710_ = l_Lake_JsonObject_insertJson(v___y_706_, v___y_707_, v___x_709_);
                v_obj_691_ = v___x_710_;
                state = 2;
                continue;
            }
            4 => {
                v___x_715_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_715_, 0, v___y_714_);
                lean_inc_ref(v___y_712_);
                v___x_716_ = l_Lake_JsonObject_insertJson(v___y_713_, v___y_712_, v___x_715_);
                if lean_obj_tag(v_bc_x3f_688_) == 1 {
                    v_val_717_ = lean_ctor_get(v_bc_x3f_688_, 0);
                    lean_inc(v_val_717_);
                    lean_dec_ref_known(v_bc_x3f_688_, 1);
                    v_hash_718_ = lean_ctor_get_uint64(
                        v_val_717_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_ext_719_ = lean_ctor_get(v_val_717_, 0);
                    lean_inc_ref(v_ext_719_);
                    lean_dec(v_val_717_);
                    v___x_720_ = l_Lake_ModuleOutputDescrs_toJson___closed__1;
                    v___x_721_ = lean_string_utf8_byte_size(v_ext_719_);
                    v___x_722_ = lean_unsigned_to_nat(0);
                    v___x_723_ = lean_nat_dec_eq(v___x_721_, v___x_722_);
                    if v___x_723_ == 0 {
                        v___x_724_ = l_Lake_lowerHexUInt64(v_hash_718_);
                        v___x_725_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0;
                        v___x_726_ = lean_string_append(v___x_724_, v___x_725_);
                        v___x_727_ = lean_string_append(v___x_726_, v_ext_719_);
                        lean_dec_ref(v_ext_719_);
                        v___y_706_ = v___x_716_;
                        v___y_707_ = v___x_720_;
                        v___y_708_ = v___x_727_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec_ref(v_ext_719_);
                        v___x_728_ = l_Lake_lowerHexUInt64(v_hash_718_);
                        v___y_706_ = v___x_716_;
                        v___y_707_ = v___x_720_;
                        v___y_708_ = v___x_728_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_bc_x3f_688_);
                    v_obj_691_ = v___x_716_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v_hash_731_ = lean_ctor_get_uint64(
                    v_c_687_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_ext_732_ = lean_ctor_get(v_c_687_, 0);
                lean_inc_ref(v_ext_732_);
                lean_dec_ref(v_c_687_);
                v___x_733_ = l_Lake_ModuleOutputDescrs_toJson___closed__2;
                v___x_734_ = lean_string_utf8_byte_size(v_ext_732_);
                v___x_735_ = lean_unsigned_to_nat(0);
                v___x_736_ = lean_nat_dec_eq(v___x_734_, v___x_735_);
                if v___x_736_ == 0 {
                    v___x_737_ = l_Lake_lowerHexUInt64(v_hash_731_);
                    v___x_738_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0;
                    v___x_739_ = lean_string_append(v___x_737_, v___x_738_);
                    v___x_740_ = lean_string_append(v___x_739_, v_ext_732_);
                    lean_dec_ref(v_ext_732_);
                    v___y_712_ = v___x_733_;
                    v___y_713_ = v_obj_730_;
                    v___y_714_ = v___x_740_;
                    state = 4;
                    continue;
                } else {
                    lean_dec_ref(v_ext_732_);
                    v___x_741_ = l_Lake_lowerHexUInt64(v_hash_731_);
                    v___y_712_ = v___x_733_;
                    v___y_713_ = v_obj_730_;
                    v___y_714_ = v___x_741_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_746_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_746_, 0, v___y_745_);
                lean_inc_ref(v___y_744_);
                v___x_747_ = l_Lake_JsonObject_insertJson(v___y_743_, v___y_744_, v___x_746_);
                v_obj_730_ = v___x_747_;
                state = 5;
                continue;
            }
            7 => {
                v___x_761_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_761_, 0, v___y_760_);
                v___x_762_ = l_Lake_JsonObject_insertJson(v_obj_757_, v___x_758_, v___x_761_);
                if lean_obj_tag(v_ir_x3f_686_) == 1 {
                    v_val_763_ = lean_ctor_get(v_ir_x3f_686_, 0);
                    lean_inc(v_val_763_);
                    lean_dec_ref_known(v_ir_x3f_686_, 1);
                    v_hash_764_ = lean_ctor_get_uint64(
                        v_val_763_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_ext_765_ = lean_ctor_get(v_val_763_, 0);
                    lean_inc_ref(v_ext_765_);
                    lean_dec(v_val_763_);
                    v___x_766_ = l_Lake_ModuleOutputDescrs_toJson___closed__6;
                    v___x_767_ = lean_string_utf8_byte_size(v_ext_765_);
                    v___x_768_ = lean_unsigned_to_nat(0);
                    v___x_769_ = lean_nat_dec_eq(v___x_767_, v___x_768_);
                    if v___x_769_ == 0 {
                        v___x_770_ = l_Lake_lowerHexUInt64(v_hash_764_);
                        v___x_771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lake_ModuleOutputDescrs_toJson_spec__0_spec__0___closed__0;
                        v___x_772_ = lean_string_append(v___x_770_, v___x_771_);
                        v___x_773_ = lean_string_append(v___x_772_, v_ext_765_);
                        lean_dec_ref(v_ext_765_);
                        v___y_743_ = v___x_762_;
                        v___y_744_ = v___x_766_;
                        v___y_745_ = v___x_773_;
                        state = 6;
                        continue;
                    } else {
                        lean_dec_ref(v_ext_765_);
                        v___x_774_ = l_Lake_lowerHexUInt64(v_hash_764_);
                        v___y_743_ = v___x_762_;
                        v___y_744_ = v___x_766_;
                        v___y_745_ = v___x_774_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v_ir_x3f_686_);
                    v_obj_730_ = v___x_762_;
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(
    mut v_x_787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_793_: u8 = 0;
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_797_: u8 = 0;
    let mut v_a_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_801_: u8 = 0;
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_806_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_787_) == 0 {
                    v___x_788_ = l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1___closed__0;
                    return v___x_788_;
                } else {
                    v___x_789_ = l_Lake_ArtifactDescr_fromJson_x3f(v_x_787_);
                    if lean_obj_tag(v___x_789_) == 0 {
                        v_a_790_ = lean_ctor_get(v___x_789_, 0);
                        v_isSharedCheck_797_ = (!lean_is_exclusive(v___x_789_)) as u8;
                        if v_isSharedCheck_797_ == 0 {
                            v___x_792_ = v___x_789_;
                            v_isShared_793_ = v_isSharedCheck_797_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_790_);
                            lean_dec(v___x_789_);
                            v___x_792_ = lean_box(0);
                            v_isShared_793_ = v_isSharedCheck_797_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_798_ = lean_ctor_get(v___x_789_, 0);
                        v_isSharedCheck_806_ = (!lean_is_exclusive(v___x_789_)) as u8;
                        if v_isSharedCheck_806_ == 0 {
                            v___x_800_ = v___x_789_;
                            v_isShared_801_ = v_isSharedCheck_806_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_798_);
                            lean_dec(v___x_789_);
                            v___x_800_ = lean_box(0);
                            v_isShared_801_ = v_isSharedCheck_806_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_793_ == 0 {
                    v___x_795_ = v___x_792_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
                    v___x_795_ = v_reuseFailAlloc_796_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_795_;
            }
            3 => {
                v___x_802_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_802_, 0, v_a_798_);
                if v_isShared_801_ == 0 {
                    lean_ctor_set(v___x_800_, 0, v___x_802_);
                    v___x_804_ = v___x_800_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
                    v___x_804_ = v_reuseFailAlloc_805_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_804_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2(
    mut v_x_809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_815_: u8 = 0;
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_819_: u8 = 0;
    let mut v_a_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_823_: u8 = 0;
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_828_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_809_) == 0 {
                    v___x_810_ = l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___closed__0;
                    return v___x_810_;
                } else {
                    v___x_811_ = l_Lean_Json_getBool_x3f(v_x_809_);
                    if lean_obj_tag(v___x_811_) == 0 {
                        v_a_812_ = lean_ctor_get(v___x_811_, 0);
                        v_isSharedCheck_819_ = (!lean_is_exclusive(v___x_811_)) as u8;
                        if v_isSharedCheck_819_ == 0 {
                            v___x_814_ = v___x_811_;
                            v_isShared_815_ = v_isSharedCheck_819_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_812_);
                            lean_dec(v___x_811_);
                            v___x_814_ = lean_box(0);
                            v_isShared_815_ = v_isSharedCheck_819_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_820_ = lean_ctor_get(v___x_811_, 0);
                        v_isSharedCheck_828_ = (!lean_is_exclusive(v___x_811_)) as u8;
                        if v_isSharedCheck_828_ == 0 {
                            v___x_822_ = v___x_811_;
                            v_isShared_823_ = v_isSharedCheck_828_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_820_);
                            lean_dec(v___x_811_);
                            v___x_822_ = lean_box(0);
                            v_isShared_823_ = v_isSharedCheck_828_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_815_ == 0 {
                    v___x_817_ = v___x_814_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
                    v___x_817_ = v_reuseFailAlloc_818_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_817_;
            }
            3 => {
                v___x_824_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_824_, 0, v_a_820_);
                if v_isShared_823_ == 0 {
                    lean_ctor_set(v___x_822_, 0, v___x_824_);
                    v___x_826_ = v___x_822_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
                    v___x_826_ = v_reuseFailAlloc_827_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_826_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2___boxed(
    mut v_x_829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_830_: *mut LeanObject = core::ptr::null_mut();
    v_res_830_ =
        l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2(v_x_829_);
    lean_dec(v_x_829_);
    return v_res_830_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(
    mut v_sz_831_: usize,
    mut v_i_832_: usize,
    mut v_bs_833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_834_: u8 = 0;
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_841_: u8 = 0;
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_845_: u8 = 0;
    let mut v_a_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: usize = 0;
    let mut v___x_850_: usize = 0;
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_834_ = lean_usize_dec_lt(v_i_832_, v_sz_831_);
                if v___x_834_ == 0 {
                    v___x_835_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_835_, 0, v_bs_833_);
                    return v___x_835_;
                } else {
                    v_v_836_ = lean_array_uget_borrowed(v_bs_833_, v_i_832_);
                    lean_inc(v_v_836_);
                    v___x_837_ = l_Lake_ArtifactDescr_fromJson_x3f(v_v_836_);
                    if lean_obj_tag(v___x_837_) == 0 {
                        lean_dec_ref(v_bs_833_);
                        v_a_838_ = lean_ctor_get(v___x_837_, 0);
                        v_isSharedCheck_845_ = (!lean_is_exclusive(v___x_837_)) as u8;
                        if v_isSharedCheck_845_ == 0 {
                            v___x_840_ = v___x_837_;
                            v_isShared_841_ = v_isSharedCheck_845_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_838_);
                            lean_dec(v___x_837_);
                            v___x_840_ = lean_box(0);
                            v_isShared_841_ = v_isSharedCheck_845_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_846_ = lean_ctor_get(v___x_837_, 0);
                        lean_inc(v_a_846_);
                        lean_dec_ref_known(v___x_837_, 1);
                        v___x_847_ = lean_unsigned_to_nat(0);
                        v_bs_x27_848_ = lean_array_uset(v_bs_833_, v_i_832_, v___x_847_);
                        v___x_849_ = 1usize;
                        v___x_850_ = lean_usize_add(v_i_832_, v___x_849_);
                        v___x_851_ = lean_array_uset(v_bs_x27_848_, v_i_832_, v_a_846_);
                        v_i_832_ = v___x_850_;
                        v_bs_833_ = v___x_851_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_841_ == 0 {
                    v___x_843_ = v___x_840_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
                    v___x_843_ = v_reuseFailAlloc_844_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_843_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0___boxed(
    mut v_sz_853_: *mut LeanObject,
    mut v_i_854_: *mut LeanObject,
    mut v_bs_855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_856_: usize = 0;
    let mut v_i_boxed_857_: usize = 0;
    let mut v_res_858_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_856_ = lean_unbox_usize(v_sz_853_);
    lean_dec(v_sz_853_);
    v_i_boxed_857_ = lean_unbox_usize(v_i_854_);
    lean_dec(v_i_854_);
    v_res_858_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(v_sz_boxed_856_, v_i_boxed_857_, v_bs_855_);
    return v_res_858_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0(
    mut v_x_861_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_861_) == 4 {
        let mut v_elems_862_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_863_: usize = 0;
        let mut v___x_864_: usize = 0;
        let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
        v_elems_862_ = lean_ctor_get(v_x_861_, 0);
        lean_inc_ref(v_elems_862_);
        lean_dec_ref_known(v_x_861_, 1);
        v_sz_863_ = lean_array_size(v_elems_862_);
        v___x_864_ = 0usize;
        v___x_865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0_spec__0(v_sz_863_, v___x_864_, v_elems_862_);
        return v___x_865_;
    } else {
        let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
        v___x_866_ =
            l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__0;
        v___x_867_ = lean_unsigned_to_nat(80);
        v___x_868_ = l_Lean_Json_pretty(v_x_861_, v___x_867_);
        v___x_869_ = lean_string_append(v___x_866_, v___x_868_);
        lean_dec_ref(v___x_868_);
        v___x_870_ =
            l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0___closed__1;
        v___x_871_ = lean_string_append(v___x_869_, v___x_870_);
        v___x_872_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_872_, 0, v___x_871_);
        return v___x_872_;
    }
}
pub unsafe fn l_Lake_ModuleOutputDescrs_fromJson_x3f(
    mut v_val_892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_897_: u8 = 0;
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_901_: u8 = 0;
    let mut v_a_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_909_: u8 = 0;
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_914_: u8 = 0;
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_920_: u8 = 0;
    let mut v_a_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_924_: u8 = 0;
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_928_: u8 = 0;
    let mut v_a_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_932_: u8 = 0;
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: u8 = 0;
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_942_: u8 = 0;
    let mut v___y_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_955_: u8 = 0;
    let mut v___y_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_960_: u8 = 0;
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_972_: u8 = 0;
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: u8 = 0;
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: u8 = 0;
    let mut v_val_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: u8 = 0;
    let mut v___y_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1003_: u8 = 0;
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1009_: u8 = 0;
    let mut v_a_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1013_: u8 = 0;
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1017_: u8 = 0;
    let mut v_a_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1031_: u8 = 0;
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1037_: u8 = 0;
    let mut v_a_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1041_: u8 = 0;
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1045_: u8 = 0;
    let mut v_a_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1055_: u8 = 0;
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1061_: u8 = 0;
    let mut v_a_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1065_: u8 = 0;
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1069_: u8 = 0;
    let mut v_a_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1081_: u8 = 0;
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1087_: u8 = 0;
    let mut v_a_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1091_: u8 = 0;
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1095_: u8 = 0;
    let mut v_a_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1105_: u8 = 0;
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1111_: u8 = 0;
    let mut v_a_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1115_: u8 = 0;
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1119_: u8 = 0;
    let mut v_a_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1129_: u8 = 0;
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1135_: u8 = 0;
    let mut v_a_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1139_: u8 = 0;
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1143_: u8 = 0;
    let mut v_a_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1145_: u8 = 0;
    let mut v_isSharedCheck_1146_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_893_ = l_Lean_Json_getObj_x3f(v_val_892_);
                if lean_obj_tag(v___x_893_) == 0 {
                    v_a_894_ = lean_ctor_get(v___x_893_, 0);
                    v_isSharedCheck_901_ = (!lean_is_exclusive(v___x_893_)) as u8;
                    if v_isSharedCheck_901_ == 0 {
                        v___x_896_ = v___x_893_;
                        v_isShared_897_ = v_isSharedCheck_901_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_894_);
                        lean_dec(v___x_893_);
                        v___x_896_ = lean_box(0);
                        v_isShared_897_ = v_isSharedCheck_901_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_902_ = lean_ctor_get(v___x_893_, 0);
                    lean_inc(v_a_902_);
                    lean_dec_ref_known(v___x_893_, 1);
                    v___x_903_ = l_Lake_ModuleOutputDescrs_toJson___closed__4;
                    v___x_904_ = l_Lake_JsonObject_getJson_x3f(v_a_902_, v___x_903_);
                    if lean_obj_tag(v___x_904_) == 0 {
                        lean_dec(v_a_902_);
                        v___x_905_ = l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__1;
                        return v___x_905_;
                    } else {
                        v_val_906_ = lean_ctor_get(v___x_904_, 0);
                        v_isSharedCheck_1146_ = (!lean_is_exclusive(v___x_904_)) as u8;
                        if v_isSharedCheck_1146_ == 0 {
                            v___x_908_ = v___x_904_;
                            v_isShared_909_ = v_isSharedCheck_1146_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_906_);
                            lean_dec(v___x_904_);
                            v___x_908_ = lean_box(0);
                            v_isShared_909_ = v_isSharedCheck_1146_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_897_ == 0 {
                    v___x_899_ = v___x_896_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
                    v___x_899_ = v_reuseFailAlloc_900_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_899_;
            }
            3 => {
                v___x_910_ =
                    l_Array_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__0(
                        v_val_906_,
                    );
                if lean_obj_tag(v___x_910_) == 0 {
                    lean_del_object(v___x_908_);
                    lean_dec(v_a_902_);
                    v_a_911_ = lean_ctor_get(v___x_910_, 0);
                    v_isSharedCheck_920_ = (!lean_is_exclusive(v___x_910_)) as u8;
                    if v_isSharedCheck_920_ == 0 {
                        v___x_913_ = v___x_910_;
                        v_isShared_914_ = v_isSharedCheck_920_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_911_);
                        lean_dec(v___x_910_);
                        v___x_913_ = lean_box(0);
                        v_isShared_914_ = v_isSharedCheck_920_;
                        state = 4;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_910_) == 0 {
                        lean_del_object(v___x_908_);
                        lean_dec(v_a_902_);
                        v_a_921_ = lean_ctor_get(v___x_910_, 0);
                        v_isSharedCheck_928_ = (!lean_is_exclusive(v___x_910_)) as u8;
                        if v_isSharedCheck_928_ == 0 {
                            v___x_923_ = v___x_910_;
                            v_isShared_924_ = v_isSharedCheck_928_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_921_);
                            lean_dec(v___x_910_);
                            v___x_923_ = lean_box(0);
                            v_isShared_924_ = v_isSharedCheck_928_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_929_ = lean_ctor_get(v___x_910_, 0);
                        v_isSharedCheck_1145_ = (!lean_is_exclusive(v___x_910_)) as u8;
                        if v_isSharedCheck_1145_ == 0 {
                            v___x_931_ = v___x_910_;
                            v_isShared_932_ = v_isSharedCheck_1145_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_929_);
                            lean_dec(v___x_910_);
                            v___x_931_ = lean_box(0);
                            v_isShared_932_ = v_isSharedCheck_1145_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v___x_915_ = l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__2;
                v___x_916_ = lean_string_append(v___x_915_, v_a_911_);
                lean_dec(v_a_911_);
                if v_isShared_914_ == 0 {
                    lean_ctor_set(v___x_913_, 0, v___x_916_);
                    v___x_918_ = v___x_913_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
                    v___x_918_ = v_reuseFailAlloc_919_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_918_;
            }
            6 => {
                if v_isShared_924_ == 0 {
                    lean_ctor_set_tag(v___x_923_, 0);
                    v___x_926_ = v___x_923_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
                    v___x_926_ = v_reuseFailAlloc_927_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_926_;
            }
            8 => {
                v___x_933_ = lean_unsigned_to_nat(0);
                v___x_934_ = lean_array_get_size(v_a_929_);
                v___x_935_ = lean_nat_dec_lt(v___x_933_, v___x_934_);
                if v___x_935_ == 0 {
                    lean_del_object(v___x_931_);
                    lean_dec(v_a_929_);
                    lean_del_object(v___x_908_);
                    lean_dec(v_a_902_);
                    v___x_936_ = l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__4;
                    return v___x_936_;
                } else {
                    v___x_937_ = lean_array_fget(v_a_929_, v___x_933_);
                    v___x_1121_ = l_Lake_ModuleOutputDescrs_toJson___closed__3;
                    v___x_1122_ = l_Lake_JsonObject_getJson_x3f(v_a_902_, v___x_1121_);
                    if lean_obj_tag(v___x_1122_) == 0 {
                        v___x_1123_ = lean_box(0);
                        v_a_1072_ = v___x_1123_;
                        state = 29;
                        continue;
                    } else {
                        v_val_1124_ = lean_ctor_get(v___x_1122_, 0);
                        lean_inc(v_val_1124_);
                        lean_dec_ref_known(v___x_1122_, 1);
                        v___x_1125_ = l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__2(v_val_1124_);
                        lean_dec(v_val_1124_);
                        if lean_obj_tag(v___x_1125_) == 0 {
                            lean_dec(v___x_937_);
                            lean_del_object(v___x_931_);
                            lean_dec(v_a_929_);
                            lean_del_object(v___x_908_);
                            lean_dec(v_a_902_);
                            v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
                            v_isSharedCheck_1135_ = (!lean_is_exclusive(v___x_1125_)) as u8;
                            if v_isSharedCheck_1135_ == 0 {
                                v___x_1128_ = v___x_1125_;
                                v_isShared_1129_ = v_isSharedCheck_1135_;
                                state = 38;
                                continue;
                            } else {
                                lean_inc(v_a_1126_);
                                lean_dec(v___x_1125_);
                                v___x_1128_ = lean_box(0);
                                v_isShared_1129_ = v_isSharedCheck_1135_;
                                state = 38;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_1125_) == 0 {
                                lean_dec(v___x_937_);
                                lean_del_object(v___x_931_);
                                lean_dec(v_a_929_);
                                lean_del_object(v___x_908_);
                                lean_dec(v_a_902_);
                                v_a_1136_ = lean_ctor_get(v___x_1125_, 0);
                                v_isSharedCheck_1143_ = (!lean_is_exclusive(v___x_1125_)) as u8;
                                if v_isSharedCheck_1143_ == 0 {
                                    v___x_1138_ = v___x_1125_;
                                    v_isShared_1139_ = v_isSharedCheck_1143_;
                                    state = 40;
                                    continue;
                                } else {
                                    lean_inc(v_a_1136_);
                                    lean_dec(v___x_1125_);
                                    v___x_1138_ = lean_box(0);
                                    v_isShared_1139_ = v_isSharedCheck_1143_;
                                    state = 40;
                                    continue;
                                }
                            } else {
                                v_a_1144_ = lean_ctor_get(v___x_1125_, 0);
                                lean_inc(v_a_1144_);
                                lean_dec_ref_known(v___x_1125_, 1);
                                v_a_1072_ = v_a_1144_;
                                state = 29;
                                continue;
                            }
                        }
                    }
                }
            }
            9 => {
                v___x_947_ = lean_alloc_ctor(0, 8, (1) as u32);
                lean_ctor_set(v___x_947_, 0, v___x_937_);
                lean_ctor_set(v___x_947_, 1, v___y_945_);
                lean_ctor_set(v___x_947_, 2, v___y_946_);
                lean_ctor_set(v___x_947_, 3, v___y_944_);
                lean_ctor_set(v___x_947_, 4, v___y_940_);
                lean_ctor_set(v___x_947_, 5, v___y_943_);
                lean_ctor_set(v___x_947_, 6, v___y_939_);
                lean_ctor_set(v___x_947_, 7, v___y_941_);
                lean_ctor_set_uint8(
                    v___x_947_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    v___y_942_,
                );
                if v_isShared_932_ == 0 {
                    lean_ctor_set(v___x_931_, 0, v___x_947_);
                    v___x_949_ = v___x_931_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_947_);
                    v___x_949_ = v_reuseFailAlloc_950_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_949_;
            }
            11 => {
                v___x_959_ = lean_unsigned_to_nat(2);
                v___x_960_ = lean_nat_dec_lt(v___x_959_, v___x_934_);
                if v___x_960_ == 0 {
                    lean_dec(v_a_929_);
                    lean_del_object(v___x_908_);
                    v___x_961_ = lean_box(0);
                    v___y_939_ = v___y_952_;
                    v___y_940_ = v___y_953_;
                    v___y_941_ = v___y_954_;
                    v___y_942_ = v___y_955_;
                    v___y_943_ = v___y_956_;
                    v___y_944_ = v___y_957_;
                    v___y_945_ = v___y_958_;
                    v___y_946_ = v___x_961_;
                    state = 9;
                    continue;
                } else {
                    v___x_962_ = lean_array_fget(v_a_929_, v___x_959_);
                    lean_dec(v_a_929_);
                    if v_isShared_909_ == 0 {
                        lean_ctor_set(v___x_908_, 0, v___x_962_);
                        v___x_964_ = v___x_908_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
                        v___x_964_ = v_reuseFailAlloc_965_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                v___y_939_ = v___y_952_;
                v___y_940_ = v___y_953_;
                v___y_941_ = v___y_954_;
                v___y_942_ = v___y_955_;
                v___y_943_ = v___y_956_;
                v___y_944_ = v___y_957_;
                v___y_945_ = v___y_958_;
                v___y_946_ = v___x_964_;
                state = 9;
                continue;
            }
            13 => {
                v___x_973_ = lean_unsigned_to_nat(1);
                v___x_974_ = lean_nat_dec_lt(v___x_973_, v___x_934_);
                if v___x_974_ == 0 {
                    v___x_975_ = lean_box(0);
                    v___y_952_ = v___y_967_;
                    v___y_953_ = v___y_968_;
                    v___y_954_ = v___y_969_;
                    v___y_955_ = v___y_972_;
                    v___y_956_ = v___y_970_;
                    v___y_957_ = v___y_971_;
                    v___y_958_ = v___x_975_;
                    state = 11;
                    continue;
                } else {
                    v___x_976_ = lean_array_fget_borrowed(v_a_929_, v___x_973_);
                    lean_inc(v___x_976_);
                    v___x_977_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_977_, 0, v___x_976_);
                    v___y_952_ = v___y_967_;
                    v___y_953_ = v___y_968_;
                    v___y_954_ = v___y_969_;
                    v___y_955_ = v___y_972_;
                    v___y_956_ = v___y_970_;
                    v___y_957_ = v___y_971_;
                    v___y_958_ = v___x_977_;
                    state = 11;
                    continue;
                }
            }
            14 => {
                if lean_obj_tag(v___y_981_) == 0 {
                    v___x_985_ = lean_unsigned_to_nat(1);
                    v___x_986_ = lean_nat_dec_lt(v___x_985_, v___x_934_);
                    v___y_967_ = v___y_979_;
                    v___y_968_ = v___y_980_;
                    v___y_969_ = v_a_984_;
                    v___y_970_ = v___y_982_;
                    v___y_971_ = v___y_983_;
                    v___y_972_ = v___x_986_;
                    state = 13;
                    continue;
                } else {
                    v_val_987_ = lean_ctor_get(v___y_981_, 0);
                    lean_inc(v_val_987_);
                    lean_dec_ref_known(v___y_981_, 1);
                    v___x_988_ = (lean_unbox(v_val_987_) as u8);
                    lean_dec(v_val_987_);
                    v___y_967_ = v___y_979_;
                    v___y_968_ = v___y_980_;
                    v___y_969_ = v_a_984_;
                    v___y_970_ = v___y_982_;
                    v___y_971_ = v___y_983_;
                    v___y_972_ = v___x_988_;
                    state = 13;
                    continue;
                }
            }
            15 => {
                v___x_995_ = l_Lake_ModuleOutputDescrs_toJson___closed__0;
                v___x_996_ = l_Lake_JsonObject_getJson_x3f(v_a_902_, v___x_995_);
                lean_dec(v_a_902_);
                if lean_obj_tag(v___x_996_) == 0 {
                    v___x_997_ = lean_box(0);
                    v___y_979_ = v_a_994_;
                    v___y_980_ = v___y_990_;
                    v___y_981_ = v___y_991_;
                    v___y_982_ = v___y_992_;
                    v___y_983_ = v___y_993_;
                    v_a_984_ = v___x_997_;
                    state = 14;
                    continue;
                } else {
                    v_val_998_ = lean_ctor_get(v___x_996_, 0);
                    lean_inc(v_val_998_);
                    lean_dec_ref_known(v___x_996_, 1);
                    v___x_999_ =
                        l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(
                            v_val_998_,
                        );
                    if lean_obj_tag(v___x_999_) == 0 {
                        lean_dec(v_a_994_);
                        lean_dec_ref(v___y_993_);
                        lean_dec_ref(v___y_992_);
                        lean_dec(v___y_991_);
                        lean_dec(v___y_990_);
                        lean_dec(v___x_937_);
                        lean_del_object(v___x_931_);
                        lean_dec(v_a_929_);
                        lean_del_object(v___x_908_);
                        v_a_1000_ = lean_ctor_get(v___x_999_, 0);
                        v_isSharedCheck_1009_ = (!lean_is_exclusive(v___x_999_)) as u8;
                        if v_isSharedCheck_1009_ == 0 {
                            v___x_1002_ = v___x_999_;
                            v_isShared_1003_ = v_isSharedCheck_1009_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_a_1000_);
                            lean_dec(v___x_999_);
                            v___x_1002_ = lean_box(0);
                            v_isShared_1003_ = v_isSharedCheck_1009_;
                            state = 16;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v___x_999_) == 0 {
                            lean_dec(v_a_994_);
                            lean_dec_ref(v___y_993_);
                            lean_dec_ref(v___y_992_);
                            lean_dec(v___y_991_);
                            lean_dec(v___y_990_);
                            lean_dec(v___x_937_);
                            lean_del_object(v___x_931_);
                            lean_dec(v_a_929_);
                            lean_del_object(v___x_908_);
                            v_a_1010_ = lean_ctor_get(v___x_999_, 0);
                            v_isSharedCheck_1017_ = (!lean_is_exclusive(v___x_999_)) as u8;
                            if v_isSharedCheck_1017_ == 0 {
                                v___x_1012_ = v___x_999_;
                                v_isShared_1013_ = v_isSharedCheck_1017_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_a_1010_);
                                lean_dec(v___x_999_);
                                v___x_1012_ = lean_box(0);
                                v_isShared_1013_ = v_isSharedCheck_1017_;
                                state = 18;
                                continue;
                            }
                        } else {
                            v_a_1018_ = lean_ctor_get(v___x_999_, 0);
                            lean_inc(v_a_1018_);
                            lean_dec_ref_known(v___x_999_, 1);
                            v___y_979_ = v_a_994_;
                            v___y_980_ = v___y_990_;
                            v___y_981_ = v___y_991_;
                            v___y_982_ = v___y_992_;
                            v___y_983_ = v___y_993_;
                            v_a_984_ = v_a_1018_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            16 => {
                v___x_1004_ = l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__5;
                v___x_1005_ = lean_string_append(v___x_1004_, v_a_1000_);
                lean_dec(v_a_1000_);
                if v_isShared_1003_ == 0 {
                    lean_ctor_set(v___x_1002_, 0, v___x_1005_);
                    v___x_1007_ = v___x_1002_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1005_);
                    v___x_1007_ = v_reuseFailAlloc_1008_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1007_;
            }
            18 => {
                if v_isShared_1013_ == 0 {
                    lean_ctor_set_tag(v___x_1012_, 0);
                    v___x_1015_ = v___x_1012_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
                    v___x_1015_ = v_reuseFailAlloc_1016_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1015_;
            }
            20 => {
                v___x_1023_ = l_Lake_ModuleOutputDescrs_toJson___closed__2;
                v___x_1024_ = l_Lake_JsonObject_getJson_x3f(v_a_902_, v___x_1023_);
                if lean_obj_tag(v___x_1024_) == 0 {
                    lean_dec(v_a_1022_);
                    lean_dec_ref(v___y_1021_);
                    lean_dec(v___y_1020_);
                    lean_dec(v___x_937_);
                    lean_del_object(v___x_931_);
                    lean_dec(v_a_929_);
                    lean_del_object(v___x_908_);
                    lean_dec(v_a_902_);
                    v___x_1025_ = l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__7;
                    return v___x_1025_;
                } else {
                    v_val_1026_ = lean_ctor_get(v___x_1024_, 0);
                    lean_inc(v_val_1026_);
                    lean_dec_ref_known(v___x_1024_, 1);
                    v___x_1027_ = l_Lake_ArtifactDescr_fromJson_x3f(v_val_1026_);
                    if lean_obj_tag(v___x_1027_) == 0 {
                        lean_dec(v_a_1022_);
                        lean_dec_ref(v___y_1021_);
                        lean_dec(v___y_1020_);
                        lean_dec(v___x_937_);
                        lean_del_object(v___x_931_);
                        lean_dec(v_a_929_);
                        lean_del_object(v___x_908_);
                        lean_dec(v_a_902_);
                        v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
                        v_isSharedCheck_1037_ = (!lean_is_exclusive(v___x_1027_)) as u8;
                        if v_isSharedCheck_1037_ == 0 {
                            v___x_1030_ = v___x_1027_;
                            v_isShared_1031_ = v_isSharedCheck_1037_;
                            state = 21;
                            continue;
                        } else {
                            lean_inc(v_a_1028_);
                            lean_dec(v___x_1027_);
                            v___x_1030_ = lean_box(0);
                            v_isShared_1031_ = v_isSharedCheck_1037_;
                            state = 21;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v___x_1027_) == 0 {
                            lean_dec(v_a_1022_);
                            lean_dec_ref(v___y_1021_);
                            lean_dec(v___y_1020_);
                            lean_dec(v___x_937_);
                            lean_del_object(v___x_931_);
                            lean_dec(v_a_929_);
                            lean_del_object(v___x_908_);
                            lean_dec(v_a_902_);
                            v_a_1038_ = lean_ctor_get(v___x_1027_, 0);
                            v_isSharedCheck_1045_ = (!lean_is_exclusive(v___x_1027_)) as u8;
                            if v_isSharedCheck_1045_ == 0 {
                                v___x_1040_ = v___x_1027_;
                                v_isShared_1041_ = v_isSharedCheck_1045_;
                                state = 23;
                                continue;
                            } else {
                                lean_inc(v_a_1038_);
                                lean_dec(v___x_1027_);
                                v___x_1040_ = lean_box(0);
                                v_isShared_1041_ = v_isSharedCheck_1045_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v_a_1046_ = lean_ctor_get(v___x_1027_, 0);
                            lean_inc(v_a_1046_);
                            lean_dec_ref_known(v___x_1027_, 1);
                            v___x_1047_ = l_Lake_ModuleOutputDescrs_toJson___closed__1;
                            v___x_1048_ = l_Lake_JsonObject_getJson_x3f(v_a_902_, v___x_1047_);
                            if lean_obj_tag(v___x_1048_) == 0 {
                                v___x_1049_ = lean_box(0);
                                v___y_990_ = v_a_1022_;
                                v___y_991_ = v___y_1020_;
                                v___y_992_ = v_a_1046_;
                                v___y_993_ = v___y_1021_;
                                v_a_994_ = v___x_1049_;
                                state = 15;
                                continue;
                            } else {
                                v_val_1050_ = lean_ctor_get(v___x_1048_, 0);
                                lean_inc(v_val_1050_);
                                lean_dec_ref_known(v___x_1048_, 1);
                                v___x_1051_ = l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_1050_);
                                if lean_obj_tag(v___x_1051_) == 0 {
                                    lean_dec(v_a_1046_);
                                    lean_dec(v_a_1022_);
                                    lean_dec_ref(v___y_1021_);
                                    lean_dec(v___y_1020_);
                                    lean_dec(v___x_937_);
                                    lean_del_object(v___x_931_);
                                    lean_dec(v_a_929_);
                                    lean_del_object(v___x_908_);
                                    lean_dec(v_a_902_);
                                    v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
                                    v_isSharedCheck_1061_ = (!lean_is_exclusive(v___x_1051_)) as u8;
                                    if v_isSharedCheck_1061_ == 0 {
                                        v___x_1054_ = v___x_1051_;
                                        v_isShared_1055_ = v_isSharedCheck_1061_;
                                        state = 25;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1052_);
                                        lean_dec(v___x_1051_);
                                        v___x_1054_ = lean_box(0);
                                        v_isShared_1055_ = v_isSharedCheck_1061_;
                                        state = 25;
                                        continue;
                                    }
                                } else {
                                    if lean_obj_tag(v___x_1051_) == 0 {
                                        lean_dec(v_a_1046_);
                                        lean_dec(v_a_1022_);
                                        lean_dec_ref(v___y_1021_);
                                        lean_dec(v___y_1020_);
                                        lean_dec(v___x_937_);
                                        lean_del_object(v___x_931_);
                                        lean_dec(v_a_929_);
                                        lean_del_object(v___x_908_);
                                        lean_dec(v_a_902_);
                                        v_a_1062_ = lean_ctor_get(v___x_1051_, 0);
                                        v_isSharedCheck_1069_ =
                                            (!lean_is_exclusive(v___x_1051_)) as u8;
                                        if v_isSharedCheck_1069_ == 0 {
                                            v___x_1064_ = v___x_1051_;
                                            v_isShared_1065_ = v_isSharedCheck_1069_;
                                            state = 27;
                                            continue;
                                        } else {
                                            lean_inc(v_a_1062_);
                                            lean_dec(v___x_1051_);
                                            v___x_1064_ = lean_box(0);
                                            v_isShared_1065_ = v_isSharedCheck_1069_;
                                            state = 27;
                                            continue;
                                        }
                                    } else {
                                        v_a_1070_ = lean_ctor_get(v___x_1051_, 0);
                                        lean_inc(v_a_1070_);
                                        lean_dec_ref_known(v___x_1051_, 1);
                                        v___y_990_ = v_a_1022_;
                                        v___y_991_ = v___y_1020_;
                                        v___y_992_ = v_a_1046_;
                                        v___y_993_ = v___y_1021_;
                                        v_a_994_ = v_a_1070_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            21 => {
                v___x_1032_ = l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__8;
                v___x_1033_ = lean_string_append(v___x_1032_, v_a_1028_);
                lean_dec(v_a_1028_);
                if v_isShared_1031_ == 0 {
                    lean_ctor_set(v___x_1030_, 0, v___x_1033_);
                    v___x_1035_ = v___x_1030_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1033_);
                    v___x_1035_ = v_reuseFailAlloc_1036_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_1035_;
            }
            23 => {
                if v_isShared_1041_ == 0 {
                    lean_ctor_set_tag(v___x_1040_, 0);
                    v___x_1043_ = v___x_1040_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
                    v___x_1043_ = v_reuseFailAlloc_1044_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1043_;
            }
            25 => {
                v___x_1056_ = l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__9;
                v___x_1057_ = lean_string_append(v___x_1056_, v_a_1052_);
                lean_dec(v_a_1052_);
                if v_isShared_1055_ == 0 {
                    lean_ctor_set(v___x_1054_, 0, v___x_1057_);
                    v___x_1059_ = v___x_1054_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
                    v___x_1059_ = v_reuseFailAlloc_1060_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_1059_;
            }
            27 => {
                if v_isShared_1065_ == 0 {
                    lean_ctor_set_tag(v___x_1064_, 0);
                    v___x_1067_ = v___x_1064_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
                    v___x_1067_ = v_reuseFailAlloc_1068_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_1067_;
            }
            29 => {
                v___x_1073_ = l_Lake_ModuleOutputDescrs_toJson___closed__5;
                v___x_1074_ = l_Lake_JsonObject_getJson_x3f(v_a_902_, v___x_1073_);
                if lean_obj_tag(v___x_1074_) == 0 {
                    lean_dec(v_a_1072_);
                    lean_dec(v___x_937_);
                    lean_del_object(v___x_931_);
                    lean_dec(v_a_929_);
                    lean_del_object(v___x_908_);
                    lean_dec(v_a_902_);
                    v___x_1075_ = l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__11;
                    return v___x_1075_;
                } else {
                    v_val_1076_ = lean_ctor_get(v___x_1074_, 0);
                    lean_inc(v_val_1076_);
                    lean_dec_ref_known(v___x_1074_, 1);
                    v___x_1077_ = l_Lake_ArtifactDescr_fromJson_x3f(v_val_1076_);
                    if lean_obj_tag(v___x_1077_) == 0 {
                        lean_dec(v_a_1072_);
                        lean_dec(v___x_937_);
                        lean_del_object(v___x_931_);
                        lean_dec(v_a_929_);
                        lean_del_object(v___x_908_);
                        lean_dec(v_a_902_);
                        v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
                        v_isSharedCheck_1087_ = (!lean_is_exclusive(v___x_1077_)) as u8;
                        if v_isSharedCheck_1087_ == 0 {
                            v___x_1080_ = v___x_1077_;
                            v_isShared_1081_ = v_isSharedCheck_1087_;
                            state = 30;
                            continue;
                        } else {
                            lean_inc(v_a_1078_);
                            lean_dec(v___x_1077_);
                            v___x_1080_ = lean_box(0);
                            v_isShared_1081_ = v_isSharedCheck_1087_;
                            state = 30;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v___x_1077_) == 0 {
                            lean_dec(v_a_1072_);
                            lean_dec(v___x_937_);
                            lean_del_object(v___x_931_);
                            lean_dec(v_a_929_);
                            lean_del_object(v___x_908_);
                            lean_dec(v_a_902_);
                            v_a_1088_ = lean_ctor_get(v___x_1077_, 0);
                            v_isSharedCheck_1095_ = (!lean_is_exclusive(v___x_1077_)) as u8;
                            if v_isSharedCheck_1095_ == 0 {
                                v___x_1090_ = v___x_1077_;
                                v_isShared_1091_ = v_isSharedCheck_1095_;
                                state = 32;
                                continue;
                            } else {
                                lean_inc(v_a_1088_);
                                lean_dec(v___x_1077_);
                                v___x_1090_ = lean_box(0);
                                v_isShared_1091_ = v_isSharedCheck_1095_;
                                state = 32;
                                continue;
                            }
                        } else {
                            v_a_1096_ = lean_ctor_get(v___x_1077_, 0);
                            lean_inc(v_a_1096_);
                            lean_dec_ref_known(v___x_1077_, 1);
                            v___x_1097_ = l_Lake_ModuleOutputDescrs_toJson___closed__6;
                            v___x_1098_ = l_Lake_JsonObject_getJson_x3f(v_a_902_, v___x_1097_);
                            if lean_obj_tag(v___x_1098_) == 0 {
                                v___x_1099_ = lean_box(0);
                                v___y_1020_ = v_a_1072_;
                                v___y_1021_ = v_a_1096_;
                                v_a_1022_ = v___x_1099_;
                                state = 20;
                                continue;
                            } else {
                                v_val_1100_ = lean_ctor_get(v___x_1098_, 0);
                                lean_inc(v_val_1100_);
                                lean_dec_ref_known(v___x_1098_, 1);
                                v___x_1101_ = l_Option_fromJson_x3f___at___00Lake_ModuleOutputDescrs_fromJson_x3f_spec__1(v_val_1100_);
                                if lean_obj_tag(v___x_1101_) == 0 {
                                    lean_dec(v_a_1096_);
                                    lean_dec(v_a_1072_);
                                    lean_dec(v___x_937_);
                                    lean_del_object(v___x_931_);
                                    lean_dec(v_a_929_);
                                    lean_del_object(v___x_908_);
                                    lean_dec(v_a_902_);
                                    v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
                                    v_isSharedCheck_1111_ = (!lean_is_exclusive(v___x_1101_)) as u8;
                                    if v_isSharedCheck_1111_ == 0 {
                                        v___x_1104_ = v___x_1101_;
                                        v_isShared_1105_ = v_isSharedCheck_1111_;
                                        state = 34;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1102_);
                                        lean_dec(v___x_1101_);
                                        v___x_1104_ = lean_box(0);
                                        v_isShared_1105_ = v_isSharedCheck_1111_;
                                        state = 34;
                                        continue;
                                    }
                                } else {
                                    if lean_obj_tag(v___x_1101_) == 0 {
                                        lean_dec(v_a_1096_);
                                        lean_dec(v_a_1072_);
                                        lean_dec(v___x_937_);
                                        lean_del_object(v___x_931_);
                                        lean_dec(v_a_929_);
                                        lean_del_object(v___x_908_);
                                        lean_dec(v_a_902_);
                                        v_a_1112_ = lean_ctor_get(v___x_1101_, 0);
                                        v_isSharedCheck_1119_ =
                                            (!lean_is_exclusive(v___x_1101_)) as u8;
                                        if v_isSharedCheck_1119_ == 0 {
                                            v___x_1114_ = v___x_1101_;
                                            v_isShared_1115_ = v_isSharedCheck_1119_;
                                            state = 36;
                                            continue;
                                        } else {
                                            lean_inc(v_a_1112_);
                                            lean_dec(v___x_1101_);
                                            v___x_1114_ = lean_box(0);
                                            v_isShared_1115_ = v_isSharedCheck_1119_;
                                            state = 36;
                                            continue;
                                        }
                                    } else {
                                        v_a_1120_ = lean_ctor_get(v___x_1101_, 0);
                                        lean_inc(v_a_1120_);
                                        lean_dec_ref_known(v___x_1101_, 1);
                                        v___y_1020_ = v_a_1072_;
                                        v___y_1021_ = v_a_1096_;
                                        v_a_1022_ = v_a_1120_;
                                        state = 20;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            30 => {
                v___x_1082_ = l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__12;
                v___x_1083_ = lean_string_append(v___x_1082_, v_a_1078_);
                lean_dec(v_a_1078_);
                if v_isShared_1081_ == 0 {
                    lean_ctor_set(v___x_1080_, 0, v___x_1083_);
                    v___x_1085_ = v___x_1080_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
                    v___x_1085_ = v_reuseFailAlloc_1086_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_1085_;
            }
            32 => {
                if v_isShared_1091_ == 0 {
                    lean_ctor_set_tag(v___x_1090_, 0);
                    v___x_1093_ = v___x_1090_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
                    v___x_1093_ = v_reuseFailAlloc_1094_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1093_;
            }
            34 => {
                v___x_1106_ = l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__13;
                v___x_1107_ = lean_string_append(v___x_1106_, v_a_1102_);
                lean_dec(v_a_1102_);
                if v_isShared_1105_ == 0 {
                    lean_ctor_set(v___x_1104_, 0, v___x_1107_);
                    v___x_1109_ = v___x_1104_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
                    v___x_1109_ = v_reuseFailAlloc_1110_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_1109_;
            }
            36 => {
                if v_isShared_1115_ == 0 {
                    lean_ctor_set_tag(v___x_1114_, 0);
                    v___x_1117_ = v___x_1114_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
                    v___x_1117_ = v_reuseFailAlloc_1118_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_1117_;
            }
            38 => {
                v___x_1130_ = l_Lake_ModuleOutputDescrs_fromJson_x3f___closed__14;
                v___x_1131_ = lean_string_append(v___x_1130_, v_a_1126_);
                lean_dec(v_a_1126_);
                if v_isShared_1129_ == 0 {
                    lean_ctor_set(v___x_1128_, 0, v___x_1131_);
                    v___x_1133_ = v___x_1128_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1131_);
                    v___x_1133_ = v_reuseFailAlloc_1134_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_1133_;
            }
            40 => {
                if v_isShared_1139_ == 0 {
                    lean_ctor_set_tag(v___x_1138_, 0);
                    v___x_1141_ = v___x_1138_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
                    v___x_1141_ = v_reuseFailAlloc_1142_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_1141_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_ModuleOutputArtifacts_descrs(
    mut v_arts_1149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_olean_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_1151_: u8 = 0;
    let mut v_oleanServer_x3f_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_oleanPrivate_x3f_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ilean_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ir_x3f_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bc_x3f_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltar_x3f_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1161_: u8 = 0;
    let mut v_descr_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1177_: u8 = 0;
    let mut v_descr_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1185_: u8 = 0;
    let mut v___y_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1196_: u8 = 0;
    let mut v_descr_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1202_: u8 = 0;
    let mut v___y_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1211_: u8 = 0;
    let mut v_descr_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1217_: u8 = 0;
    let mut v___y_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1224_: u8 = 0;
    let mut v_descr_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1229_: u8 = 0;
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1234_: u8 = 0;
    let mut v_descr_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1239_: u8 = 0;
    let mut v_isSharedCheck_1240_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_olean_1150_ = lean_ctor_get(v_arts_1149_, 0);
                v_isModule_1151_ = lean_ctor_get_uint8(
                    v_arts_1149_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                v_oleanServer_x3f_1152_ = lean_ctor_get(v_arts_1149_, 1);
                v_oleanPrivate_x3f_1153_ = lean_ctor_get(v_arts_1149_, 2);
                v_ilean_1154_ = lean_ctor_get(v_arts_1149_, 3);
                v_ir_x3f_1155_ = lean_ctor_get(v_arts_1149_, 4);
                v_c_1156_ = lean_ctor_get(v_arts_1149_, 5);
                v_bc_x3f_1157_ = lean_ctor_get(v_arts_1149_, 6);
                v_ltar_x3f_1158_ = lean_ctor_get(v_arts_1149_, 7);
                v_isSharedCheck_1240_ = (!lean_is_exclusive(v_arts_1149_)) as u8;
                if v_isSharedCheck_1240_ == 0 {
                    v___x_1160_ = v_arts_1149_;
                    v_isShared_1161_ = v_isSharedCheck_1240_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_ltar_x3f_1158_);
                    lean_inc(v_bc_x3f_1157_);
                    lean_inc(v_c_1156_);
                    lean_inc(v_ir_x3f_1155_);
                    lean_inc(v_ilean_1154_);
                    lean_inc(v_oleanPrivate_x3f_1153_);
                    lean_inc(v_oleanServer_x3f_1152_);
                    lean_inc(v_olean_1150_);
                    lean_dec(v_arts_1149_);
                    v___x_1160_ = lean_box(0);
                    v_isShared_1161_ = v_isSharedCheck_1240_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_descr_1162_ = lean_ctor_get(v_olean_1150_, 0);
                lean_inc_ref(v_descr_1162_);
                lean_dec_ref(v_olean_1150_);
                if lean_obj_tag(v_oleanServer_x3f_1152_) == 0 {
                    v___x_1230_ = lean_box(0);
                    v___y_1219_ = v___x_1230_;
                    state = 13;
                    continue;
                } else {
                    v_val_1231_ = lean_ctor_get(v_oleanServer_x3f_1152_, 0);
                    v_isSharedCheck_1239_ = (!lean_is_exclusive(v_oleanServer_x3f_1152_)) as u8;
                    if v_isSharedCheck_1239_ == 0 {
                        v___x_1233_ = v_oleanServer_x3f_1152_;
                        v_isShared_1234_ = v_isSharedCheck_1239_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_val_1231_);
                        lean_dec(v_oleanServer_x3f_1152_);
                        v___x_1233_ = lean_box(0);
                        v_isShared_1234_ = v_isSharedCheck_1239_;
                        state = 16;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_ltar_x3f_1158_) == 0 {
                    v___x_1170_ = lean_box(0);
                    if v_isShared_1161_ == 0 {
                        lean_ctor_set(v___x_1160_, 7, v___x_1170_);
                        lean_ctor_set(v___x_1160_, 6, v___y_1169_);
                        lean_ctor_set(v___x_1160_, 5, v___y_1165_);
                        lean_ctor_set(v___x_1160_, 4, v___y_1164_);
                        lean_ctor_set(v___x_1160_, 3, v___y_1168_);
                        lean_ctor_set(v___x_1160_, 2, v___y_1166_);
                        lean_ctor_set(v___x_1160_, 1, v___y_1167_);
                        lean_ctor_set(v___x_1160_, 0, v_descr_1162_);
                        v___x_1172_ = v___x_1160_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 8, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_descr_1162_);
                        lean_ctor_set(v_reuseFailAlloc_1173_, 1, v___y_1167_);
                        lean_ctor_set(v_reuseFailAlloc_1173_, 2, v___y_1166_);
                        lean_ctor_set(v_reuseFailAlloc_1173_, 3, v___y_1168_);
                        lean_ctor_set(v_reuseFailAlloc_1173_, 4, v___y_1164_);
                        lean_ctor_set(v_reuseFailAlloc_1173_, 5, v___y_1165_);
                        lean_ctor_set(v_reuseFailAlloc_1173_, 6, v___y_1169_);
                        lean_ctor_set(v_reuseFailAlloc_1173_, 7, v___x_1170_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1173_,
                            (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                            v_isModule_1151_,
                        );
                        v___x_1172_ = v_reuseFailAlloc_1173_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_val_1174_ = lean_ctor_get(v_ltar_x3f_1158_, 0);
                    v_isSharedCheck_1185_ = (!lean_is_exclusive(v_ltar_x3f_1158_)) as u8;
                    if v_isSharedCheck_1185_ == 0 {
                        v___x_1176_ = v_ltar_x3f_1158_;
                        v_isShared_1177_ = v_isSharedCheck_1185_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_1174_);
                        lean_dec(v_ltar_x3f_1158_);
                        v___x_1176_ = lean_box(0);
                        v_isShared_1177_ = v_isSharedCheck_1185_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1172_;
            }
            4 => {
                v_descr_1178_ = lean_ctor_get(v_val_1174_, 0);
                lean_inc_ref(v_descr_1178_);
                lean_dec(v_val_1174_);
                if v_isShared_1177_ == 0 {
                    lean_ctor_set(v___x_1176_, 0, v_descr_1178_);
                    v___x_1180_ = v___x_1176_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_descr_1178_);
                    v___x_1180_ = v_reuseFailAlloc_1184_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1161_ == 0 {
                    lean_ctor_set(v___x_1160_, 7, v___x_1180_);
                    lean_ctor_set(v___x_1160_, 6, v___y_1169_);
                    lean_ctor_set(v___x_1160_, 5, v___y_1165_);
                    lean_ctor_set(v___x_1160_, 4, v___y_1164_);
                    lean_ctor_set(v___x_1160_, 3, v___y_1168_);
                    lean_ctor_set(v___x_1160_, 2, v___y_1166_);
                    lean_ctor_set(v___x_1160_, 1, v___y_1167_);
                    lean_ctor_set(v___x_1160_, 0, v_descr_1162_);
                    v___x_1182_ = v___x_1160_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 8, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_descr_1162_);
                    lean_ctor_set(v_reuseFailAlloc_1183_, 1, v___y_1167_);
                    lean_ctor_set(v_reuseFailAlloc_1183_, 2, v___y_1166_);
                    lean_ctor_set(v_reuseFailAlloc_1183_, 3, v___y_1168_);
                    lean_ctor_set(v_reuseFailAlloc_1183_, 4, v___y_1164_);
                    lean_ctor_set(v_reuseFailAlloc_1183_, 5, v___y_1165_);
                    lean_ctor_set(v_reuseFailAlloc_1183_, 6, v___y_1169_);
                    lean_ctor_set(v_reuseFailAlloc_1183_, 7, v___x_1180_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1183_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                        v_isModule_1151_,
                    );
                    v___x_1182_ = v_reuseFailAlloc_1183_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1182_;
            }
            7 => {
                if lean_obj_tag(v_bc_x3f_1157_) == 0 {
                    v_descr_1191_ = lean_ctor_get(v_c_1156_, 0);
                    lean_inc_ref(v_descr_1191_);
                    lean_dec_ref(v_c_1156_);
                    v___x_1192_ = lean_box(0);
                    v___y_1164_ = v___y_1190_;
                    v___y_1165_ = v_descr_1191_;
                    v___y_1166_ = v___y_1188_;
                    v___y_1167_ = v___y_1187_;
                    v___y_1168_ = v___y_1189_;
                    v___y_1169_ = v___x_1192_;
                    state = 2;
                    continue;
                } else {
                    v_val_1193_ = lean_ctor_get(v_bc_x3f_1157_, 0);
                    v_isSharedCheck_1202_ = (!lean_is_exclusive(v_bc_x3f_1157_)) as u8;
                    if v_isSharedCheck_1202_ == 0 {
                        v___x_1195_ = v_bc_x3f_1157_;
                        v_isShared_1196_ = v_isSharedCheck_1202_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_val_1193_);
                        lean_dec(v_bc_x3f_1157_);
                        v___x_1195_ = lean_box(0);
                        v_isShared_1196_ = v_isSharedCheck_1202_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                v_descr_1197_ = lean_ctor_get(v_c_1156_, 0);
                lean_inc_ref(v_descr_1197_);
                lean_dec_ref(v_c_1156_);
                v_descr_1198_ = lean_ctor_get(v_val_1193_, 0);
                lean_inc_ref(v_descr_1198_);
                lean_dec(v_val_1193_);
                if v_isShared_1196_ == 0 {
                    lean_ctor_set(v___x_1195_, 0, v_descr_1198_);
                    v___x_1200_ = v___x_1195_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_descr_1198_);
                    v___x_1200_ = v_reuseFailAlloc_1201_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_1164_ = v___y_1190_;
                v___y_1165_ = v_descr_1197_;
                v___y_1166_ = v___y_1188_;
                v___y_1167_ = v___y_1187_;
                v___y_1168_ = v___y_1189_;
                v___y_1169_ = v___x_1200_;
                state = 2;
                continue;
            }
            10 => {
                if lean_obj_tag(v_ir_x3f_1155_) == 0 {
                    v_descr_1206_ = lean_ctor_get(v_ilean_1154_, 0);
                    lean_inc_ref(v_descr_1206_);
                    lean_dec_ref(v_ilean_1154_);
                    v___x_1207_ = lean_box(0);
                    v___y_1187_ = v___y_1204_;
                    v___y_1188_ = v___y_1205_;
                    v___y_1189_ = v_descr_1206_;
                    v___y_1190_ = v___x_1207_;
                    state = 7;
                    continue;
                } else {
                    v_val_1208_ = lean_ctor_get(v_ir_x3f_1155_, 0);
                    v_isSharedCheck_1217_ = (!lean_is_exclusive(v_ir_x3f_1155_)) as u8;
                    if v_isSharedCheck_1217_ == 0 {
                        v___x_1210_ = v_ir_x3f_1155_;
                        v_isShared_1211_ = v_isSharedCheck_1217_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_val_1208_);
                        lean_dec(v_ir_x3f_1155_);
                        v___x_1210_ = lean_box(0);
                        v_isShared_1211_ = v_isSharedCheck_1217_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                v_descr_1212_ = lean_ctor_get(v_ilean_1154_, 0);
                lean_inc_ref(v_descr_1212_);
                lean_dec_ref(v_ilean_1154_);
                v_descr_1213_ = lean_ctor_get(v_val_1208_, 0);
                lean_inc_ref(v_descr_1213_);
                lean_dec(v_val_1208_);
                if v_isShared_1211_ == 0 {
                    lean_ctor_set(v___x_1210_, 0, v_descr_1213_);
                    v___x_1215_ = v___x_1210_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_descr_1213_);
                    v___x_1215_ = v_reuseFailAlloc_1216_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___y_1187_ = v___y_1204_;
                v___y_1188_ = v___y_1205_;
                v___y_1189_ = v_descr_1212_;
                v___y_1190_ = v___x_1215_;
                state = 7;
                continue;
            }
            13 => {
                if lean_obj_tag(v_oleanPrivate_x3f_1153_) == 0 {
                    v___x_1220_ = lean_box(0);
                    v___y_1204_ = v___y_1219_;
                    v___y_1205_ = v___x_1220_;
                    state = 10;
                    continue;
                } else {
                    v_val_1221_ = lean_ctor_get(v_oleanPrivate_x3f_1153_, 0);
                    v_isSharedCheck_1229_ = (!lean_is_exclusive(v_oleanPrivate_x3f_1153_)) as u8;
                    if v_isSharedCheck_1229_ == 0 {
                        v___x_1223_ = v_oleanPrivate_x3f_1153_;
                        v_isShared_1224_ = v_isSharedCheck_1229_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_val_1221_);
                        lean_dec(v_oleanPrivate_x3f_1153_);
                        v___x_1223_ = lean_box(0);
                        v_isShared_1224_ = v_isSharedCheck_1229_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                v_descr_1225_ = lean_ctor_get(v_val_1221_, 0);
                lean_inc_ref(v_descr_1225_);
                lean_dec(v_val_1221_);
                if v_isShared_1224_ == 0 {
                    lean_ctor_set(v___x_1223_, 0, v_descr_1225_);
                    v___x_1227_ = v___x_1223_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_descr_1225_);
                    v___x_1227_ = v_reuseFailAlloc_1228_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___y_1204_ = v___y_1219_;
                v___y_1205_ = v___x_1227_;
                state = 10;
                continue;
            }
            16 => {
                v_descr_1235_ = lean_ctor_get(v_val_1231_, 0);
                lean_inc_ref(v_descr_1235_);
                lean_dec(v_val_1231_);
                if v_isShared_1234_ == 0 {
                    lean_ctor_set(v___x_1233_, 0, v_descr_1235_);
                    v___x_1237_ = v___x_1233_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_descr_1235_);
                    v___x_1237_ = v_reuseFailAlloc_1238_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___y_1219_ = v___x_1237_;
                state = 13;
                continue;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_ModuleArtifacts(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Artifact(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_JsonObject(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_ModuleArtifacts(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_ModuleArtifacts(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Artifact(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_JsonObject(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_ModuleArtifacts(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Build_ModuleArtifacts(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Build_ModuleArtifacts(builtin);
}
