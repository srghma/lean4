// Lean compiler output
// Module: Lean.Data.Lsp.Extra
// Imports: Lean.Data.Lsp.TextSync Lean.Server.Rpc.Basic
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr3};
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getBool_x3f, l_Lean_Json_getNat_x3f, l_Lean_Json_getObjValD,
    l_Lean_Json_getStr_x3f, l_Lean_Json_mkObj, l_Lean_JsonNumber_fromNat,
};
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::{
    l_Lean_Json_getTag_x3f, l_Lean_Name_fromJson_x3f, l_Lean_bignumToJson, l_UInt64_fromJson_x3f,
};
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_pretty;
use crate::r#gen::Lean::Data::Lsp::Basic::{
    l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson,
    l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson,
    l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson,
    l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson,
    l_Lean_Lsp_instToJsonTextDocumentItem_toJson,
    l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson,
};
use crate::r#gen::Lean::Data::Lsp::BasicAux::{
    l_Lean_Lsp_instFromJsonPosition_fromJson, l_Lean_Lsp_instFromJsonRange_fromJson,
    l_Lean_Lsp_instToJsonPosition_toJson, l_Lean_Lsp_instToJsonRange_toJson,
};
use crate::r#gen::Lean::Data::Lsp::TextSync::{
    initialize_Lean_Data_Lsp_TextSync, runtime_initialize_Lean_Data_Lsp_TextSync,
};
use crate::r#gen::Lean::Server::Rpc::Basic::{
    initialize_Lean_Server_Rpc_Basic, l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson,
    l_Lean_Lsp_instToJsonRpcWireFormat_toJson, runtime_initialize_Lean_Server_Rpc_Basic,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_to_nat, lean_usize_add, lean_usize_dec_lt,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_string_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_ctor_set_uint64, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_uint64, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__0_value: LeanStringObject<
    23,
> = LeanStringObject {
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
        110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 97, 103, 32, 102, 111,
        117, 110, 100, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__1_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__2_value: LeanStringObject<
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
    m_data: [110, 101, 118, 101, 114, 0],
};
static mut l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__3_value: LeanStringObject<
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
    m_data: [97, 108, 119, 97, 121, 115, 0],
};
static mut l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__4_value: LeanStringObject<
    5,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [111, 110, 99, 101, 0],
};
static mut l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__5_value: LeanStringObject<
    33,
> = LeanStringObject {
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
        110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 99, 111, 110, 115, 116, 114,
        117, 99, 116, 111, 114, 32, 109, 97, 116, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__6_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__5_value
    ) as *mut LeanObject],
};
static mut l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__7_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__8_value: LeanCtorObject<
    1,
> = LeanCtorObject {
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
static mut l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__9_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((2 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonDependencyBuildMode___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonDependencyBuildMode___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDependencyBuildMode___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonDependencyBuildMode: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDependencyBuildMode___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__0_value: LeanCtorObject<1> =
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
            l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__3_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__1_value: LeanCtorObject<1> =
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
            l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__4_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__2_value: LeanCtorObject<1> =
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
            l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__2_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonDependencyBuildMode___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonDependencyBuildMode___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDependencyBuildMode___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonDependencyBuildMode: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDependencyBuildMode___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instInhabitedDependencyBuildMode_default: u8 = 0;
pub static mut l_Lean_Lsp_instInhabitedDependencyBuildMode: u8 = 0;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0_value:
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
    m_data: [116, 101, 120, 116, 68, 111, 99, 117, 109, 101, 110, 116, 0],
};
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value:
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
    m_data: [76, 115, 112, 0],
};
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__3_value:
    LeanStringObject<30> = LeanStringObject {
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
        76, 101, 97, 110, 68, 105, 100, 79, 112, 101, 110, 84, 101, 120, 116, 68, 111, 99, 117,
        109, 101, 110, 116, 80, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__3_value
) as *mut LeanObject;
static l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__4_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__4_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value
        ) as *mut LeanObject,
        6773744487318448338 as *mut LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__3_value
        ) as *mut LeanObject,
        4208460485772109124 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__4_value
) as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6_value:
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
    m_data: [46, 0],
};
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6_value
) as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__8_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0_value
        ) as *mut LeanObject,
        18338692295241883607 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__8_value
) as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__10_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__10:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11_value:
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
    m_data: [58, 32, 0],
};
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11_value
) as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__12_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__12:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__13_value:
    LeanStringObject<20> = LeanStringObject {
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
        100, 101, 112, 101, 110, 100, 101, 110, 99, 121, 66, 117, 105, 108, 100, 77, 111, 100, 101,
        0,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__13_value
) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__14_value:
    LeanStringObject<21> = LeanStringObject {
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
        100, 101, 112, 101, 110, 100, 101, 110, 99, 121, 66, 117, 105, 108, 100, 77, 111, 100, 101,
        63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__14_value
) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__15_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__14_value
        ) as *mut LeanObject,
        1654166709801890083 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__15_value
) as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__16_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__16:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__17_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__17:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__18_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__18:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0_value:
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
static mut l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0_value:
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
    m_data: [117, 114, 105, 0],
};
static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__1_value:
    LeanStringObject<25> = LeanStringObject {
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
        87, 97, 105, 116, 70, 111, 114, 68, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 80, 97,
        114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__1_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__2_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__2_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__2_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value
        ) as *mut LeanObject,
        6773744487318448338 as *mut LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__2_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__2_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__1_value
        ) as *mut LeanObject,
        15003107547105210748 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__5_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0_value
        ) as *mut LeanObject,
        6053811214292724070 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9_value:
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
static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__10_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9_value
        ) as *mut LeanObject,
        7822243067770061991 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__11_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__12_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__13_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonWaitForDiagnosticsParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonWaitForDiagnosticsParams_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonWaitForDiagnosticsParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWaitForDiagnosticsParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonWaitForDiagnosticsParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWaitForDiagnosticsParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0___closed__0_value: LeanCtorObject<1> =
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
static mut l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonWaitForDiagnostics___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonWaitForDiagnostics___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForDiagnostics___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonWaitForDiagnostics: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForDiagnostics___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instToJsonWaitForDiagnostics___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonWaitForDiagnostics___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWaitForDiagnostics___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonWaitForDiagnostics: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWaitForDiagnostics___closed__0_value)
        as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__0_value: LeanStringObject<
    20,
> = LeanStringObject {
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
        87, 97, 105, 116, 70, 111, 114, 73, 76, 101, 97, 110, 115, 80, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__0_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__1_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__1_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value
        ) as *mut LeanObject,
        6773744487318448338 as *mut LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__1_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__0_value)
            as *mut LeanObject,
        14071555176704055700 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__4_value: LeanStringObject<
    5,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [117, 114, 105, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__5_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__4_value)
            as *mut LeanObject,
        15098297766303001221 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__9_value: LeanStringObject<
    9,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [118, 101, 114, 115, 105, 111, 110, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__10_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__9_value)
            as *mut LeanObject,
        5707914067652744443 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWaitForILeansParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonWaitForILeansParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForILeansParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonWaitForILeansParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForILeansParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonWaitForILeansParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonWaitForILeansParams_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonWaitForILeansParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWaitForILeansParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonWaitForILeansParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWaitForILeansParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___closed__0_value: LeanCtorObject<1> =
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
static mut l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonWaitForILeans___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonWaitForILeans___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForILeans___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonWaitForILeans: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWaitForILeans___closed__0_value) as *mut LeanObject;
static mut l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instToJsonWaitForILeans___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonWaitForILeans_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonWaitForILeans___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWaitForILeans___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonWaitForILeans: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWaitForILeans___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instInhabitedLeanFileProgressKind_default: u8 = 0;
pub static mut l_Lean_Lsp_instInhabitedLeanFileProgressKind: u8 = 0;
pub static l_Lean_Lsp_instBEqLeanFileProgressKind___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instBEqLeanFileProgressKind_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instBEqLeanFileProgressKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqLeanFileProgressKind___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instBEqLeanFileProgressKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqLeanFileProgressKind___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__0_value:
    LeanStringObject<31> = LeanStringObject {
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
        117, 110, 107, 110, 111, 119, 110, 32, 76, 101, 97, 110, 70, 105, 108, 101, 80, 114, 111,
        103, 114, 101, 115, 115, 75, 105, 110, 100, 32, 39, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1_value:
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
static mut l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__2_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__3_value: LeanCtorObject<
    1,
> = LeanCtorObject {
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
static mut l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanFileProgressKind___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonLeanFileProgressKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanFileProgressKind___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonLeanFileProgressKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanFileProgressKind___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instToJsonLeanFileProgressKind___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonLeanFileProgressKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanFileProgressKind___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonLeanFileProgressKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanFileProgressKind___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0_value:
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
    m_data: [114, 97, 110, 103, 101, 0],
};
static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__1_value:
    LeanStringObject<31> = LeanStringObject {
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
        76, 101, 97, 110, 70, 105, 108, 101, 80, 114, 111, 103, 114, 101, 115, 115, 80, 114, 111,
        99, 101, 115, 115, 105, 110, 103, 73, 110, 102, 111, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__1_value
) as *mut LeanObject;
static l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__2_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__2_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__2_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value
        ) as *mut LeanObject,
        6773744487318448338 as *mut LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__2_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__2_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__1_value
        ) as *mut LeanObject,
        7076309381763043140 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__2_value
) as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__5_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0_value
        ) as *mut LeanObject,
        12743603005877258865 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__5_value
) as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9_value:
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
    m_data: [107, 105, 110, 100, 0],
};
static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9_value
) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__10_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9_value
        ) as *mut LeanObject,
        11445860042738416218 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__10_value
) as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo___closed__0_value)
        as *mut LeanObject;
pub static l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__0_value:
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
        76, 101, 97, 110, 70, 105, 108, 101, 80, 114, 111, 103, 114, 101, 115, 115, 80, 97, 114,
        97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__0_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__1_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__1_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value
        ) as *mut LeanObject,
        6773744487318448338 as *mut LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__0_value
        ) as *mut LeanObject,
        18039773570687315226 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__6_value:
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
    m_data: [112, 114, 111, 99, 101, 115, 115, 105, 110, 103, 0],
};
static mut l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__7_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__6_value
        ) as *mut LeanObject,
        10833393810673022613 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanFileProgressParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonLeanFileProgressParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanFileProgressParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonLeanFileProgressParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanFileProgressParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonLeanFileProgressParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonLeanFileProgressParams_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonLeanFileProgressParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanFileProgressParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonLeanFileProgressParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanFileProgressParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__0_value: LeanStringObject<16> =
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
            80, 108, 97, 105, 110, 71, 111, 97, 108, 80, 97, 114, 97, 109, 115, 0,
        ],
    };
static mut l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__0_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value
            ) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value
            ) as *mut LeanObject,
            6773744487318448338 as *mut LeanObject,
        ],
    };
pub static l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__0_value)
                as *mut LeanObject,
            5144552679150019573 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6_value: LeanStringObject<9> =
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
        m_data: [112, 111, 115, 105, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6_value)
                as *mut LeanObject,
            11418699319541476443 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonPlainGoalParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonPlainGoalParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainGoalParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonPlainGoalParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainGoalParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonPlainGoalParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonPlainGoalParams_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonPlainGoalParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPlainGoalParams___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonPlainGoalParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPlainGoalParams___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__0_value: LeanStringObject<9> =
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
        m_data: [114, 101, 110, 100, 101, 114, 101, 100, 0],
    };
static mut l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__1_value: LeanStringObject<10> =
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
        m_data: [80, 108, 97, 105, 110, 71, 111, 97, 108, 0],
    };
static mut l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__1_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value
            ) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value
            ) as *mut LeanObject,
            6773744487318448338 as *mut LeanObject,
        ],
    };
pub static l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__2_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__1_value)
                as *mut LeanObject,
            11329784756819007916 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__0_value)
                as *mut LeanObject,
            14156529057435623211 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__9_value: LeanStringObject<6> =
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
        m_data: [103, 111, 97, 108, 115, 0],
    };
static mut l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__9_value)
                as *mut LeanObject,
            2161670366465228492 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonPlainGoal___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonPlainGoal_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonPlainGoal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainGoal___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonPlainGoal: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainGoal___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonPlainGoal___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonPlainGoal_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonPlainGoal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPlainGoal___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonPlainGoal: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPlainGoal___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__0_value: LeanStringObject<
    20,
> = LeanStringObject {
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
        80, 108, 97, 105, 110, 84, 101, 114, 109, 71, 111, 97, 108, 80, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__0_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__1_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__1_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value
        ) as *mut LeanObject,
        6773744487318448338 as *mut LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__1_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__0_value)
            as *mut LeanObject,
        16077031621694237224 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonPlainTermGoalParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonPlainTermGoalParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainTermGoalParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonPlainTermGoalParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainTermGoalParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonPlainTermGoalParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonPlainTermGoalParams_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonPlainTermGoalParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPlainTermGoalParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonPlainTermGoalParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPlainTermGoalParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__0_value: LeanStringObject<5> =
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
        m_data: [103, 111, 97, 108, 0],
    };
static mut l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__1_value: LeanStringObject<14> =
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
            80, 108, 97, 105, 110, 84, 101, 114, 109, 71, 111, 97, 108, 0,
        ],
    };
static mut l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__1_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value
            ) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__2_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value
            ) as *mut LeanObject,
            6773744487318448338 as *mut LeanObject,
        ],
    };
pub static l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__2_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__1_value)
                as *mut LeanObject,
            2840677436119232233 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__0_value)
                as *mut LeanObject,
            10230924334957577002 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonPlainTermGoal___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonPlainTermGoal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainTermGoal___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonPlainTermGoal: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonPlainTermGoal___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonPlainTermGoal___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonPlainTermGoal_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonPlainTermGoal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPlainTermGoal___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonPlainTermGoal: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonPlainTermGoal___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___closed__0_value:
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
static mut l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonModuleHierarchyOptions___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonModuleHierarchyOptions___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonModuleHierarchyOptions___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonModuleHierarchyOptions: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonModuleHierarchyOptions___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonModuleHierarchyOptions___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonModuleHierarchyOptions___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonModuleHierarchyOptions___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonModuleHierarchyOptions: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonModuleHierarchyOptions___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0_value:
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
static mut l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonHighlightMatchesOptions___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonHighlightMatchesOptions___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHighlightMatchesOptions___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonHighlightMatchesOptions: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHighlightMatchesOptions___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonHighlightMatchesOptions___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonHighlightMatchesOptions___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHighlightMatchesOptions___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonHighlightMatchesOptions: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHighlightMatchesOptions___closed__0_value)
        as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2___closed__0_value) as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__0_value: LeanStringObject<25> =
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
            104, 105, 103, 104, 108, 105, 103, 104, 116, 77, 97, 116, 99, 104, 101, 115, 80, 114,
            111, 118, 105, 100, 101, 114, 0,
        ],
    };
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__1_value: LeanStringObject<11> =
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
        m_data: [82, 112, 99, 79, 112, 116, 105, 111, 110, 115, 0],
    };
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__1_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value
            ) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value
            ) as *mut LeanObject,
            6773744487318448338 as *mut LeanObject,
        ],
    };
pub static l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__2_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__1_value)
                as *mut LeanObject,
            14540034856542732120 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__5_value: LeanStringObject<26> =
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
            104, 105, 103, 104, 108, 105, 103, 104, 116, 77, 97, 116, 99, 104, 101, 115, 80, 114,
            111, 118, 105, 100, 101, 114, 63, 0,
        ],
    };
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__5_value)
                as *mut LeanObject,
            4832200758128680230 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__10_value: LeanStringObject<14> =
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
            114, 112, 99, 87, 105, 114, 101, 70, 111, 114, 109, 97, 116, 0,
        ],
    };
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__11_value: LeanStringObject<15> =
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
            114, 112, 99, 87, 105, 114, 101, 70, 111, 114, 109, 97, 116, 63, 0,
        ],
    };
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__11_value)
                as *mut LeanObject,
            11967579340742895206 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRpcOptions___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonRpcOptions_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonRpcOptions___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcOptions___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonRpcOptions: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcOptions___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonRpcOptions___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonRpcOptions_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonRpcOptions___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRpcOptions___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonRpcOptions: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRpcOptions___closed__0_value) as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__1_value: LeanStringObject<11> =
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
        m_data: [76, 101, 97, 110, 77, 111, 100, 117, 108, 101, 0],
    };
static mut l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__1_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value
            ) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value
            ) as *mut LeanObject,
            6773744487318448338 as *mut LeanObject,
        ],
    };
pub static l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__2_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__1_value)
                as *mut LeanObject,
            16889621590017171973 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__0_value)
                as *mut LeanObject,
            5949480926448383572 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__11_value: LeanStringObject<5> =
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
        m_data: [100, 97, 116, 97, 0],
    };
static mut l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanModule___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonLeanModule_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonLeanModule___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanModule___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonLeanModule: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanModule___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonLeanModule___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonLeanModule_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonLeanModule___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanModule___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonLeanModule: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanModule___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__0_value:
    LeanStringObject<33> = LeanStringObject {
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
        76, 101, 97, 110, 80, 114, 101, 112, 97, 114, 101, 77, 111, 100, 117, 108, 101, 72, 105,
        101, 114, 97, 114, 99, 104, 121, 80, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__0_value
) as *mut LeanObject;
static l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__1_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value) as *mut LeanObject,6773744487318448338 as *mut LeanObject] };
pub static l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__0_value) as *mut LeanObject,1572027020898763307 as *mut LeanObject] };
static mut l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__1_value
) as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instInhabitedLeanImportMetaKind_default: u8 = 0;
pub static mut l_Lean_Lsp_instInhabitedLeanImportMetaKind: u8 = 0;
pub static l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__1_value: LeanStringObject<
    5,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [102, 117, 108, 108, 0],
};
static mut l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__2_value: LeanStringObject<
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
    m_data: [110, 111, 110, 77, 101, 116, 97, 0],
};
static mut l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__3_value: LeanStringObject<
    5,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [109, 101, 116, 97, 0],
};
static mut l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__4_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__5_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__6_value: LeanCtorObject<1> =
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
static mut l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__7_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanImportMetaKind___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonLeanImportMetaKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportMetaKind___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonLeanImportMetaKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportMetaKind___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__0_value: LeanCtorObject<1> =
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
            l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__2_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__1_value: LeanCtorObject<1> =
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
            l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__3_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__2_value: LeanCtorObject<1> =
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
            l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__1_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonLeanImportMetaKind___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonLeanImportMetaKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanImportMetaKind___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonLeanImportMetaKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanImportMetaKind___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__0_value: LeanStringObject<10> =
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
        m_data: [105, 115, 80, 114, 105, 118, 97, 116, 101, 0],
    };
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__1_value: LeanStringObject<15> =
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
            76, 101, 97, 110, 73, 109, 112, 111, 114, 116, 75, 105, 110, 100, 0,
        ],
    };
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__1_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value
            ) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__2_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value
            ) as *mut LeanObject,
            6773744487318448338 as *mut LeanObject,
        ],
    };
pub static l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__2_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__1_value)
                as *mut LeanObject,
            6598182023884241329 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__0_value)
                as *mut LeanObject,
            669396322782783324 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__9_value: LeanStringObject<6> =
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
        m_data: [105, 115, 65, 108, 108, 0],
    };
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__9_value)
                as *mut LeanObject,
            2279298587086710714 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__14_value: LeanStringObject<9> =
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
        m_data: [109, 101, 116, 97, 75, 105, 110, 100, 0],
    };
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__15_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__14_value)
                as *mut LeanObject,
            2269651469996521300 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__15_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanImportKind___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonLeanImportKind_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonLeanImportKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportKind___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonLeanImportKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImportKind___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonLeanImportKind___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonLeanImportKind_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonLeanImportKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanImportKind___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonLeanImportKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanImportKind___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0_value: LeanStringObject<7> =
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
static mut l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__1_value: LeanStringObject<11> =
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
        m_data: [76, 101, 97, 110, 73, 109, 112, 111, 114, 116, 0],
    };
static mut l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__1_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value
            ) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value
            ) as *mut LeanObject,
            6773744487318448338 as *mut LeanObject,
        ],
    };
pub static l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__2_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__1_value)
                as *mut LeanObject,
            15524993532920779620 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0_value)
                as *mut LeanObject,
            5134674735115079031 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanImport___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonLeanImport_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonLeanImport___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImport___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonLeanImport: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanImport___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonLeanImport___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonLeanImport_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonLeanImport___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanImport___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonLeanImport: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanImport___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__0_value:
    LeanStringObject<33> = LeanStringObject {
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
        76, 101, 97, 110, 77, 111, 100, 117, 108, 101, 72, 105, 101, 114, 97, 114, 99, 104, 121,
        73, 109, 112, 111, 114, 116, 115, 80, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__0_value
) as *mut LeanObject;
static l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__1_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value) as *mut LeanObject,6773744487318448338 as *mut LeanObject] };
pub static l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__0_value) as *mut LeanObject,10679961565396149009 as *mut LeanObject] };
static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__1_value
) as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__0_value:
    LeanStringObject<36> = LeanStringObject {
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
        76, 101, 97, 110, 77, 111, 100, 117, 108, 101, 72, 105, 101, 114, 97, 114, 99, 104, 121,
        73, 109, 112, 111, 114, 116, 101, 100, 66, 121, 80, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__0_value
) as *mut LeanObject;
static l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value) as *mut LeanObject,6773744487318448338 as *mut LeanObject] };
pub static l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__0_value) as *mut LeanObject,13281216081140862494 as *mut LeanObject] };
static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__1_value
) as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams___closed__0_value
)
    as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__0_value: LeanStringObject<
    17,
> = LeanStringObject {
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
        82, 112, 99, 67, 111, 110, 110, 101, 99, 116, 80, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__0_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value
            ) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value
            ) as *mut LeanObject,
            6773744487318448338 as *mut LeanObject,
        ],
    };
pub static l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__0_value)
                as *mut LeanObject,
            3801587995712050804 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRpcConnectParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonRpcConnectParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcConnectParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonRpcConnectParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcConnectParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonRpcConnectParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonRpcConnectParams_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonRpcConnectParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRpcConnectParams___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonRpcConnectParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRpcConnectParams___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0_value: LeanStringObject<10> =
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
        m_data: [115, 101, 115, 115, 105, 111, 110, 73, 100, 0],
    };
static mut l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__1_value: LeanStringObject<13> =
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
        m_data: [82, 112, 99, 67, 111, 110, 110, 101, 99, 116, 101, 100, 0],
    };
static mut l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__1_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value
            ) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__2_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value
            ) as *mut LeanObject,
            6773744487318448338 as *mut LeanObject,
        ],
    };
pub static l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__2_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__1_value)
                as *mut LeanObject,
            11486397293585691060 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0_value)
                as *mut LeanObject,
            8266014154353595525 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRpcConnected___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonRpcConnected_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonRpcConnected___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcConnected___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonRpcConnected: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcConnected___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonRpcConnected___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonRpcConnected_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonRpcConnected___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRpcConnected___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonRpcConnected: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRpcConnected___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__0_value: LeanStringObject<14> =
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
        m_data: [82, 112, 99, 67, 97, 108, 108, 80, 97, 114, 97, 109, 115, 0],
    };
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__0_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value
            ) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value
            ) as *mut LeanObject,
            6773744487318448338 as *mut LeanObject,
        ],
    };
pub static l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__0_value)
                as *mut LeanObject,
            6022269458358166380 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__10_value: LeanStringObject<7> =
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
        m_data: [109, 101, 116, 104, 111, 100, 0],
    };
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__10_value)
                as *mut LeanObject,
            10404875796858280754 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__15_value: LeanStringObject<7> =
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
        m_data: [112, 97, 114, 97, 109, 115, 0],
    };
static mut l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRpcCallParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonRpcCallParams_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonRpcCallParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcCallParams___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonRpcCallParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcCallParams___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonRpcCallParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonRpcCallParams_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonRpcCallParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRpcCallParams___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonRpcCallParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRpcCallParams___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__0_value: LeanStringObject<
    17,
> = LeanStringObject {
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
        82, 112, 99, 82, 101, 108, 101, 97, 115, 101, 80, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__0_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value
            ) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value
            ) as *mut LeanObject,
            6773744487318448338 as *mut LeanObject,
        ],
    };
pub static l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__0_value)
                as *mut LeanObject,
            17417639033772671771 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__8_value: LeanStringObject<5> =
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
        m_data: [114, 101, 102, 115, 0],
    };
static mut l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__8_value)
                as *mut LeanObject,
            13537518555288142509 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__9_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRpcReleaseParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonRpcReleaseParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcReleaseParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonRpcReleaseParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcReleaseParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonRpcReleaseParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonRpcReleaseParams_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonRpcReleaseParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRpcReleaseParams___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonRpcReleaseParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRpcReleaseParams___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__0_value: LeanStringObject<
    19,
> = LeanStringObject {
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
        82, 112, 99, 75, 101, 101, 112, 65, 108, 105, 118, 101, 80, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__0_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__1_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__1_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value
        ) as *mut LeanObject,
        6773744487318448338 as *mut LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__0_value
            ) as *mut LeanObject,
            16178679952852214846 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonRpcKeepAliveParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonRpcKeepAliveParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcKeepAliveParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonRpcKeepAliveParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcKeepAliveParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonRpcKeepAliveParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonRpcKeepAliveParams_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonRpcKeepAliveParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRpcKeepAliveParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonRpcKeepAliveParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRpcKeepAliveParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instInhabitedLineRange_default___closed__0_value: LeanCtorObject<2> =
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
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instInhabitedLineRange_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instInhabitedLineRange_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instInhabitedLineRange_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instInhabitedLineRange_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instInhabitedLineRange: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instInhabitedLineRange_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instReprLineRange_repr___redArg___closed__0_value: LeanStringObject<3> =
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
static mut l_Lean_Lsp_instReprLineRange_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instReprLineRange_repr___redArg___closed__1_value: LeanStringObject<6> =
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
        m_data: [115, 116, 97, 114, 116, 0],
    };
static mut l_Lean_Lsp_instReprLineRange_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instReprLineRange_repr___redArg___closed__2_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instReprLineRange_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instReprLineRange_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instReprLineRange_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instReprLineRange_repr___redArg___closed__4_value: LeanStringObject<5> =
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
static mut l_Lean_Lsp_instReprLineRange_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instReprLineRange_repr___redArg___closed__5_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instReprLineRange_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instReprLineRange_repr___redArg___closed__6_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instReprLineRange_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instReprLineRange_repr___redArg___closed__8_value: LeanStringObject<2> =
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
static mut l_Lean_Lsp_instReprLineRange_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instReprLineRange_repr___redArg___closed__9_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instReprLineRange_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instReprLineRange_repr___redArg___closed__10_value: LeanStringObject<4> =
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
        m_data: [101, 110, 100, 0],
    };
static mut l_Lean_Lsp_instReprLineRange_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instReprLineRange_repr___redArg___closed__11_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instReprLineRange_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instReprLineRange_repr___redArg___closed__13_value: LeanStringObject<3> =
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
static mut l_Lean_Lsp_instReprLineRange_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__13_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instReprLineRange_repr___redArg___closed__16_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instReprLineRange_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instReprLineRange_repr___redArg___closed__17_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instReprLineRange_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instReprLineRange___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instReprLineRange_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instReprLineRange___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instReprLineRange: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__0_value: LeanStringObject<10> =
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
        m_data: [76, 105, 110, 101, 82, 97, 110, 103, 101, 0],
    };
static mut l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__0_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value
            ) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value
            ) as *mut LeanObject,
            6773744487318448338 as *mut LeanObject,
        ],
    };
pub static l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__0_value)
                as *mut LeanObject,
            16276291405582970199 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__1_value)
                as *mut LeanObject,
            12748178501718933929 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__10_value)
                as *mut LeanObject,
            7094185473178890951 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLineRange___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonLineRange_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonLineRange___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLineRange___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonLineRange: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLineRange___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonLineRange___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonLineRange_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonLineRange___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLineRange___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonLineRange: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLineRange___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lean_Lsp_DependencyBuildMode_ctorIdx(mut v_x_3357_: u8) -> *mut LeanObject {
    match v_x_3357_ {
        0 => {
            let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
            v___x_3358_ = lean_unsigned_to_nat(0);
            return v___x_3358_;
        }
        1 => {
            let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
            v___x_3359_ = lean_unsigned_to_nat(1);
            return v___x_3359_;
        }
        _ => {
            let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
            v___x_3360_ = lean_unsigned_to_nat(2);
            return v___x_3360_;
        }
    }
}
pub unsafe fn l_Lean_Lsp_DependencyBuildMode_ctorIdx___boxed(
    mut v_x_3361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_3362_: u8 = 0;
    let mut v_res_3363_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_3362_ = (lean_unbox(v_x_3361_) as u8);
    v_res_3363_ = l_Lean_Lsp_DependencyBuildMode_ctorIdx(v_x_boxed_3362_);
    return v_res_3363_;
}
pub unsafe fn l_Lean_Lsp_DependencyBuildMode_toCtorIdx(mut v_x_3364_: u8) -> *mut LeanObject {
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    v___x_3365_ = l_Lean_Lsp_DependencyBuildMode_ctorIdx(v_x_3364_);
    return v___x_3365_;
}
pub unsafe fn l_Lean_Lsp_DependencyBuildMode_toCtorIdx___boxed(
    mut v_x_3366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_3367_: u8 = 0;
    let mut v_res_3368_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_3367_ = (lean_unbox(v_x_3366_) as u8);
    v_res_3368_ = l_Lean_Lsp_DependencyBuildMode_toCtorIdx(v_x_4__boxed_3367_);
    return v_res_3368_;
}
pub unsafe fn l_Lean_Lsp_DependencyBuildMode_ctorElim___redArg(
    mut v_k_3369_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_3369_);
    return v_k_3369_;
}
pub unsafe fn l_Lean_Lsp_DependencyBuildMode_ctorElim___redArg___boxed(
    mut v_k_3370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3371_: *mut LeanObject = core::ptr::null_mut();
    v_res_3371_ = l_Lean_Lsp_DependencyBuildMode_ctorElim___redArg(v_k_3370_);
    lean_dec(v_k_3370_);
    return v_res_3371_;
}
pub unsafe fn l_Lean_Lsp_DependencyBuildMode_ctorElim(
    mut v_motive_3372_: *mut LeanObject,
    mut v_ctorIdx_3373_: *mut LeanObject,
    mut v_t_3374_: u8,
    mut v_h_3375_: *mut LeanObject,
    mut v_k_3376_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_3376_);
    return v_k_3376_;
}
pub unsafe fn l_Lean_Lsp_DependencyBuildMode_ctorElim___boxed(
    mut v_motive_3377_: *mut LeanObject,
    mut v_ctorIdx_3378_: *mut LeanObject,
    mut v_t_3379_: *mut LeanObject,
    mut v_h_3380_: *mut LeanObject,
    mut v_k_3381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_3382_: u8 = 0;
    let mut v_res_3383_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_3382_ = (lean_unbox(v_t_3379_) as u8);
    v_res_3383_ = l_Lean_Lsp_DependencyBuildMode_ctorElim(
        v_motive_3377_,
        v_ctorIdx_3378_,
        v_t_boxed_3382_,
        v_h_3380_,
        v_k_3381_,
    );
    lean_dec(v_k_3381_);
    lean_dec(v_ctorIdx_3378_);
    return v_res_3383_;
}
pub unsafe fn l_Lean_Lsp_DependencyBuildMode_always_elim___redArg(
    mut v_always_3384_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_always_3384_);
    return v_always_3384_;
}
pub unsafe fn l_Lean_Lsp_DependencyBuildMode_always_elim___redArg___boxed(
    mut v_always_3385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3386_: *mut LeanObject = core::ptr::null_mut();
    v_res_3386_ = l_Lean_Lsp_DependencyBuildMode_always_elim___redArg(v_always_3385_);
    lean_dec(v_always_3385_);
    return v_res_3386_;
}
pub unsafe fn l_Lean_Lsp_DependencyBuildMode_always_elim(
    mut v_motive_3387_: *mut LeanObject,
    mut v_t_3388_: u8,
    mut v_h_3389_: *mut LeanObject,
    mut v_always_3390_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_always_3390_);
    return v_always_3390_;
}
pub unsafe fn l_Lean_Lsp_DependencyBuildMode_always_elim___boxed(
    mut v_motive_3391_: *mut LeanObject,
    mut v_t_3392_: *mut LeanObject,
    mut v_h_3393_: *mut LeanObject,
    mut v_always_3394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_3395_: u8 = 0;
    let mut v_res_3396_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_3395_ = (lean_unbox(v_t_3392_) as u8);
    v_res_3396_ = l_Lean_Lsp_DependencyBuildMode_always_elim(
        v_motive_3391_,
        v_t_boxed_3395_,
        v_h_3393_,
        v_always_3394_,
    );
    lean_dec(v_always_3394_);
    return v_res_3396_;
}
pub unsafe fn l_Lean_Lsp_DependencyBuildMode_once_elim___redArg(
    mut v_once_3397_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_once_3397_);
    return v_once_3397_;
}
pub unsafe fn l_Lean_Lsp_DependencyBuildMode_once_elim___redArg___boxed(
    mut v_once_3398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3399_: *mut LeanObject = core::ptr::null_mut();
    v_res_3399_ = l_Lean_Lsp_DependencyBuildMode_once_elim___redArg(v_once_3398_);
    lean_dec(v_once_3398_);
    return v_res_3399_;
}
pub unsafe fn l_Lean_Lsp_DependencyBuildMode_once_elim(
    mut v_motive_3400_: *mut LeanObject,
    mut v_t_3401_: u8,
    mut v_h_3402_: *mut LeanObject,
    mut v_once_3403_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_once_3403_);
    return v_once_3403_;
}
pub unsafe fn l_Lean_Lsp_DependencyBuildMode_once_elim___boxed(
    mut v_motive_3404_: *mut LeanObject,
    mut v_t_3405_: *mut LeanObject,
    mut v_h_3406_: *mut LeanObject,
    mut v_once_3407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_3408_: u8 = 0;
    let mut v_res_3409_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_3408_ = (lean_unbox(v_t_3405_) as u8);
    v_res_3409_ = l_Lean_Lsp_DependencyBuildMode_once_elim(
        v_motive_3404_,
        v_t_boxed_3408_,
        v_h_3406_,
        v_once_3407_,
    );
    lean_dec(v_once_3407_);
    return v_res_3409_;
}
pub unsafe fn l_Lean_Lsp_DependencyBuildMode_never_elim___redArg(
    mut v_never_3410_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_never_3410_);
    return v_never_3410_;
}
pub unsafe fn l_Lean_Lsp_DependencyBuildMode_never_elim___redArg___boxed(
    mut v_never_3411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3412_: *mut LeanObject = core::ptr::null_mut();
    v_res_3412_ = l_Lean_Lsp_DependencyBuildMode_never_elim___redArg(v_never_3411_);
    lean_dec(v_never_3411_);
    return v_res_3412_;
}
pub unsafe fn l_Lean_Lsp_DependencyBuildMode_never_elim(
    mut v_motive_3413_: *mut LeanObject,
    mut v_t_3414_: u8,
    mut v_h_3415_: *mut LeanObject,
    mut v_never_3416_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_never_3416_);
    return v_never_3416_;
}
pub unsafe fn l_Lean_Lsp_DependencyBuildMode_never_elim___boxed(
    mut v_motive_3417_: *mut LeanObject,
    mut v_t_3418_: *mut LeanObject,
    mut v_h_3419_: *mut LeanObject,
    mut v_never_3420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_3421_: u8 = 0;
    let mut v_res_3422_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_3421_ = (lean_unbox(v_t_3418_) as u8);
    v_res_3422_ = l_Lean_Lsp_DependencyBuildMode_never_elim(
        v_motive_3417_,
        v_t_boxed_3421_,
        v_h_3419_,
        v_never_3420_,
    );
    lean_dec(v_never_3420_);
    return v_res_3422_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson(
    mut v_json_3441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    v___x_3442_ = l_Lean_Json_getTag_x3f(v_json_3441_);
    if lean_obj_tag(v___x_3442_) == 0 {
        let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
        v___x_3443_ = l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__1;
        return v___x_3443_;
    } else {
        let mut v_val_3444_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3446_: u8 = 0;
        v_val_3444_ = lean_ctor_get(v___x_3442_, 0);
        lean_inc(v_val_3444_);
        lean_dec_ref_known(v___x_3442_, 1);
        v___x_3445_ = l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__2;
        v___x_3446_ = lean_string_dec_eq(v_val_3444_, v___x_3445_);
        if v___x_3446_ == 0 {
            let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3448_: u8 = 0;
            v___x_3447_ = l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__3;
            v___x_3448_ = lean_string_dec_eq(v_val_3444_, v___x_3447_);
            if v___x_3448_ == 0 {
                let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3450_: u8 = 0;
                v___x_3449_ = l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__4;
                v___x_3450_ = lean_string_dec_eq(v_val_3444_, v___x_3449_);
                lean_dec(v_val_3444_);
                if v___x_3450_ == 0 {
                    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
                    v___x_3451_ = l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__6;
                    return v___x_3451_;
                } else {
                    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
                    v___x_3452_ = l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__7;
                    return v___x_3452_;
                }
            } else {
                let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_val_3444_);
                v___x_3453_ = l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__8;
                return v___x_3453_;
            }
        } else {
            let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_val_3444_);
            v___x_3454_ = l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__9;
            return v___x_3454_;
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonDependencyBuildMode_toJson(
    mut v_x_3463_: u8,
) -> *mut LeanObject {
    match v_x_3463_ {
        0 => {
            let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
            v___x_3464_ = l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__0;
            return v___x_3464_;
        }
        1 => {
            let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
            v___x_3465_ = l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__1;
            return v___x_3465_;
        }
        _ => {
            let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
            v___x_3466_ = l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__2;
            return v___x_3466_;
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___boxed(
    mut v_x_3467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_64__boxed_3468_: u8 = 0;
    let mut v_res_3469_: *mut LeanObject = core::ptr::null_mut();
    v_x_64__boxed_3468_ = (lean_unbox(v_x_3467_) as u8);
    v_res_3469_ = l_Lean_Lsp_instToJsonDependencyBuildMode_toJson(v_x_64__boxed_3468_);
    return v_res_3469_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedDependencyBuildMode_default() -> u8 {
    let mut v___x_3472_: u8 = 0;
    v___x_3472_ = 0;
    return v___x_3472_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedDependencyBuildMode() -> u8 {
    let mut v___x_3473_: u8 = 0;
    v___x_3473_ = 0;
    return v___x_3473_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__0(
    mut v_j_3474_: *mut LeanObject,
    mut v_k_3475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    v___x_3476_ = l_Lean_Json_getObjValD(v_j_3474_, v_k_3475_);
    v___x_3477_ = l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson(v___x_3476_);
    return v___x_3477_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__0___boxed(
    mut v_j_3478_: *mut LeanObject,
    mut v_k_3479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3480_: *mut LeanObject = core::ptr::null_mut();
    v_res_3480_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__0(v_j_3478_, v_k_3479_);
    lean_dec_ref(v_k_3479_);
    return v_res_3480_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1(
    mut v_x_3483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3489_: u8 = 0;
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3493_: u8 = 0;
    let mut v_a_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3497_: u8 = 0;
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3502_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3483_) == 0 {
                    v___x_3484_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1___closed__0;
                    return v___x_3484_;
                } else {
                    v___x_3485_ = l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson(v_x_3483_);
                    if lean_obj_tag(v___x_3485_) == 0 {
                        v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
                        v_isSharedCheck_3493_ = (!lean_is_exclusive(v___x_3485_)) as u8;
                        if v_isSharedCheck_3493_ == 0 {
                            v___x_3488_ = v___x_3485_;
                            v_isShared_3489_ = v_isSharedCheck_3493_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3486_);
                            lean_dec(v___x_3485_);
                            v___x_3488_ = lean_box(0);
                            v_isShared_3489_ = v_isSharedCheck_3493_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3494_ = lean_ctor_get(v___x_3485_, 0);
                        v_isSharedCheck_3502_ = (!lean_is_exclusive(v___x_3485_)) as u8;
                        if v_isSharedCheck_3502_ == 0 {
                            v___x_3496_ = v___x_3485_;
                            v_isShared_3497_ = v_isSharedCheck_3502_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3494_);
                            lean_dec(v___x_3485_);
                            v___x_3496_ = lean_box(0);
                            v_isShared_3497_ = v_isSharedCheck_3502_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3489_ == 0 {
                    v___x_3491_ = v___x_3488_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
                    v___x_3491_ = v_reuseFailAlloc_3492_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3491_;
            }
            3 => {
                v___x_3498_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3498_, 0, v_a_3494_);
                if v_isShared_3497_ == 0 {
                    lean_ctor_set(v___x_3496_, 0, v___x_3498_);
                    v___x_3500_ = v___x_3496_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3498_);
                    v___x_3500_ = v_reuseFailAlloc_3501_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3500_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1(
    mut v_j_3503_: *mut LeanObject,
    mut v_k_3504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    v___x_3505_ = l_Lean_Json_getObjValD(v_j_3503_, v_k_3504_);
    v___x_3506_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1(v___x_3505_);
    return v___x_3506_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1___boxed(
    mut v_j_3507_: *mut LeanObject,
    mut v_k_3508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3509_: *mut LeanObject = core::ptr::null_mut();
    v_res_3509_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1(v_j_3507_, v_k_3508_);
    lean_dec_ref(v_k_3508_);
    return v_res_3509_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__5()
-> *mut LeanObject {
    let mut v___x_3518_: u8 = 0;
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    v___x_3518_ = 1;
    v___x_3519_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__4;
    v___x_3520_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3519_, v___x_3518_);
    return v___x_3520_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7()
-> *mut LeanObject {
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    v___x_3522_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6;
    v___x_3523_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__5_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__5,
    );
    v___x_3524_ = lean_string_append(v___x_3523_, v___x_3522_);
    return v___x_3524_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9()
-> *mut LeanObject {
    let mut v___x_3527_: u8 = 0;
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    v___x_3527_ = 1;
    v___x_3528_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__8;
    v___x_3529_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3528_, v___x_3527_);
    return v___x_3529_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__10()
-> *mut LeanObject {
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    v___x_3530_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9,
    );
    v___x_3531_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7,
    );
    v___x_3532_ = lean_string_append(v___x_3531_, v___x_3530_);
    return v___x_3532_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__12()
-> *mut LeanObject {
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    v___x_3534_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_3535_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__10_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__10,
    );
    v___x_3536_ = lean_string_append(v___x_3535_, v___x_3534_);
    return v___x_3536_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__16()
-> *mut LeanObject {
    let mut v___x_3541_: u8 = 0;
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    v___x_3541_ = 1;
    v___x_3542_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__15;
    v___x_3543_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3542_, v___x_3541_);
    return v___x_3543_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__17()
-> *mut LeanObject {
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    v___x_3544_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__16
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__16_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__16,
    );
    v___x_3545_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7,
    );
    v___x_3546_ = lean_string_append(v___x_3545_, v___x_3544_);
    return v___x_3546_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__18()
-> *mut LeanObject {
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    v___x_3547_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_3548_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__17
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__17_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__17,
    );
    v___x_3549_ = lean_string_append(v___x_3548_, v___x_3547_);
    return v___x_3549_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson(
    mut v_json_3550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3556_: u8 = 0;
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3562_: u8 = 0;
    let mut v_a_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3566_: u8 = 0;
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3570_: u8 = 0;
    let mut v_a_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3577_: u8 = 0;
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3583_: u8 = 0;
    let mut v_a_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3587_: u8 = 0;
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3591_: u8 = 0;
    let mut v_a_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3595_: u8 = 0;
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3600_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3551_ =
                    l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0;
                lean_inc(v_json_3550_);
                v___x_3552_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__0(v_json_3550_, v___x_3551_);
                if lean_obj_tag(v___x_3552_) == 0 {
                    lean_dec(v_json_3550_);
                    v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
                    v_isSharedCheck_3562_ = (!lean_is_exclusive(v___x_3552_)) as u8;
                    if v_isSharedCheck_3562_ == 0 {
                        v___x_3555_ = v___x_3552_;
                        v_isShared_3556_ = v_isSharedCheck_3562_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3553_);
                        lean_dec(v___x_3552_);
                        v___x_3555_ = lean_box(0);
                        v_isShared_3556_ = v_isSharedCheck_3562_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_3552_) == 0 {
                        lean_dec(v_json_3550_);
                        v_a_3563_ = lean_ctor_get(v___x_3552_, 0);
                        v_isSharedCheck_3570_ = (!lean_is_exclusive(v___x_3552_)) as u8;
                        if v_isSharedCheck_3570_ == 0 {
                            v___x_3565_ = v___x_3552_;
                            v_isShared_3566_ = v_isSharedCheck_3570_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3563_);
                            lean_dec(v___x_3552_);
                            v___x_3565_ = lean_box(0);
                            v_isShared_3566_ = v_isSharedCheck_3570_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3571_ = lean_ctor_get(v___x_3552_, 0);
                        lean_inc(v_a_3571_);
                        lean_dec_ref_known(v___x_3552_, 1);
                        v___x_3572_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__13;
                        v___x_3573_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1(v_json_3550_, v___x_3572_);
                        if lean_obj_tag(v___x_3573_) == 0 {
                            lean_dec(v_a_3571_);
                            v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
                            v_isSharedCheck_3583_ = (!lean_is_exclusive(v___x_3573_)) as u8;
                            if v_isSharedCheck_3583_ == 0 {
                                v___x_3576_ = v___x_3573_;
                                v_isShared_3577_ = v_isSharedCheck_3583_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_3574_);
                                lean_dec(v___x_3573_);
                                v___x_3576_ = lean_box(0);
                                v_isShared_3577_ = v_isSharedCheck_3583_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_3573_) == 0 {
                                lean_dec(v_a_3571_);
                                v_a_3584_ = lean_ctor_get(v___x_3573_, 0);
                                v_isSharedCheck_3591_ = (!lean_is_exclusive(v___x_3573_)) as u8;
                                if v_isSharedCheck_3591_ == 0 {
                                    v___x_3586_ = v___x_3573_;
                                    v_isShared_3587_ = v_isSharedCheck_3591_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_3584_);
                                    lean_dec(v___x_3573_);
                                    v___x_3586_ = lean_box(0);
                                    v_isShared_3587_ = v_isSharedCheck_3591_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_3592_ = lean_ctor_get(v___x_3573_, 0);
                                v_isSharedCheck_3600_ = (!lean_is_exclusive(v___x_3573_)) as u8;
                                if v_isSharedCheck_3600_ == 0 {
                                    v___x_3594_ = v___x_3573_;
                                    v_isShared_3595_ = v_isSharedCheck_3600_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_3592_);
                                    lean_dec(v___x_3573_);
                                    v___x_3594_ = lean_box(0);
                                    v_isShared_3595_ = v_isSharedCheck_3600_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3557_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__12), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__12_once), _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__12);
                v___x_3558_ = lean_string_append(v___x_3557_, v_a_3553_);
                lean_dec(v_a_3553_);
                if v_isShared_3556_ == 0 {
                    lean_ctor_set(v___x_3555_, 0, v___x_3558_);
                    v___x_3560_ = v___x_3555_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3561_, 0, v___x_3558_);
                    v___x_3560_ = v_reuseFailAlloc_3561_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3560_;
            }
            3 => {
                if v_isShared_3566_ == 0 {
                    lean_ctor_set_tag(v___x_3565_, 0);
                    v___x_3568_ = v___x_3565_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
                    v___x_3568_ = v_reuseFailAlloc_3569_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3568_;
            }
            5 => {
                v___x_3578_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__18), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__18_once), _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__18);
                v___x_3579_ = lean_string_append(v___x_3578_, v_a_3574_);
                lean_dec(v_a_3574_);
                if v_isShared_3577_ == 0 {
                    lean_ctor_set(v___x_3576_, 0, v___x_3579_);
                    v___x_3581_ = v___x_3576_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_3579_);
                    v___x_3581_ = v_reuseFailAlloc_3582_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3581_;
            }
            7 => {
                if v_isShared_3587_ == 0 {
                    lean_ctor_set_tag(v___x_3586_, 0);
                    v___x_3589_ = v___x_3586_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3584_);
                    v___x_3589_ = v_reuseFailAlloc_3590_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3589_;
            }
            9 => {
                v___x_3596_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3596_, 0, v_a_3571_);
                lean_ctor_set(v___x_3596_, 1, v_a_3592_);
                if v_isShared_3595_ == 0 {
                    lean_ctor_set(v___x_3594_, 0, v___x_3596_);
                    v___x_3598_ = v___x_3594_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3599_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3596_);
                    v___x_3598_ = v_reuseFailAlloc_3599_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3598_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__0(
    mut v_k_3603_: *mut LeanObject,
    mut v_x_3604_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3604_) == 0 {
        let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_k_3603_);
        v___x_3605_ = lean_box(0);
        return v___x_3605_;
    } else {
        let mut v_val_3606_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3607_: u8 = 0;
        let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
        v_val_3606_ = lean_ctor_get(v_x_3604_, 0);
        v___x_3607_ = (lean_unbox(v_val_3606_) as u8);
        v___x_3608_ = l_Lean_Lsp_instToJsonDependencyBuildMode_toJson(v___x_3607_);
        v___x_3609_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3609_, 0, v_k_3603_);
        lean_ctor_set(v___x_3609_, 1, v___x_3608_);
        v___x_3610_ = lean_box(0);
        v___x_3611_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3611_, 0, v___x_3609_);
        lean_ctor_set(v___x_3611_, 1, v___x_3610_);
        return v___x_3611_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__0___boxed(
    mut v_k_3612_: *mut LeanObject,
    mut v_x_3613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3614_: *mut LeanObject = core::ptr::null_mut();
    v_res_3614_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__0(
            v_k_3612_, v_x_3613_,
        );
    lean_dec(v_x_3613_);
    return v_res_3614_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(
    mut v_a_3615_: *mut LeanObject,
    mut v_a_3616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3615_) == 0 {
                    v___x_3617_ = lean_array_to_list(v_a_3616_);
                    return v___x_3617_;
                } else {
                    v_head_3618_ = lean_ctor_get(v_a_3615_, 0);
                    lean_inc(v_head_3618_);
                    v_tail_3619_ = lean_ctor_get(v_a_3615_, 1);
                    lean_inc(v_tail_3619_);
                    lean_dec_ref_known(v_a_3615_, 2);
                    v___x_3620_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_3616_,
                        v_head_3618_,
                    );
                    v_a_3615_ = v_tail_3619_;
                    v_a_3616_ = v___x_3620_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson(
    mut v_x_3624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toDidOpenTextDocumentParams_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dependencyBuildMode_x3f_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3629_: u8 = 0;
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3644_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toDidOpenTextDocumentParams_3625_ = lean_ctor_get(v_x_3624_, 0);
                v_dependencyBuildMode_x3f_3626_ = lean_ctor_get(v_x_3624_, 1);
                v_isSharedCheck_3644_ = (!lean_is_exclusive(v_x_3624_)) as u8;
                if v_isSharedCheck_3644_ == 0 {
                    v___x_3628_ = v_x_3624_;
                    v_isShared_3629_ = v_isSharedCheck_3644_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_dependencyBuildMode_x3f_3626_);
                    lean_inc(v_toDidOpenTextDocumentParams_3625_);
                    lean_dec(v_x_3624_);
                    v___x_3628_ = lean_box(0);
                    v_isShared_3629_ = v_isSharedCheck_3644_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3630_ =
                    l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0;
                v___x_3631_ = l_Lean_Lsp_instToJsonTextDocumentItem_toJson(
                    v_toDidOpenTextDocumentParams_3625_,
                );
                if v_isShared_3629_ == 0 {
                    lean_ctor_set(v___x_3628_, 1, v___x_3631_);
                    lean_ctor_set(v___x_3628_, 0, v___x_3630_);
                    v___x_3633_ = v___x_3628_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3643_, 0, v___x_3630_);
                    lean_ctor_set(v_reuseFailAlloc_3643_, 1, v___x_3631_);
                    v___x_3633_ = v_reuseFailAlloc_3643_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3634_ = lean_box(0);
                v___x_3635_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3635_, 0, v___x_3633_);
                lean_ctor_set(v___x_3635_, 1, v___x_3634_);
                v___x_3636_ =
                    l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__13;
                v___x_3637_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__0(v___x_3636_, v_dependencyBuildMode_x3f_3626_);
                lean_dec(v_dependencyBuildMode_x3f_3626_);
                v___x_3638_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3638_, 0, v___x_3637_);
                lean_ctor_set(v___x_3638_, 1, v___x_3634_);
                v___x_3639_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3639_, 0, v___x_3635_);
                lean_ctor_set(v___x_3639_, 1, v___x_3638_);
                v___x_3640_ = l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0;
                v___x_3641_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_3639_, v___x_3640_);
                v___x_3642_ = l_Lean_Json_mkObj(v___x_3641_);
                lean_dec(v___x_3641_);
                return v___x_3642_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(
    mut v_j_3647_: *mut LeanObject,
    mut v_k_3648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    v___x_3649_ = l_Lean_Json_getObjValD(v_j_3647_, v_k_3648_);
    v___x_3650_ = l_Lean_Json_getStr_x3f(v___x_3649_);
    return v___x_3650_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0___boxed(
    mut v_j_3651_: *mut LeanObject,
    mut v_k_3652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3653_: *mut LeanObject = core::ptr::null_mut();
    v_res_3653_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_j_3651_, v_k_3652_);
    lean_dec_ref(v_k_3652_);
    return v_res_3653_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1(
    mut v_j_3654_: *mut LeanObject,
    mut v_k_3655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    v___x_3656_ = l_Lean_Json_getObjValD(v_j_3654_, v_k_3655_);
    v___x_3657_ = l_Lean_Json_getNat_x3f(v___x_3656_);
    return v___x_3657_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1___boxed(
    mut v_j_3658_: *mut LeanObject,
    mut v_k_3659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3660_: *mut LeanObject = core::ptr::null_mut();
    v_res_3660_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1(v_j_3658_, v_k_3659_);
    lean_dec_ref(v_k_3659_);
    return v_res_3660_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__3()
-> *mut LeanObject {
    let mut v___x_3667_: u8 = 0;
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    v___x_3667_ = 1;
    v___x_3668_ = l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__2;
    v___x_3669_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3668_, v___x_3667_);
    return v___x_3669_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4()
-> *mut LeanObject {
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    v___x_3670_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6;
    v___x_3671_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__3,
    );
    v___x_3672_ = lean_string_append(v___x_3671_, v___x_3670_);
    return v___x_3672_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6()
-> *mut LeanObject {
    let mut v___x_3675_: u8 = 0;
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    v___x_3675_ = 1;
    v___x_3676_ = l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__5;
    v___x_3677_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3676_, v___x_3675_);
    return v___x_3677_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__7()
-> *mut LeanObject {
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    v___x_3678_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6,
    );
    v___x_3679_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4,
    );
    v___x_3680_ = lean_string_append(v___x_3679_, v___x_3678_);
    return v___x_3680_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__8()
-> *mut LeanObject {
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    v___x_3681_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_3682_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__7,
    );
    v___x_3683_ = lean_string_append(v___x_3682_, v___x_3681_);
    return v___x_3683_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__11()
-> *mut LeanObject {
    let mut v___x_3687_: u8 = 0;
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    v___x_3687_ = 1;
    v___x_3688_ = l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__10;
    v___x_3689_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3688_, v___x_3687_);
    return v___x_3689_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__12()
-> *mut LeanObject {
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    v___x_3690_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__11
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__11_once
        ),
        _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__11,
    );
    v___x_3691_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4,
    );
    v___x_3692_ = lean_string_append(v___x_3691_, v___x_3690_);
    return v___x_3692_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__13()
-> *mut LeanObject {
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    v___x_3693_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_3694_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__12_once
        ),
        _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__12,
    );
    v___x_3695_ = lean_string_append(v___x_3694_, v___x_3693_);
    return v___x_3695_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson(
    mut v_json_3696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3702_: u8 = 0;
    let mut v___x_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3708_: u8 = 0;
    let mut v_a_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3712_: u8 = 0;
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3716_: u8 = 0;
    let mut v_a_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3723_: u8 = 0;
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3729_: u8 = 0;
    let mut v_a_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3733_: u8 = 0;
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3737_: u8 = 0;
    let mut v_a_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3741_: u8 = 0;
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3746_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3697_ = l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0;
                lean_inc(v_json_3696_);
                v___x_3698_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_3696_, v___x_3697_);
                if lean_obj_tag(v___x_3698_) == 0 {
                    lean_dec(v_json_3696_);
                    v_a_3699_ = lean_ctor_get(v___x_3698_, 0);
                    v_isSharedCheck_3708_ = (!lean_is_exclusive(v___x_3698_)) as u8;
                    if v_isSharedCheck_3708_ == 0 {
                        v___x_3701_ = v___x_3698_;
                        v_isShared_3702_ = v_isSharedCheck_3708_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3699_);
                        lean_dec(v___x_3698_);
                        v___x_3701_ = lean_box(0);
                        v_isShared_3702_ = v_isSharedCheck_3708_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_3698_) == 0 {
                        lean_dec(v_json_3696_);
                        v_a_3709_ = lean_ctor_get(v___x_3698_, 0);
                        v_isSharedCheck_3716_ = (!lean_is_exclusive(v___x_3698_)) as u8;
                        if v_isSharedCheck_3716_ == 0 {
                            v___x_3711_ = v___x_3698_;
                            v_isShared_3712_ = v_isSharedCheck_3716_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3709_);
                            lean_dec(v___x_3698_);
                            v___x_3711_ = lean_box(0);
                            v_isShared_3712_ = v_isSharedCheck_3716_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3717_ = lean_ctor_get(v___x_3698_, 0);
                        lean_inc(v_a_3717_);
                        lean_dec_ref_known(v___x_3698_, 1);
                        v___x_3718_ =
                            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9;
                        v___x_3719_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1(v_json_3696_, v___x_3718_);
                        if lean_obj_tag(v___x_3719_) == 0 {
                            lean_dec(v_a_3717_);
                            v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
                            v_isSharedCheck_3729_ = (!lean_is_exclusive(v___x_3719_)) as u8;
                            if v_isSharedCheck_3729_ == 0 {
                                v___x_3722_ = v___x_3719_;
                                v_isShared_3723_ = v_isSharedCheck_3729_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_3720_);
                                lean_dec(v___x_3719_);
                                v___x_3722_ = lean_box(0);
                                v_isShared_3723_ = v_isSharedCheck_3729_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_3719_) == 0 {
                                lean_dec(v_a_3717_);
                                v_a_3730_ = lean_ctor_get(v___x_3719_, 0);
                                v_isSharedCheck_3737_ = (!lean_is_exclusive(v___x_3719_)) as u8;
                                if v_isSharedCheck_3737_ == 0 {
                                    v___x_3732_ = v___x_3719_;
                                    v_isShared_3733_ = v_isSharedCheck_3737_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_3730_);
                                    lean_dec(v___x_3719_);
                                    v___x_3732_ = lean_box(0);
                                    v_isShared_3733_ = v_isSharedCheck_3737_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_3738_ = lean_ctor_get(v___x_3719_, 0);
                                v_isSharedCheck_3746_ = (!lean_is_exclusive(v___x_3719_)) as u8;
                                if v_isSharedCheck_3746_ == 0 {
                                    v___x_3740_ = v___x_3719_;
                                    v_isShared_3741_ = v_isSharedCheck_3746_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_3738_);
                                    lean_dec(v___x_3719_);
                                    v___x_3740_ = lean_box(0);
                                    v_isShared_3741_ = v_isSharedCheck_3746_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3703_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__8_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__8,
                );
                v___x_3704_ = lean_string_append(v___x_3703_, v_a_3699_);
                lean_dec(v_a_3699_);
                if v_isShared_3702_ == 0 {
                    lean_ctor_set(v___x_3701_, 0, v___x_3704_);
                    v___x_3706_ = v___x_3701_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3704_);
                    v___x_3706_ = v_reuseFailAlloc_3707_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3706_;
            }
            3 => {
                if v_isShared_3712_ == 0 {
                    lean_ctor_set_tag(v___x_3711_, 0);
                    v___x_3714_ = v___x_3711_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
                    v___x_3714_ = v_reuseFailAlloc_3715_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3714_;
            }
            5 => {
                v___x_3724_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__13
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__13_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__13,
                );
                v___x_3725_ = lean_string_append(v___x_3724_, v_a_3720_);
                lean_dec(v_a_3720_);
                if v_isShared_3723_ == 0 {
                    lean_ctor_set(v___x_3722_, 0, v___x_3725_);
                    v___x_3727_ = v___x_3722_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3725_);
                    v___x_3727_ = v_reuseFailAlloc_3728_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3727_;
            }
            7 => {
                if v_isShared_3733_ == 0 {
                    lean_ctor_set_tag(v___x_3732_, 0);
                    v___x_3735_ = v___x_3732_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3736_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
                    v___x_3735_ = v_reuseFailAlloc_3736_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3735_;
            }
            9 => {
                v___x_3742_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3742_, 0, v_a_3717_);
                lean_ctor_set(v___x_3742_, 1, v_a_3738_);
                if v_isShared_3741_ == 0 {
                    lean_ctor_set(v___x_3740_, 0, v___x_3742_);
                    v___x_3744_ = v___x_3740_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3745_, 0, v___x_3742_);
                    v___x_3744_ = v_reuseFailAlloc_3745_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3744_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonWaitForDiagnosticsParams_toJson(
    mut v_x_3749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_uri_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_version_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3754_: u8 = 0;
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3772_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_uri_3750_ = lean_ctor_get(v_x_3749_, 0);
                v_version_3751_ = lean_ctor_get(v_x_3749_, 1);
                v_isSharedCheck_3772_ = (!lean_is_exclusive(v_x_3749_)) as u8;
                if v_isSharedCheck_3772_ == 0 {
                    v___x_3753_ = v_x_3749_;
                    v_isShared_3754_ = v_isSharedCheck_3772_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_version_3751_);
                    lean_inc(v_uri_3750_);
                    lean_dec(v_x_3749_);
                    v___x_3753_ = lean_box(0);
                    v_isShared_3754_ = v_isSharedCheck_3772_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3755_ = l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0;
                v___x_3756_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3756_, 0, v_uri_3750_);
                if v_isShared_3754_ == 0 {
                    lean_ctor_set(v___x_3753_, 1, v___x_3756_);
                    lean_ctor_set(v___x_3753_, 0, v___x_3755_);
                    v___x_3758_ = v___x_3753_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3755_);
                    lean_ctor_set(v_reuseFailAlloc_3771_, 1, v___x_3756_);
                    v___x_3758_ = v_reuseFailAlloc_3771_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3759_ = lean_box(0);
                v___x_3760_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3760_, 0, v___x_3758_);
                lean_ctor_set(v___x_3760_, 1, v___x_3759_);
                v___x_3761_ = l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9;
                v___x_3762_ = l_Lean_JsonNumber_fromNat(v_version_3751_);
                v___x_3763_ = lean_alloc_ctor(2, 1, (0) as u32);
                lean_ctor_set(v___x_3763_, 0, v___x_3762_);
                v___x_3764_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3764_, 0, v___x_3761_);
                lean_ctor_set(v___x_3764_, 1, v___x_3763_);
                v___x_3765_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3765_, 0, v___x_3764_);
                lean_ctor_set(v___x_3765_, 1, v___x_3759_);
                v___x_3766_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3766_, 0, v___x_3765_);
                lean_ctor_set(v___x_3766_, 1, v___x_3759_);
                v___x_3767_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3767_, 0, v___x_3760_);
                lean_ctor_set(v___x_3767_, 1, v___x_3766_);
                v___x_3768_ = l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0;
                v___x_3769_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_3767_, v___x_3768_);
                v___x_3770_ = l_Lean_Json_mkObj(v___x_3769_);
                lean_dec(v___x_3769_);
                return v___x_3770_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_WaitForDiagnostics_toCtorIdx(
    mut v_x_3775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    v___x_3776_ = lean_unsigned_to_nat(0);
    return v___x_3776_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0(
    mut v_x_3779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    v___x_3780_ = l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0___closed__0;
    return v___x_3780_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0___boxed(
    mut v_x_3781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3782_: *mut LeanObject = core::ptr::null_mut();
    v_res_3782_ = l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0(v_x_3781_);
    lean_dec(v_x_3781_);
    return v_res_3782_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0() -> *mut LeanObject
{
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    v___x_3785_ = lean_box(0);
    v___x_3786_ = l_Lean_Json_mkObj(v___x_3785_);
    return v___x_3786_;
}
pub unsafe fn l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0(
    mut v_x_3787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    v___x_3788_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0_once),
        _init_l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0,
    );
    return v___x_3788_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0(
    mut v_x_3793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3799_: u8 = 0;
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3803_: u8 = 0;
    let mut v_a_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3807_: u8 = 0;
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3812_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3793_) == 0 {
                    v___x_3794_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0___closed__0;
                    return v___x_3794_;
                } else {
                    v___x_3795_ = l_Lean_Json_getStr_x3f(v_x_3793_);
                    if lean_obj_tag(v___x_3795_) == 0 {
                        v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
                        v_isSharedCheck_3803_ = (!lean_is_exclusive(v___x_3795_)) as u8;
                        if v_isSharedCheck_3803_ == 0 {
                            v___x_3798_ = v___x_3795_;
                            v_isShared_3799_ = v_isSharedCheck_3803_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3796_);
                            lean_dec(v___x_3795_);
                            v___x_3798_ = lean_box(0);
                            v_isShared_3799_ = v_isSharedCheck_3803_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3804_ = lean_ctor_get(v___x_3795_, 0);
                        v_isSharedCheck_3812_ = (!lean_is_exclusive(v___x_3795_)) as u8;
                        if v_isSharedCheck_3812_ == 0 {
                            v___x_3806_ = v___x_3795_;
                            v_isShared_3807_ = v_isSharedCheck_3812_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3804_);
                            lean_dec(v___x_3795_);
                            v___x_3806_ = lean_box(0);
                            v_isShared_3807_ = v_isSharedCheck_3812_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3799_ == 0 {
                    v___x_3801_ = v___x_3798_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_a_3796_);
                    v___x_3801_ = v_reuseFailAlloc_3802_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3801_;
            }
            3 => {
                v___x_3808_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3808_, 0, v_a_3804_);
                if v_isShared_3807_ == 0 {
                    lean_ctor_set(v___x_3806_, 0, v___x_3808_);
                    v___x_3810_ = v___x_3806_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3811_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3811_, 0, v___x_3808_);
                    v___x_3810_ = v_reuseFailAlloc_3811_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3810_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0(
    mut v_j_3813_: *mut LeanObject,
    mut v_k_3814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut LeanObject = core::ptr::null_mut();
    v___x_3815_ = l_Lean_Json_getObjValD(v_j_3813_, v_k_3814_);
    v___x_3816_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0(v___x_3815_);
    return v___x_3816_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0___boxed(
    mut v_j_3817_: *mut LeanObject,
    mut v_k_3818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3819_: *mut LeanObject = core::ptr::null_mut();
    v_res_3819_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0(v_j_3817_, v_k_3818_);
    lean_dec_ref(v_k_3818_);
    return v_res_3819_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2(
    mut v_x_3822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3828_: u8 = 0;
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3832_: u8 = 0;
    let mut v_a_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3836_: u8 = 0;
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3841_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3822_) == 0 {
                    v___x_3823_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2___closed__0;
                    return v___x_3823_;
                } else {
                    v___x_3824_ = l_Lean_Json_getNat_x3f(v_x_3822_);
                    if lean_obj_tag(v___x_3824_) == 0 {
                        v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
                        v_isSharedCheck_3832_ = (!lean_is_exclusive(v___x_3824_)) as u8;
                        if v_isSharedCheck_3832_ == 0 {
                            v___x_3827_ = v___x_3824_;
                            v_isShared_3828_ = v_isSharedCheck_3832_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3825_);
                            lean_dec(v___x_3824_);
                            v___x_3827_ = lean_box(0);
                            v_isShared_3828_ = v_isSharedCheck_3832_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3833_ = lean_ctor_get(v___x_3824_, 0);
                        v_isSharedCheck_3841_ = (!lean_is_exclusive(v___x_3824_)) as u8;
                        if v_isSharedCheck_3841_ == 0 {
                            v___x_3835_ = v___x_3824_;
                            v_isShared_3836_ = v_isSharedCheck_3841_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3833_);
                            lean_dec(v___x_3824_);
                            v___x_3835_ = lean_box(0);
                            v_isShared_3836_ = v_isSharedCheck_3841_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3828_ == 0 {
                    v___x_3830_ = v___x_3827_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
                    v___x_3830_ = v_reuseFailAlloc_3831_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3830_;
            }
            3 => {
                v___x_3837_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3837_, 0, v_a_3833_);
                if v_isShared_3836_ == 0 {
                    lean_ctor_set(v___x_3835_, 0, v___x_3837_);
                    v___x_3839_ = v___x_3835_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3840_, 0, v___x_3837_);
                    v___x_3839_ = v_reuseFailAlloc_3840_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3839_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1(
    mut v_j_3842_: *mut LeanObject,
    mut v_k_3843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    v___x_3844_ = l_Lean_Json_getObjValD(v_j_3842_, v_k_3843_);
    v___x_3845_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2(v___x_3844_);
    return v___x_3845_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1___boxed(
    mut v_j_3846_: *mut LeanObject,
    mut v_k_3847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3848_: *mut LeanObject = core::ptr::null_mut();
    v_res_3848_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1(v_j_3846_, v_k_3847_);
    lean_dec_ref(v_k_3847_);
    return v_res_3848_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2()
-> *mut LeanObject {
    let mut v___x_3854_: u8 = 0;
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    v___x_3854_ = 1;
    v___x_3855_ = l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__1;
    v___x_3856_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3855_, v___x_3854_);
    return v___x_3856_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3()
-> *mut LeanObject {
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    v___x_3857_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6;
    v___x_3858_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2,
    );
    v___x_3859_ = lean_string_append(v___x_3858_, v___x_3857_);
    return v___x_3859_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6()
-> *mut LeanObject {
    let mut v___x_3863_: u8 = 0;
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    v___x_3863_ = 1;
    v___x_3864_ = l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__5;
    v___x_3865_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3864_, v___x_3863_);
    return v___x_3865_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7()
-> *mut LeanObject {
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    v___x_3866_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6,
    );
    v___x_3867_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3,
    );
    v___x_3868_ = lean_string_append(v___x_3867_, v___x_3866_);
    return v___x_3868_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8()
-> *mut LeanObject {
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    v___x_3869_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_3870_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7,
    );
    v___x_3871_ = lean_string_append(v___x_3870_, v___x_3869_);
    return v___x_3871_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11()
-> *mut LeanObject {
    let mut v___x_3875_: u8 = 0;
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    v___x_3875_ = 1;
    v___x_3876_ = l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__10;
    v___x_3877_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3876_, v___x_3875_);
    return v___x_3877_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12()
-> *mut LeanObject {
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    v___x_3878_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11_once
        ),
        _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11,
    );
    v___x_3879_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3,
    );
    v___x_3880_ = lean_string_append(v___x_3879_, v___x_3878_);
    return v___x_3880_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13()
-> *mut LeanObject {
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    v___x_3881_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_3882_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12_once
        ),
        _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12,
    );
    v___x_3883_ = lean_string_append(v___x_3882_, v___x_3881_);
    return v___x_3883_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson(
    mut v_json_3884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3890_: u8 = 0;
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3896_: u8 = 0;
    let mut v_a_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3900_: u8 = 0;
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3904_: u8 = 0;
    let mut v_a_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3911_: u8 = 0;
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3917_: u8 = 0;
    let mut v_a_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3921_: u8 = 0;
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3925_: u8 = 0;
    let mut v_a_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3929_: u8 = 0;
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3885_ = l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0;
                lean_inc(v_json_3884_);
                v___x_3886_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0(v_json_3884_, v___x_3885_);
                if lean_obj_tag(v___x_3886_) == 0 {
                    lean_dec(v_json_3884_);
                    v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
                    v_isSharedCheck_3896_ = (!lean_is_exclusive(v___x_3886_)) as u8;
                    if v_isSharedCheck_3896_ == 0 {
                        v___x_3889_ = v___x_3886_;
                        v_isShared_3890_ = v_isSharedCheck_3896_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3887_);
                        lean_dec(v___x_3886_);
                        v___x_3889_ = lean_box(0);
                        v_isShared_3890_ = v_isSharedCheck_3896_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_3886_) == 0 {
                        lean_dec(v_json_3884_);
                        v_a_3897_ = lean_ctor_get(v___x_3886_, 0);
                        v_isSharedCheck_3904_ = (!lean_is_exclusive(v___x_3886_)) as u8;
                        if v_isSharedCheck_3904_ == 0 {
                            v___x_3899_ = v___x_3886_;
                            v_isShared_3900_ = v_isSharedCheck_3904_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3897_);
                            lean_dec(v___x_3886_);
                            v___x_3899_ = lean_box(0);
                            v_isShared_3900_ = v_isSharedCheck_3904_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3905_ = lean_ctor_get(v___x_3886_, 0);
                        lean_inc(v_a_3905_);
                        lean_dec_ref_known(v___x_3886_, 1);
                        v___x_3906_ =
                            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9;
                        v___x_3907_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1(v_json_3884_, v___x_3906_);
                        if lean_obj_tag(v___x_3907_) == 0 {
                            lean_dec(v_a_3905_);
                            v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
                            v_isSharedCheck_3917_ = (!lean_is_exclusive(v___x_3907_)) as u8;
                            if v_isSharedCheck_3917_ == 0 {
                                v___x_3910_ = v___x_3907_;
                                v_isShared_3911_ = v_isSharedCheck_3917_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_3908_);
                                lean_dec(v___x_3907_);
                                v___x_3910_ = lean_box(0);
                                v_isShared_3911_ = v_isSharedCheck_3917_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_3907_) == 0 {
                                lean_dec(v_a_3905_);
                                v_a_3918_ = lean_ctor_get(v___x_3907_, 0);
                                v_isSharedCheck_3925_ = (!lean_is_exclusive(v___x_3907_)) as u8;
                                if v_isSharedCheck_3925_ == 0 {
                                    v___x_3920_ = v___x_3907_;
                                    v_isShared_3921_ = v_isSharedCheck_3925_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_3918_);
                                    lean_dec(v___x_3907_);
                                    v___x_3920_ = lean_box(0);
                                    v_isShared_3921_ = v_isSharedCheck_3925_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_3926_ = lean_ctor_get(v___x_3907_, 0);
                                v_isSharedCheck_3934_ = (!lean_is_exclusive(v___x_3907_)) as u8;
                                if v_isSharedCheck_3934_ == 0 {
                                    v___x_3928_ = v___x_3907_;
                                    v_isShared_3929_ = v_isSharedCheck_3934_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_3926_);
                                    lean_dec(v___x_3907_);
                                    v___x_3928_ = lean_box(0);
                                    v_isShared_3929_ = v_isSharedCheck_3934_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3891_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8,
                );
                v___x_3892_ = lean_string_append(v___x_3891_, v_a_3887_);
                lean_dec(v_a_3887_);
                if v_isShared_3890_ == 0 {
                    lean_ctor_set(v___x_3889_, 0, v___x_3892_);
                    v___x_3894_ = v___x_3889_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3895_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3895_, 0, v___x_3892_);
                    v___x_3894_ = v_reuseFailAlloc_3895_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3894_;
            }
            3 => {
                if v_isShared_3900_ == 0 {
                    lean_ctor_set_tag(v___x_3899_, 0);
                    v___x_3902_ = v___x_3899_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3903_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_a_3897_);
                    v___x_3902_ = v_reuseFailAlloc_3903_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3902_;
            }
            5 => {
                v___x_3912_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13,
                );
                v___x_3913_ = lean_string_append(v___x_3912_, v_a_3908_);
                lean_dec(v_a_3908_);
                if v_isShared_3911_ == 0 {
                    lean_ctor_set(v___x_3910_, 0, v___x_3913_);
                    v___x_3915_ = v___x_3910_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3913_);
                    v___x_3915_ = v_reuseFailAlloc_3916_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3915_;
            }
            7 => {
                if v_isShared_3921_ == 0 {
                    lean_ctor_set_tag(v___x_3920_, 0);
                    v___x_3923_ = v___x_3920_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3918_);
                    v___x_3923_ = v_reuseFailAlloc_3924_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3923_;
            }
            9 => {
                v___x_3930_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3930_, 0, v_a_3905_);
                lean_ctor_set(v___x_3930_, 1, v_a_3926_);
                if v_isShared_3929_ == 0 {
                    lean_ctor_set(v___x_3928_, 0, v___x_3930_);
                    v___x_3932_ = v___x_3928_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3933_, 0, v___x_3930_);
                    v___x_3932_ = v_reuseFailAlloc_3933_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3932_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWaitForILeansParams_toJson_spec__0(
    mut v_k_3937_: *mut LeanObject,
    mut v_x_3938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3943_: u8 = 0;
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3950_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3938_) == 0 {
                    lean_dec_ref(v_k_3937_);
                    v___x_3939_ = lean_box(0);
                    return v___x_3939_;
                } else {
                    v_val_3940_ = lean_ctor_get(v_x_3938_, 0);
                    v_isSharedCheck_3950_ = (!lean_is_exclusive(v_x_3938_)) as u8;
                    if v_isSharedCheck_3950_ == 0 {
                        v___x_3942_ = v_x_3938_;
                        v_isShared_3943_ = v_isSharedCheck_3950_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3940_);
                        lean_dec(v_x_3938_);
                        v___x_3942_ = lean_box(0);
                        v_isShared_3943_ = v_isSharedCheck_3950_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3943_ == 0 {
                    lean_ctor_set_tag(v___x_3942_, 3);
                    v___x_3945_ = v___x_3942_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3949_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_val_3940_);
                    v___x_3945_ = v_reuseFailAlloc_3949_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3946_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3946_, 0, v_k_3937_);
                lean_ctor_set(v___x_3946_, 1, v___x_3945_);
                v___x_3947_ = lean_box(0);
                v___x_3948_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3948_, 0, v___x_3946_);
                lean_ctor_set(v___x_3948_, 1, v___x_3947_);
                return v___x_3948_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWaitForILeansParams_toJson_spec__1(
    mut v_k_3951_: *mut LeanObject,
    mut v_x_3952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3957_: u8 = 0;
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3965_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3952_) == 0 {
                    lean_dec_ref(v_k_3951_);
                    v___x_3953_ = lean_box(0);
                    return v___x_3953_;
                } else {
                    v_val_3954_ = lean_ctor_get(v_x_3952_, 0);
                    v_isSharedCheck_3965_ = (!lean_is_exclusive(v_x_3952_)) as u8;
                    if v_isSharedCheck_3965_ == 0 {
                        v___x_3956_ = v_x_3952_;
                        v_isShared_3957_ = v_isSharedCheck_3965_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3954_);
                        lean_dec(v_x_3952_);
                        v___x_3956_ = lean_box(0);
                        v_isShared_3957_ = v_isSharedCheck_3965_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3958_ = l_Lean_JsonNumber_fromNat(v_val_3954_);
                if v_isShared_3957_ == 0 {
                    lean_ctor_set_tag(v___x_3956_, 2);
                    lean_ctor_set(v___x_3956_, 0, v___x_3958_);
                    v___x_3960_ = v___x_3956_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3964_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3964_, 0, v___x_3958_);
                    v___x_3960_ = v_reuseFailAlloc_3964_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3961_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3961_, 0, v_k_3951_);
                lean_ctor_set(v___x_3961_, 1, v___x_3960_);
                v___x_3962_ = lean_box(0);
                v___x_3963_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3963_, 0, v___x_3961_);
                lean_ctor_set(v___x_3963_, 1, v___x_3962_);
                return v___x_3963_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonWaitForILeansParams_toJson(
    mut v_x_3966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_uri_x3f_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_version_x3f_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3971_: u8 = 0;
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3984_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_uri_x3f_3967_ = lean_ctor_get(v_x_3966_, 0);
                v_version_x3f_3968_ = lean_ctor_get(v_x_3966_, 1);
                v_isSharedCheck_3984_ = (!lean_is_exclusive(v_x_3966_)) as u8;
                if v_isSharedCheck_3984_ == 0 {
                    v___x_3970_ = v_x_3966_;
                    v_isShared_3971_ = v_isSharedCheck_3984_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_version_x3f_3968_);
                    lean_inc(v_uri_x3f_3967_);
                    lean_dec(v_x_3966_);
                    v___x_3970_ = lean_box(0);
                    v_isShared_3971_ = v_isSharedCheck_3984_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3972_ = l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0;
                v___x_3973_ =
                    l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWaitForILeansParams_toJson_spec__0(
                        v___x_3972_,
                        v_uri_x3f_3967_,
                    );
                v___x_3974_ = l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9;
                v___x_3975_ =
                    l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWaitForILeansParams_toJson_spec__1(
                        v___x_3974_,
                        v_version_x3f_3968_,
                    );
                v___x_3976_ = lean_box(0);
                if v_isShared_3971_ == 0 {
                    lean_ctor_set_tag(v___x_3970_, 1);
                    lean_ctor_set(v___x_3970_, 1, v___x_3976_);
                    lean_ctor_set(v___x_3970_, 0, v___x_3975_);
                    v___x_3978_ = v___x_3970_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3983_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3983_, 0, v___x_3975_);
                    lean_ctor_set(v_reuseFailAlloc_3983_, 1, v___x_3976_);
                    v___x_3978_ = v_reuseFailAlloc_3983_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3979_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3979_, 0, v___x_3973_);
                lean_ctor_set(v___x_3979_, 1, v___x_3978_);
                v___x_3980_ = l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0;
                v___x_3981_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_3979_, v___x_3980_);
                v___x_3982_ = l_Lean_Json_mkObj(v___x_3981_);
                lean_dec(v___x_3981_);
                return v___x_3982_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_WaitForILeans_toCtorIdx(
    mut v_x_3987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    v___x_3988_ = lean_unsigned_to_nat(0);
    return v___x_3988_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonWaitForILeans_fromJson(
    mut v_json_3991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    v___x_3992_ = l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___closed__0;
    return v___x_3992_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___boxed(
    mut v_json_3993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3994_: *mut LeanObject = core::ptr::null_mut();
    v_res_3994_ = l_Lean_Lsp_instFromJsonWaitForILeans_fromJson(v_json_3993_);
    lean_dec(v_json_3993_);
    return v_res_3994_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0() -> *mut LeanObject {
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    v___x_3997_ = l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0;
    v___x_3998_ = lean_box(0);
    v___x_3999_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_3998_, v___x_3997_);
    return v___x_3999_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1() -> *mut LeanObject {
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    v___x_4000_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0_once),
        _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0,
    );
    v___x_4001_ = l_Lean_Json_mkObj(v___x_4000_);
    return v___x_4001_;
}
pub unsafe fn l_Lean_Lsp_instToJsonWaitForILeans_toJson(
    mut v_x_4002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    v___x_4003_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1_once),
        _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1,
    );
    return v___x_4003_;
}
pub unsafe fn l_Lean_Lsp_LeanFileProgressKind_ctorIdx(mut v_x_4006_: u8) -> *mut LeanObject {
    if v_x_4006_ == 0 {
        let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
        v___x_4007_ = lean_unsigned_to_nat(0);
        return v___x_4007_;
    } else {
        let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
        v___x_4008_ = lean_unsigned_to_nat(1);
        return v___x_4008_;
    }
}
pub unsafe fn l_Lean_Lsp_LeanFileProgressKind_ctorIdx___boxed(
    mut v_x_4009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_4010_: u8 = 0;
    let mut v_res_4011_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_4010_ = (lean_unbox(v_x_4009_) as u8);
    v_res_4011_ = l_Lean_Lsp_LeanFileProgressKind_ctorIdx(v_x_boxed_4010_);
    return v_res_4011_;
}
pub unsafe fn l_Lean_Lsp_LeanFileProgressKind_toCtorIdx(mut v_x_4012_: u8) -> *mut LeanObject {
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    v___x_4013_ = l_Lean_Lsp_LeanFileProgressKind_ctorIdx(v_x_4012_);
    return v___x_4013_;
}
pub unsafe fn l_Lean_Lsp_LeanFileProgressKind_toCtorIdx___boxed(
    mut v_x_4014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_4015_: u8 = 0;
    let mut v_res_4016_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_4015_ = (lean_unbox(v_x_4014_) as u8);
    v_res_4016_ = l_Lean_Lsp_LeanFileProgressKind_toCtorIdx(v_x_4__boxed_4015_);
    return v_res_4016_;
}
pub unsafe fn l_Lean_Lsp_LeanFileProgressKind_ctorElim___redArg(
    mut v_k_4017_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_4017_);
    return v_k_4017_;
}
pub unsafe fn l_Lean_Lsp_LeanFileProgressKind_ctorElim___redArg___boxed(
    mut v_k_4018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4019_: *mut LeanObject = core::ptr::null_mut();
    v_res_4019_ = l_Lean_Lsp_LeanFileProgressKind_ctorElim___redArg(v_k_4018_);
    lean_dec(v_k_4018_);
    return v_res_4019_;
}
pub unsafe fn l_Lean_Lsp_LeanFileProgressKind_ctorElim(
    mut v_motive_4020_: *mut LeanObject,
    mut v_ctorIdx_4021_: *mut LeanObject,
    mut v_t_4022_: u8,
    mut v_h_4023_: *mut LeanObject,
    mut v_k_4024_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_4024_);
    return v_k_4024_;
}
pub unsafe fn l_Lean_Lsp_LeanFileProgressKind_ctorElim___boxed(
    mut v_motive_4025_: *mut LeanObject,
    mut v_ctorIdx_4026_: *mut LeanObject,
    mut v_t_4027_: *mut LeanObject,
    mut v_h_4028_: *mut LeanObject,
    mut v_k_4029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4030_: u8 = 0;
    let mut v_res_4031_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4030_ = (lean_unbox(v_t_4027_) as u8);
    v_res_4031_ = l_Lean_Lsp_LeanFileProgressKind_ctorElim(
        v_motive_4025_,
        v_ctorIdx_4026_,
        v_t_boxed_4030_,
        v_h_4028_,
        v_k_4029_,
    );
    lean_dec(v_k_4029_);
    lean_dec(v_ctorIdx_4026_);
    return v_res_4031_;
}
pub unsafe fn l_Lean_Lsp_LeanFileProgressKind_processing_elim___redArg(
    mut v_processing_4032_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_processing_4032_);
    return v_processing_4032_;
}
pub unsafe fn l_Lean_Lsp_LeanFileProgressKind_processing_elim___redArg___boxed(
    mut v_processing_4033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4034_: *mut LeanObject = core::ptr::null_mut();
    v_res_4034_ = l_Lean_Lsp_LeanFileProgressKind_processing_elim___redArg(v_processing_4033_);
    lean_dec(v_processing_4033_);
    return v_res_4034_;
}
pub unsafe fn l_Lean_Lsp_LeanFileProgressKind_processing_elim(
    mut v_motive_4035_: *mut LeanObject,
    mut v_t_4036_: u8,
    mut v_h_4037_: *mut LeanObject,
    mut v_processing_4038_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_processing_4038_);
    return v_processing_4038_;
}
pub unsafe fn l_Lean_Lsp_LeanFileProgressKind_processing_elim___boxed(
    mut v_motive_4039_: *mut LeanObject,
    mut v_t_4040_: *mut LeanObject,
    mut v_h_4041_: *mut LeanObject,
    mut v_processing_4042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4043_: u8 = 0;
    let mut v_res_4044_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4043_ = (lean_unbox(v_t_4040_) as u8);
    v_res_4044_ = l_Lean_Lsp_LeanFileProgressKind_processing_elim(
        v_motive_4039_,
        v_t_boxed_4043_,
        v_h_4041_,
        v_processing_4042_,
    );
    lean_dec(v_processing_4042_);
    return v_res_4044_;
}
pub unsafe fn l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___redArg(
    mut v_fatalError_4045_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_fatalError_4045_);
    return v_fatalError_4045_;
}
pub unsafe fn l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___redArg___boxed(
    mut v_fatalError_4046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4047_: *mut LeanObject = core::ptr::null_mut();
    v_res_4047_ = l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___redArg(v_fatalError_4046_);
    lean_dec(v_fatalError_4046_);
    return v_res_4047_;
}
pub unsafe fn l_Lean_Lsp_LeanFileProgressKind_fatalError_elim(
    mut v_motive_4048_: *mut LeanObject,
    mut v_t_4049_: u8,
    mut v_h_4050_: *mut LeanObject,
    mut v_fatalError_4051_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_fatalError_4051_);
    return v_fatalError_4051_;
}
pub unsafe fn l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___boxed(
    mut v_motive_4052_: *mut LeanObject,
    mut v_t_4053_: *mut LeanObject,
    mut v_h_4054_: *mut LeanObject,
    mut v_fatalError_4055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4056_: u8 = 0;
    let mut v_res_4057_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4056_ = (lean_unbox(v_t_4053_) as u8);
    v_res_4057_ = l_Lean_Lsp_LeanFileProgressKind_fatalError_elim(
        v_motive_4052_,
        v_t_boxed_4056_,
        v_h_4054_,
        v_fatalError_4055_,
    );
    lean_dec(v_fatalError_4055_);
    return v_res_4057_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedLeanFileProgressKind_default() -> u8 {
    let mut v___x_4058_: u8 = 0;
    v___x_4058_ = 0;
    return v___x_4058_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedLeanFileProgressKind() -> u8 {
    let mut v___x_4059_: u8 = 0;
    v___x_4059_ = 0;
    return v___x_4059_;
}
pub unsafe fn l_Lean_Lsp_instBEqLeanFileProgressKind_beq(
    mut v_x_4060_: u8,
    mut v_y_4061_: u8,
) -> u8 {
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: u8 = 0;
    v___x_4062_ = l_Lean_Lsp_LeanFileProgressKind_ctorIdx(v_x_4060_);
    v___x_4063_ = l_Lean_Lsp_LeanFileProgressKind_ctorIdx(v_y_4061_);
    v___x_4064_ = lean_nat_dec_eq(v___x_4062_, v___x_4063_);
    lean_dec(v___x_4063_);
    lean_dec(v___x_4062_);
    return v___x_4064_;
}
pub unsafe fn l_Lean_Lsp_instBEqLeanFileProgressKind_beq___boxed(
    mut v_x_4065_: *mut LeanObject,
    mut v_y_4066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_17__boxed_4067_: u8 = 0;
    let mut v_y_18__boxed_4068_: u8 = 0;
    let mut v_res_4069_: u8 = 0;
    let mut v_r_4070_: *mut LeanObject = core::ptr::null_mut();
    v_x_17__boxed_4067_ = (lean_unbox(v_x_4065_) as u8);
    v_y_18__boxed_4068_ = (lean_unbox(v_y_4066_) as u8);
    v_res_4069_ =
        l_Lean_Lsp_instBEqLeanFileProgressKind_beq(v_x_17__boxed_4067_, v_y_18__boxed_4068_);
    v_r_4070_ = lean_box((v_res_4069_) as usize);
    return v_r_4070_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0(
    mut v_j_4081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: u8 = 0;
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: u8 = 0;
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_j_4081_);
                v___x_4090_ = l_Lean_Json_getNat_x3f(v_j_4081_);
                if lean_obj_tag(v___x_4090_) == 1 {
                    v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
                    lean_inc(v_a_4091_);
                    lean_dec_ref_known(v___x_4090_, 1);
                    v___x_4092_ = lean_unsigned_to_nat(1);
                    v___x_4093_ = lean_nat_dec_eq(v_a_4091_, v___x_4092_);
                    if v___x_4093_ == 0 {
                        v___x_4094_ = lean_unsigned_to_nat(2);
                        v___x_4095_ = lean_nat_dec_eq(v_a_4091_, v___x_4094_);
                        lean_dec(v_a_4091_);
                        if v___x_4095_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_j_4081_);
                            v___x_4096_ =
                                l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__2;
                            return v___x_4096_;
                        }
                    } else {
                        lean_dec(v_a_4091_);
                        lean_dec(v_j_4081_);
                        v___x_4097_ =
                            l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__3;
                        return v___x_4097_;
                    }
                } else {
                    lean_dec_ref(v___x_4090_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4083_ = l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__0;
                v___x_4084_ = lean_unsigned_to_nat(80);
                v___x_4085_ = l_Lean_Json_pretty(v_j_4081_, v___x_4084_);
                v___x_4086_ = lean_string_append(v___x_4083_, v___x_4085_);
                lean_dec_ref(v___x_4085_);
                v___x_4087_ = l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1;
                v___x_4088_ = lean_string_append(v___x_4086_, v___x_4087_);
                v___x_4089_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4089_, 0, v___x_4088_);
                return v___x_4089_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    v___x_4100_ = lean_unsigned_to_nat(1);
    v___x_4101_ = l_Lean_JsonNumber_fromNat(v___x_4100_);
    return v___x_4101_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    v___x_4102_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0_once
        ),
        _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0,
    );
    v___x_4103_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_4103_, 0, v___x_4102_);
    return v___x_4103_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    v___x_4104_ = lean_unsigned_to_nat(2);
    v___x_4105_ = l_Lean_JsonNumber_fromNat(v___x_4104_);
    return v___x_4105_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    v___x_4106_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2_once
        ),
        _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2,
    );
    v___x_4107_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_4107_, 0, v___x_4106_);
    return v___x_4107_;
}
pub unsafe fn l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0(
    mut v_x_4108_: u8,
) -> *mut LeanObject {
    if v_x_4108_ == 0 {
        let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
        v___x_4109_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1_once
            ),
            _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1,
        );
        return v___x_4109_;
    } else {
        let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
        v___x_4110_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3),
            core::ptr::addr_of_mut!(
                l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3_once
            ),
            _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3,
        );
        return v___x_4110_;
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___boxed(
    mut v_x_4111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_56__boxed_4112_: u8 = 0;
    let mut v_res_4113_: *mut LeanObject = core::ptr::null_mut();
    v_x_56__boxed_4112_ = (lean_unbox(v_x_4111_) as u8);
    v_res_4113_ = l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0(v_x_56__boxed_4112_);
    return v_res_4113_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(
    mut v_j_4116_: *mut LeanObject,
    mut v_k_4117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    v___x_4118_ = l_Lean_Json_getObjValD(v_j_4116_, v_k_4117_);
    v___x_4119_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_4118_);
    return v___x_4119_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0___boxed(
    mut v_j_4120_: *mut LeanObject,
    mut v_k_4121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4122_: *mut LeanObject = core::ptr::null_mut();
    v_res_4122_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(v_j_4120_, v_k_4121_);
    lean_dec_ref(v_k_4121_);
    return v_res_4122_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1(
    mut v_j_4123_: *mut LeanObject,
    mut v_k_4124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: u8 = 0;
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: u8 = 0;
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4125_ = l_Lean_Json_getObjValD(v_j_4123_, v_k_4124_);
                lean_inc(v___x_4125_);
                v___x_4134_ = l_Lean_Json_getNat_x3f(v___x_4125_);
                if lean_obj_tag(v___x_4134_) == 1 {
                    v_a_4135_ = lean_ctor_get(v___x_4134_, 0);
                    lean_inc(v_a_4135_);
                    lean_dec_ref_known(v___x_4134_, 1);
                    v___x_4136_ = lean_unsigned_to_nat(1);
                    v___x_4137_ = lean_nat_dec_eq(v_a_4135_, v___x_4136_);
                    if v___x_4137_ == 0 {
                        v___x_4138_ = lean_unsigned_to_nat(2);
                        v___x_4139_ = lean_nat_dec_eq(v_a_4135_, v___x_4138_);
                        lean_dec(v_a_4135_);
                        if v___x_4139_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_4125_);
                            v___x_4140_ =
                                l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__2;
                            return v___x_4140_;
                        }
                    } else {
                        lean_dec(v_a_4135_);
                        lean_dec(v___x_4125_);
                        v___x_4141_ =
                            l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__3;
                        return v___x_4141_;
                    }
                } else {
                    lean_dec_ref(v___x_4134_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4127_ = l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__0;
                v___x_4128_ = lean_unsigned_to_nat(80);
                v___x_4129_ = l_Lean_Json_pretty(v___x_4125_, v___x_4128_);
                v___x_4130_ = lean_string_append(v___x_4127_, v___x_4129_);
                lean_dec_ref(v___x_4129_);
                v___x_4131_ = l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1;
                v___x_4132_ = lean_string_append(v___x_4130_, v___x_4131_);
                v___x_4133_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4133_, 0, v___x_4132_);
                return v___x_4133_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1___boxed(
    mut v_j_4142_: *mut LeanObject,
    mut v_k_4143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4144_: *mut LeanObject = core::ptr::null_mut();
    v_res_4144_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1(v_j_4142_, v_k_4143_);
    lean_dec_ref(v_k_4143_);
    return v_res_4144_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3()
-> *mut LeanObject {
    let mut v___x_4151_: u8 = 0;
    let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    v___x_4151_ = 1;
    v___x_4152_ = l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__2;
    v___x_4153_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4152_, v___x_4151_);
    return v___x_4153_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4()
-> *mut LeanObject {
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    v___x_4154_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6;
    v___x_4155_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3,
    );
    v___x_4156_ = lean_string_append(v___x_4155_, v___x_4154_);
    return v___x_4156_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6()
-> *mut LeanObject {
    let mut v___x_4159_: u8 = 0;
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    v___x_4159_ = 1;
    v___x_4160_ = l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__5;
    v___x_4161_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4160_, v___x_4159_);
    return v___x_4161_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7()
-> *mut LeanObject {
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    v___x_4162_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6,
    );
    v___x_4163_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4,
    );
    v___x_4164_ = lean_string_append(v___x_4163_, v___x_4162_);
    return v___x_4164_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8()
-> *mut LeanObject {
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    v___x_4165_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_4166_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7,
    );
    v___x_4167_ = lean_string_append(v___x_4166_, v___x_4165_);
    return v___x_4167_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11()
-> *mut LeanObject {
    let mut v___x_4171_: u8 = 0;
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    v___x_4171_ = 1;
    v___x_4172_ = l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__10;
    v___x_4173_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4172_, v___x_4171_);
    return v___x_4173_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12()
-> *mut LeanObject {
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    v___x_4174_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11,
    );
    v___x_4175_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4,
    );
    v___x_4176_ = lean_string_append(v___x_4175_, v___x_4174_);
    return v___x_4176_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13()
-> *mut LeanObject {
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    v___x_4177_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_4178_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12,
    );
    v___x_4179_ = lean_string_append(v___x_4178_, v___x_4177_);
    return v___x_4179_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson(
    mut v_json_4180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4186_: u8 = 0;
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4192_: u8 = 0;
    let mut v_a_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4196_: u8 = 0;
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4200_: u8 = 0;
    let mut v_a_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4207_: u8 = 0;
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4213_: u8 = 0;
    let mut v_a_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4217_: u8 = 0;
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4221_: u8 = 0;
    let mut v_a_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4225_: u8 = 0;
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: u8 = 0;
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4231_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4181_ =
                    l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0;
                lean_inc(v_json_4180_);
                v___x_4182_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(v_json_4180_, v___x_4181_);
                if lean_obj_tag(v___x_4182_) == 0 {
                    lean_dec(v_json_4180_);
                    v_a_4183_ = lean_ctor_get(v___x_4182_, 0);
                    v_isSharedCheck_4192_ = (!lean_is_exclusive(v___x_4182_)) as u8;
                    if v_isSharedCheck_4192_ == 0 {
                        v___x_4185_ = v___x_4182_;
                        v_isShared_4186_ = v_isSharedCheck_4192_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4183_);
                        lean_dec(v___x_4182_);
                        v___x_4185_ = lean_box(0);
                        v_isShared_4186_ = v_isSharedCheck_4192_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_4182_) == 0 {
                        lean_dec(v_json_4180_);
                        v_a_4193_ = lean_ctor_get(v___x_4182_, 0);
                        v_isSharedCheck_4200_ = (!lean_is_exclusive(v___x_4182_)) as u8;
                        if v_isSharedCheck_4200_ == 0 {
                            v___x_4195_ = v___x_4182_;
                            v_isShared_4196_ = v_isSharedCheck_4200_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4193_);
                            lean_dec(v___x_4182_);
                            v___x_4195_ = lean_box(0);
                            v_isShared_4196_ = v_isSharedCheck_4200_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4201_ = lean_ctor_get(v___x_4182_, 0);
                        lean_inc(v_a_4201_);
                        lean_dec_ref_known(v___x_4182_, 1);
                        v___x_4202_ = l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9;
                        v___x_4203_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1(v_json_4180_, v___x_4202_);
                        if lean_obj_tag(v___x_4203_) == 0 {
                            lean_dec(v_a_4201_);
                            v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
                            v_isSharedCheck_4213_ = (!lean_is_exclusive(v___x_4203_)) as u8;
                            if v_isSharedCheck_4213_ == 0 {
                                v___x_4206_ = v___x_4203_;
                                v_isShared_4207_ = v_isSharedCheck_4213_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_4204_);
                                lean_dec(v___x_4203_);
                                v___x_4206_ = lean_box(0);
                                v_isShared_4207_ = v_isSharedCheck_4213_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_4203_) == 0 {
                                lean_dec(v_a_4201_);
                                v_a_4214_ = lean_ctor_get(v___x_4203_, 0);
                                v_isSharedCheck_4221_ = (!lean_is_exclusive(v___x_4203_)) as u8;
                                if v_isSharedCheck_4221_ == 0 {
                                    v___x_4216_ = v___x_4203_;
                                    v_isShared_4217_ = v_isSharedCheck_4221_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_4214_);
                                    lean_dec(v___x_4203_);
                                    v___x_4216_ = lean_box(0);
                                    v_isShared_4217_ = v_isSharedCheck_4221_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_4222_ = lean_ctor_get(v___x_4203_, 0);
                                v_isSharedCheck_4231_ = (!lean_is_exclusive(v___x_4203_)) as u8;
                                if v_isSharedCheck_4231_ == 0 {
                                    v___x_4224_ = v___x_4203_;
                                    v_isShared_4225_ = v_isSharedCheck_4231_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_4222_);
                                    lean_dec(v___x_4203_);
                                    v___x_4224_ = lean_box(0);
                                    v_isShared_4225_ = v_isSharedCheck_4231_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4187_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8_once), _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8);
                v___x_4188_ = lean_string_append(v___x_4187_, v_a_4183_);
                lean_dec(v_a_4183_);
                if v_isShared_4186_ == 0 {
                    lean_ctor_set(v___x_4185_, 0, v___x_4188_);
                    v___x_4190_ = v___x_4185_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4191_, 0, v___x_4188_);
                    v___x_4190_ = v_reuseFailAlloc_4191_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4190_;
            }
            3 => {
                if v_isShared_4196_ == 0 {
                    lean_ctor_set_tag(v___x_4195_, 0);
                    v___x_4198_ = v___x_4195_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4199_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4199_, 0, v_a_4193_);
                    v___x_4198_ = v_reuseFailAlloc_4199_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4198_;
            }
            5 => {
                v___x_4208_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13_once), _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13);
                v___x_4209_ = lean_string_append(v___x_4208_, v_a_4204_);
                lean_dec(v_a_4204_);
                if v_isShared_4207_ == 0 {
                    lean_ctor_set(v___x_4206_, 0, v___x_4209_);
                    v___x_4211_ = v___x_4206_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4212_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4212_, 0, v___x_4209_);
                    v___x_4211_ = v_reuseFailAlloc_4212_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4211_;
            }
            7 => {
                if v_isShared_4217_ == 0 {
                    lean_ctor_set_tag(v___x_4216_, 0);
                    v___x_4219_ = v___x_4216_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_a_4214_);
                    v___x_4219_ = v_reuseFailAlloc_4220_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4219_;
            }
            9 => {
                v___x_4226_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_4226_, 0, v_a_4201_);
                v___x_4227_ = (lean_unbox(v_a_4222_) as u8);
                lean_dec(v_a_4222_);
                lean_ctor_set_uint8(
                    v___x_4226_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4227_,
                );
                if v_isShared_4225_ == 0 {
                    lean_ctor_set(v___x_4224_, 0, v___x_4226_);
                    v___x_4229_ = v___x_4224_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4230_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4226_);
                    v___x_4229_ = v_reuseFailAlloc_4230_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4229_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo_toJson(
    mut v_x_4234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_range_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_4236_: u8 = 0;
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_4235_ = lean_ctor_get(v_x_4234_, 0);
                lean_inc_ref(v_range_4235_);
                v_kind_4236_ = lean_ctor_get_uint8(
                    v_x_4234_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                lean_dec_ref(v_x_4234_);
                v___x_4237_ =
                    l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0;
                v___x_4238_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_4235_);
                v___x_4239_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4239_, 0, v___x_4237_);
                lean_ctor_set(v___x_4239_, 1, v___x_4238_);
                v___x_4240_ = lean_box(0);
                v___x_4241_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4241_, 0, v___x_4239_);
                lean_ctor_set(v___x_4241_, 1, v___x_4240_);
                v___x_4242_ =
                    l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9;
                if v_kind_4236_ == 0 {
                    v___x_4252_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1_once
                        ),
                        _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1,
                    );
                    v___y_4244_ = v___x_4252_;
                    state = 1;
                    continue;
                } else {
                    v___x_4253_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3_once
                        ),
                        _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3,
                    );
                    v___y_4244_ = v___x_4253_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v___y_4244_);
                v___x_4245_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4245_, 0, v___x_4242_);
                lean_ctor_set(v___x_4245_, 1, v___y_4244_);
                v___x_4246_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4246_, 0, v___x_4245_);
                lean_ctor_set(v___x_4246_, 1, v___x_4240_);
                v___x_4247_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4247_, 0, v___x_4246_);
                lean_ctor_set(v___x_4247_, 1, v___x_4240_);
                v___x_4248_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4248_, 0, v___x_4241_);
                lean_ctor_set(v___x_4248_, 1, v___x_4247_);
                v___x_4249_ = l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0;
                v___x_4250_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_4248_, v___x_4249_);
                v___x_4251_ = l_Lean_Json_mkObj(v___x_4250_);
                lean_dec(v___x_4250_);
                return v___x_4251_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0(
    mut v_j_4256_: *mut LeanObject,
    mut v_k_4257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    v___x_4258_ = l_Lean_Json_getObjValD(v_j_4256_, v_k_4257_);
    v___x_4259_ = l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(v___x_4258_);
    return v___x_4259_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0___boxed(
    mut v_j_4260_: *mut LeanObject,
    mut v_k_4261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4262_: *mut LeanObject = core::ptr::null_mut();
    v_res_4262_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0(v_j_4260_, v_k_4261_);
    lean_dec_ref(v_k_4261_);
    return v_res_4262_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2(
    mut v_sz_4263_: usize,
    mut v_i_4264_: usize,
    mut v_bs_4265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4266_: u8 = 0;
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4273_: u8 = 0;
    let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4277_: u8 = 0;
    let mut v_a_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: usize = 0;
    let mut v___x_4282_: usize = 0;
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4266_ = lean_usize_dec_lt(v_i_4264_, v_sz_4263_);
                if v___x_4266_ == 0 {
                    v___x_4267_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4267_, 0, v_bs_4265_);
                    return v___x_4267_;
                } else {
                    v_v_4268_ = lean_array_uget_borrowed(v_bs_4265_, v_i_4264_);
                    lean_inc(v_v_4268_);
                    v___x_4269_ =
                        l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson(v_v_4268_);
                    if lean_obj_tag(v___x_4269_) == 0 {
                        lean_dec_ref(v_bs_4265_);
                        v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
                        v_isSharedCheck_4277_ = (!lean_is_exclusive(v___x_4269_)) as u8;
                        if v_isSharedCheck_4277_ == 0 {
                            v___x_4272_ = v___x_4269_;
                            v_isShared_4273_ = v_isSharedCheck_4277_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4270_);
                            lean_dec(v___x_4269_);
                            v___x_4272_ = lean_box(0);
                            v_isShared_4273_ = v_isSharedCheck_4277_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4278_ = lean_ctor_get(v___x_4269_, 0);
                        lean_inc(v_a_4278_);
                        lean_dec_ref_known(v___x_4269_, 1);
                        v___x_4279_ = lean_unsigned_to_nat(0);
                        v_bs_x27_4280_ = lean_array_uset(v_bs_4265_, v_i_4264_, v___x_4279_);
                        v___x_4281_ = 1usize;
                        v___x_4282_ = lean_usize_add(v_i_4264_, v___x_4281_);
                        v___x_4283_ = lean_array_uset(v_bs_x27_4280_, v_i_4264_, v_a_4278_);
                        v_i_4264_ = v___x_4282_;
                        v_bs_4265_ = v___x_4283_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4273_ == 0 {
                    v___x_4275_ = v___x_4272_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4276_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4276_, 0, v_a_4270_);
                    v___x_4275_ = v_reuseFailAlloc_4276_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4275_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2___boxed(
    mut v_sz_4285_: *mut LeanObject,
    mut v_i_4286_: *mut LeanObject,
    mut v_bs_4287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4288_: usize = 0;
    let mut v_i_boxed_4289_: usize = 0;
    let mut v_res_4290_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4288_ = lean_unbox_usize(v_sz_4285_);
    lean_dec(v_sz_4285_);
    v_i_boxed_4289_ = lean_unbox_usize(v_i_4286_);
    lean_dec(v_i_4286_);
    v_res_4290_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_4288_, v_i_boxed_4289_, v_bs_4287_);
    return v_res_4290_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1(
    mut v_x_4292_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4292_) == 4 {
        let mut v_elems_4293_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_4294_: usize = 0;
        let mut v___x_4295_: usize = 0;
        let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
        v_elems_4293_ = lean_ctor_get(v_x_4292_, 0);
        lean_inc_ref(v_elems_4293_);
        lean_dec_ref_known(v_x_4292_, 1);
        v_sz_4294_ = lean_array_size(v_elems_4293_);
        v___x_4295_ = 0usize;
        v___x_4296_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2(v_sz_4294_, v___x_4295_, v_elems_4293_);
        return v___x_4296_;
    } else {
        let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
        v___x_4297_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0;
        v___x_4298_ = lean_unsigned_to_nat(80);
        v___x_4299_ = l_Lean_Json_pretty(v_x_4292_, v___x_4298_);
        v___x_4300_ = lean_string_append(v___x_4297_, v___x_4299_);
        lean_dec_ref(v___x_4299_);
        v___x_4301_ = l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1;
        v___x_4302_ = lean_string_append(v___x_4300_, v___x_4301_);
        v___x_4303_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4303_, 0, v___x_4302_);
        return v___x_4303_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1(
    mut v_j_4304_: *mut LeanObject,
    mut v_k_4305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    v___x_4306_ = l_Lean_Json_getObjValD(v_j_4304_, v_k_4305_);
    v___x_4307_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1(v___x_4306_);
    return v___x_4307_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1___boxed(
    mut v_j_4308_: *mut LeanObject,
    mut v_k_4309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4310_: *mut LeanObject = core::ptr::null_mut();
    v_res_4310_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1(v_j_4308_, v_k_4309_);
    lean_dec_ref(v_k_4309_);
    return v_res_4310_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2()
-> *mut LeanObject {
    let mut v___x_4316_: u8 = 0;
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    v___x_4316_ = 1;
    v___x_4317_ = l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__1;
    v___x_4318_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4317_, v___x_4316_);
    return v___x_4318_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3()
-> *mut LeanObject {
    let mut v___x_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    v___x_4319_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6;
    v___x_4320_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2,
    );
    v___x_4321_ = lean_string_append(v___x_4320_, v___x_4319_);
    return v___x_4321_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4()
-> *mut LeanObject {
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    v___x_4322_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9,
    );
    v___x_4323_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3,
    );
    v___x_4324_ = lean_string_append(v___x_4323_, v___x_4322_);
    return v___x_4324_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5()
-> *mut LeanObject {
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
    v___x_4325_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_4326_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4,
    );
    v___x_4327_ = lean_string_append(v___x_4326_, v___x_4325_);
    return v___x_4327_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8()
-> *mut LeanObject {
    let mut v___x_4331_: u8 = 0;
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    v___x_4331_ = 1;
    v___x_4332_ = l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__7;
    v___x_4333_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4332_, v___x_4331_);
    return v___x_4333_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9()
-> *mut LeanObject {
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    v___x_4334_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8,
    );
    v___x_4335_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3,
    );
    v___x_4336_ = lean_string_append(v___x_4335_, v___x_4334_);
    return v___x_4336_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10()
-> *mut LeanObject {
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    v___x_4337_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_4338_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9,
    );
    v___x_4339_ = lean_string_append(v___x_4338_, v___x_4337_);
    return v___x_4339_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson(
    mut v_json_4340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4346_: u8 = 0;
    let mut v___x_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4352_: u8 = 0;
    let mut v_a_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4356_: u8 = 0;
    let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4360_: u8 = 0;
    let mut v_a_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4367_: u8 = 0;
    let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4373_: u8 = 0;
    let mut v_a_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4377_: u8 = 0;
    let mut v___x_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4381_: u8 = 0;
    let mut v_a_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4385_: u8 = 0;
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4390_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4341_ =
                    l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0;
                lean_inc(v_json_4340_);
                v___x_4342_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0(v_json_4340_, v___x_4341_);
                if lean_obj_tag(v___x_4342_) == 0 {
                    lean_dec(v_json_4340_);
                    v_a_4343_ = lean_ctor_get(v___x_4342_, 0);
                    v_isSharedCheck_4352_ = (!lean_is_exclusive(v___x_4342_)) as u8;
                    if v_isSharedCheck_4352_ == 0 {
                        v___x_4345_ = v___x_4342_;
                        v_isShared_4346_ = v_isSharedCheck_4352_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4343_);
                        lean_dec(v___x_4342_);
                        v___x_4345_ = lean_box(0);
                        v_isShared_4346_ = v_isSharedCheck_4352_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_4342_) == 0 {
                        lean_dec(v_json_4340_);
                        v_a_4353_ = lean_ctor_get(v___x_4342_, 0);
                        v_isSharedCheck_4360_ = (!lean_is_exclusive(v___x_4342_)) as u8;
                        if v_isSharedCheck_4360_ == 0 {
                            v___x_4355_ = v___x_4342_;
                            v_isShared_4356_ = v_isSharedCheck_4360_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4353_);
                            lean_dec(v___x_4342_);
                            v___x_4355_ = lean_box(0);
                            v_isShared_4356_ = v_isSharedCheck_4360_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4361_ = lean_ctor_get(v___x_4342_, 0);
                        lean_inc(v_a_4361_);
                        lean_dec_ref_known(v___x_4342_, 1);
                        v___x_4362_ =
                            l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__6;
                        v___x_4363_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1(v_json_4340_, v___x_4362_);
                        if lean_obj_tag(v___x_4363_) == 0 {
                            lean_dec(v_a_4361_);
                            v_a_4364_ = lean_ctor_get(v___x_4363_, 0);
                            v_isSharedCheck_4373_ = (!lean_is_exclusive(v___x_4363_)) as u8;
                            if v_isSharedCheck_4373_ == 0 {
                                v___x_4366_ = v___x_4363_;
                                v_isShared_4367_ = v_isSharedCheck_4373_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_4364_);
                                lean_dec(v___x_4363_);
                                v___x_4366_ = lean_box(0);
                                v_isShared_4367_ = v_isSharedCheck_4373_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_4363_) == 0 {
                                lean_dec(v_a_4361_);
                                v_a_4374_ = lean_ctor_get(v___x_4363_, 0);
                                v_isSharedCheck_4381_ = (!lean_is_exclusive(v___x_4363_)) as u8;
                                if v_isSharedCheck_4381_ == 0 {
                                    v___x_4376_ = v___x_4363_;
                                    v_isShared_4377_ = v_isSharedCheck_4381_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_4374_);
                                    lean_dec(v___x_4363_);
                                    v___x_4376_ = lean_box(0);
                                    v_isShared_4377_ = v_isSharedCheck_4381_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_4382_ = lean_ctor_get(v___x_4363_, 0);
                                v_isSharedCheck_4390_ = (!lean_is_exclusive(v___x_4363_)) as u8;
                                if v_isSharedCheck_4390_ == 0 {
                                    v___x_4384_ = v___x_4363_;
                                    v_isShared_4385_ = v_isSharedCheck_4390_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_4382_);
                                    lean_dec(v___x_4363_);
                                    v___x_4384_ = lean_box(0);
                                    v_isShared_4385_ = v_isSharedCheck_4390_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4347_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5,
                );
                v___x_4348_ = lean_string_append(v___x_4347_, v_a_4343_);
                lean_dec(v_a_4343_);
                if v_isShared_4346_ == 0 {
                    lean_ctor_set(v___x_4345_, 0, v___x_4348_);
                    v___x_4350_ = v___x_4345_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4351_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4351_, 0, v___x_4348_);
                    v___x_4350_ = v_reuseFailAlloc_4351_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4350_;
            }
            3 => {
                if v_isShared_4356_ == 0 {
                    lean_ctor_set_tag(v___x_4355_, 0);
                    v___x_4358_ = v___x_4355_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4359_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4359_, 0, v_a_4353_);
                    v___x_4358_ = v_reuseFailAlloc_4359_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4358_;
            }
            5 => {
                v___x_4368_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10,
                );
                v___x_4369_ = lean_string_append(v___x_4368_, v_a_4364_);
                lean_dec(v_a_4364_);
                if v_isShared_4367_ == 0 {
                    lean_ctor_set(v___x_4366_, 0, v___x_4369_);
                    v___x_4371_ = v___x_4366_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4372_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4372_, 0, v___x_4369_);
                    v___x_4371_ = v_reuseFailAlloc_4372_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4371_;
            }
            7 => {
                if v_isShared_4377_ == 0 {
                    lean_ctor_set_tag(v___x_4376_, 0);
                    v___x_4379_ = v___x_4376_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4380_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4380_, 0, v_a_4374_);
                    v___x_4379_ = v_reuseFailAlloc_4380_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4379_;
            }
            9 => {
                v___x_4386_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4386_, 0, v_a_4361_);
                lean_ctor_set(v___x_4386_, 1, v_a_4382_);
                if v_isShared_4385_ == 0 {
                    lean_ctor_set(v___x_4384_, 0, v___x_4386_);
                    v___x_4388_ = v___x_4384_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4389_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4389_, 0, v___x_4386_);
                    v___x_4388_ = v_reuseFailAlloc_4389_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4388_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0(
    mut v_sz_4393_: usize,
    mut v_i_4394_: usize,
    mut v_bs_4395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4396_: u8 = 0;
    let mut v_v_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: usize = 0;
    let mut v___x_4402_: usize = 0;
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4396_ = lean_usize_dec_lt(v_i_4394_, v_sz_4393_);
                if v___x_4396_ == 0 {
                    return v_bs_4395_;
                } else {
                    v_v_4397_ = lean_array_uget(v_bs_4395_, v_i_4394_);
                    v___x_4398_ = lean_unsigned_to_nat(0);
                    v_bs_x27_4399_ = lean_array_uset(v_bs_4395_, v_i_4394_, v___x_4398_);
                    v___x_4400_ =
                        l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo_toJson(v_v_4397_);
                    v___x_4401_ = 1usize;
                    v___x_4402_ = lean_usize_add(v_i_4394_, v___x_4401_);
                    v___x_4403_ = lean_array_uset(v_bs_x27_4399_, v_i_4394_, v___x_4400_);
                    v_i_4394_ = v___x_4402_;
                    v_bs_4395_ = v___x_4403_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0___boxed(
    mut v_sz_4405_: *mut LeanObject,
    mut v_i_4406_: *mut LeanObject,
    mut v_bs_4407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4408_: usize = 0;
    let mut v_i_boxed_4409_: usize = 0;
    let mut v_res_4410_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4408_ = lean_unbox_usize(v_sz_4405_);
    lean_dec(v_sz_4405_);
    v_i_boxed_4409_ = lean_unbox_usize(v_i_4406_);
    lean_dec(v_i_4406_);
    v_res_4410_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0(v_sz_boxed_4408_, v_i_boxed_4409_, v_bs_4407_);
    return v_res_4410_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0(
    mut v_a_4411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_4412_: usize = 0;
    let mut v___x_4413_: usize = 0;
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    v_sz_4412_ = lean_array_size(v_a_4411_);
    v___x_4413_ = 0usize;
    v___x_4414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0(v_sz_4412_, v___x_4413_, v_a_4411_);
    v___x_4415_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_4415_, 0, v___x_4414_);
    return v___x_4415_;
}
pub unsafe fn l_Lean_Lsp_instToJsonLeanFileProgressParams_toJson(
    mut v_x_4416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_textDocument_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_processing_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4421_: u8 = 0;
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4438_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_textDocument_4417_ = lean_ctor_get(v_x_4416_, 0);
                v_processing_4418_ = lean_ctor_get(v_x_4416_, 1);
                v_isSharedCheck_4438_ = (!lean_is_exclusive(v_x_4416_)) as u8;
                if v_isSharedCheck_4438_ == 0 {
                    v___x_4420_ = v_x_4416_;
                    v_isShared_4421_ = v_isSharedCheck_4438_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_processing_4418_);
                    lean_inc(v_textDocument_4417_);
                    lean_dec(v_x_4416_);
                    v___x_4420_ = lean_box(0);
                    v_isShared_4421_ = v_isSharedCheck_4438_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4422_ =
                    l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0;
                v___x_4423_ = l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson(
                    v_textDocument_4417_,
                );
                if v_isShared_4421_ == 0 {
                    lean_ctor_set(v___x_4420_, 1, v___x_4423_);
                    lean_ctor_set(v___x_4420_, 0, v___x_4422_);
                    v___x_4425_ = v___x_4420_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4437_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4437_, 0, v___x_4422_);
                    lean_ctor_set(v_reuseFailAlloc_4437_, 1, v___x_4423_);
                    v___x_4425_ = v_reuseFailAlloc_4437_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4426_ = lean_box(0);
                v___x_4427_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4427_, 0, v___x_4425_);
                lean_ctor_set(v___x_4427_, 1, v___x_4426_);
                v___x_4428_ = l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__6;
                v___x_4429_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0(v_processing_4418_);
                v___x_4430_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4430_, 0, v___x_4428_);
                lean_ctor_set(v___x_4430_, 1, v___x_4429_);
                v___x_4431_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4431_, 0, v___x_4430_);
                lean_ctor_set(v___x_4431_, 1, v___x_4426_);
                v___x_4432_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4432_, 0, v___x_4431_);
                lean_ctor_set(v___x_4432_, 1, v___x_4426_);
                v___x_4433_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4433_, 0, v___x_4427_);
                lean_ctor_set(v___x_4433_, 1, v___x_4432_);
                v___x_4434_ = l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0;
                v___x_4435_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_4433_, v___x_4434_);
                v___x_4436_ = l_Lean_Json_mkObj(v___x_4435_);
                lean_dec(v___x_4435_);
                return v___x_4436_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(
    mut v_j_4441_: *mut LeanObject,
    mut v_k_4442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    v___x_4443_ = l_Lean_Json_getObjValD(v_j_4441_, v_k_4442_);
    v___x_4444_ = l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson(v___x_4443_);
    return v___x_4444_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0___boxed(
    mut v_j_4445_: *mut LeanObject,
    mut v_k_4446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4447_: *mut LeanObject = core::ptr::null_mut();
    v_res_4447_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(
            v_j_4445_, v_k_4446_,
        );
    lean_dec_ref(v_k_4446_);
    return v_res_4447_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(
    mut v_j_4448_: *mut LeanObject,
    mut v_k_4449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut LeanObject = core::ptr::null_mut();
    v___x_4450_ = l_Lean_Json_getObjValD(v_j_4448_, v_k_4449_);
    v___x_4451_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v___x_4450_);
    return v___x_4451_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1___boxed(
    mut v_j_4452_: *mut LeanObject,
    mut v_k_4453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4454_: *mut LeanObject = core::ptr::null_mut();
    v_res_4454_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(
            v_j_4452_, v_k_4453_,
        );
    lean_dec_ref(v_k_4453_);
    return v_res_4454_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2() -> *mut LeanObject
{
    let mut v___x_4460_: u8 = 0;
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    v___x_4460_ = 1;
    v___x_4461_ = l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__1;
    v___x_4462_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4461_, v___x_4460_);
    return v___x_4462_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3() -> *mut LeanObject
{
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    v___x_4463_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6;
    v___x_4464_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2_once),
        _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2,
    );
    v___x_4465_ = lean_string_append(v___x_4464_, v___x_4463_);
    return v___x_4465_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4() -> *mut LeanObject
{
    let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    v___x_4466_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9,
    );
    v___x_4467_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3,
    );
    v___x_4468_ = lean_string_append(v___x_4467_, v___x_4466_);
    return v___x_4468_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5() -> *mut LeanObject
{
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
    v___x_4469_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_4470_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4,
    );
    v___x_4471_ = lean_string_append(v___x_4470_, v___x_4469_);
    return v___x_4471_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8() -> *mut LeanObject
{
    let mut v___x_4475_: u8 = 0;
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    v___x_4475_ = 1;
    v___x_4476_ = l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__7;
    v___x_4477_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4476_, v___x_4475_);
    return v___x_4477_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9() -> *mut LeanObject
{
    let mut v___x_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
    v___x_4478_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8_once),
        _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8,
    );
    v___x_4479_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3,
    );
    v___x_4480_ = lean_string_append(v___x_4479_, v___x_4478_);
    return v___x_4480_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10() -> *mut LeanObject
{
    let mut v___x_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    v___x_4481_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_4482_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9_once),
        _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9,
    );
    v___x_4483_ = lean_string_append(v___x_4482_, v___x_4481_);
    return v___x_4483_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson(
    mut v_json_4484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4490_: u8 = 0;
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4496_: u8 = 0;
    let mut v_a_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4500_: u8 = 0;
    let mut v___x_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4504_: u8 = 0;
    let mut v_a_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4511_: u8 = 0;
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4517_: u8 = 0;
    let mut v_a_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4521_: u8 = 0;
    let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4525_: u8 = 0;
    let mut v_a_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4529_: u8 = 0;
    let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4534_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4485_ =
                    l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0;
                lean_inc(v_json_4484_);
                v___x_4486_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_json_4484_, v___x_4485_);
                if lean_obj_tag(v___x_4486_) == 0 {
                    lean_dec(v_json_4484_);
                    v_a_4487_ = lean_ctor_get(v___x_4486_, 0);
                    v_isSharedCheck_4496_ = (!lean_is_exclusive(v___x_4486_)) as u8;
                    if v_isSharedCheck_4496_ == 0 {
                        v___x_4489_ = v___x_4486_;
                        v_isShared_4490_ = v_isSharedCheck_4496_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4487_);
                        lean_dec(v___x_4486_);
                        v___x_4489_ = lean_box(0);
                        v_isShared_4490_ = v_isSharedCheck_4496_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_4486_) == 0 {
                        lean_dec(v_json_4484_);
                        v_a_4497_ = lean_ctor_get(v___x_4486_, 0);
                        v_isSharedCheck_4504_ = (!lean_is_exclusive(v___x_4486_)) as u8;
                        if v_isSharedCheck_4504_ == 0 {
                            v___x_4499_ = v___x_4486_;
                            v_isShared_4500_ = v_isSharedCheck_4504_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4497_);
                            lean_dec(v___x_4486_);
                            v___x_4499_ = lean_box(0);
                            v_isShared_4500_ = v_isSharedCheck_4504_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4505_ = lean_ctor_get(v___x_4486_, 0);
                        lean_inc(v_a_4505_);
                        lean_dec_ref_known(v___x_4486_, 1);
                        v___x_4506_ = l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6;
                        v___x_4507_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(v_json_4484_, v___x_4506_);
                        if lean_obj_tag(v___x_4507_) == 0 {
                            lean_dec(v_a_4505_);
                            v_a_4508_ = lean_ctor_get(v___x_4507_, 0);
                            v_isSharedCheck_4517_ = (!lean_is_exclusive(v___x_4507_)) as u8;
                            if v_isSharedCheck_4517_ == 0 {
                                v___x_4510_ = v___x_4507_;
                                v_isShared_4511_ = v_isSharedCheck_4517_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_4508_);
                                lean_dec(v___x_4507_);
                                v___x_4510_ = lean_box(0);
                                v_isShared_4511_ = v_isSharedCheck_4517_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_4507_) == 0 {
                                lean_dec(v_a_4505_);
                                v_a_4518_ = lean_ctor_get(v___x_4507_, 0);
                                v_isSharedCheck_4525_ = (!lean_is_exclusive(v___x_4507_)) as u8;
                                if v_isSharedCheck_4525_ == 0 {
                                    v___x_4520_ = v___x_4507_;
                                    v_isShared_4521_ = v_isSharedCheck_4525_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_4518_);
                                    lean_dec(v___x_4507_);
                                    v___x_4520_ = lean_box(0);
                                    v_isShared_4521_ = v_isSharedCheck_4525_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_4526_ = lean_ctor_get(v___x_4507_, 0);
                                v_isSharedCheck_4534_ = (!lean_is_exclusive(v___x_4507_)) as u8;
                                if v_isSharedCheck_4534_ == 0 {
                                    v___x_4528_ = v___x_4507_;
                                    v_isShared_4529_ = v_isSharedCheck_4534_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_4526_);
                                    lean_dec(v___x_4507_);
                                    v___x_4528_ = lean_box(0);
                                    v_isShared_4529_ = v_isSharedCheck_4534_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4491_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5,
                );
                v___x_4492_ = lean_string_append(v___x_4491_, v_a_4487_);
                lean_dec(v_a_4487_);
                if v_isShared_4490_ == 0 {
                    lean_ctor_set(v___x_4489_, 0, v___x_4492_);
                    v___x_4494_ = v___x_4489_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4495_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4495_, 0, v___x_4492_);
                    v___x_4494_ = v_reuseFailAlloc_4495_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4494_;
            }
            3 => {
                if v_isShared_4500_ == 0 {
                    lean_ctor_set_tag(v___x_4499_, 0);
                    v___x_4502_ = v___x_4499_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4503_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4503_, 0, v_a_4497_);
                    v___x_4502_ = v_reuseFailAlloc_4503_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4502_;
            }
            5 => {
                v___x_4512_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10,
                );
                v___x_4513_ = lean_string_append(v___x_4512_, v_a_4508_);
                lean_dec(v_a_4508_);
                if v_isShared_4511_ == 0 {
                    lean_ctor_set(v___x_4510_, 0, v___x_4513_);
                    v___x_4515_ = v___x_4510_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4516_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4516_, 0, v___x_4513_);
                    v___x_4515_ = v_reuseFailAlloc_4516_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4515_;
            }
            7 => {
                if v_isShared_4521_ == 0 {
                    lean_ctor_set_tag(v___x_4520_, 0);
                    v___x_4523_ = v___x_4520_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4524_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4524_, 0, v_a_4518_);
                    v___x_4523_ = v_reuseFailAlloc_4524_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4523_;
            }
            9 => {
                v___x_4530_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4530_, 0, v_a_4505_);
                lean_ctor_set(v___x_4530_, 1, v_a_4526_);
                if v_isShared_4529_ == 0 {
                    lean_ctor_set(v___x_4528_, 0, v___x_4530_);
                    v___x_4532_ = v___x_4528_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4533_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4533_, 0, v___x_4530_);
                    v___x_4532_ = v_reuseFailAlloc_4533_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4532_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonPlainGoalParams_toJson(
    mut v_x_4537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_textDocument_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_position_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4542_: u8 = 0;
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4559_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_textDocument_4538_ = lean_ctor_get(v_x_4537_, 0);
                v_position_4539_ = lean_ctor_get(v_x_4537_, 1);
                v_isSharedCheck_4559_ = (!lean_is_exclusive(v_x_4537_)) as u8;
                if v_isSharedCheck_4559_ == 0 {
                    v___x_4541_ = v_x_4537_;
                    v_isShared_4542_ = v_isSharedCheck_4559_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_position_4539_);
                    lean_inc(v_textDocument_4538_);
                    lean_dec(v_x_4537_);
                    v___x_4541_ = lean_box(0);
                    v_isShared_4542_ = v_isSharedCheck_4559_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4543_ =
                    l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0;
                v___x_4544_ =
                    l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_4538_);
                if v_isShared_4542_ == 0 {
                    lean_ctor_set(v___x_4541_, 1, v___x_4544_);
                    lean_ctor_set(v___x_4541_, 0, v___x_4543_);
                    v___x_4546_ = v___x_4541_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4558_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4558_, 0, v___x_4543_);
                    lean_ctor_set(v_reuseFailAlloc_4558_, 1, v___x_4544_);
                    v___x_4546_ = v_reuseFailAlloc_4558_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4547_ = lean_box(0);
                v___x_4548_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4548_, 0, v___x_4546_);
                lean_ctor_set(v___x_4548_, 1, v___x_4547_);
                v___x_4549_ = l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6;
                v___x_4550_ = l_Lean_Lsp_instToJsonPosition_toJson(v_position_4539_);
                v___x_4551_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4551_, 0, v___x_4549_);
                lean_ctor_set(v___x_4551_, 1, v___x_4550_);
                v___x_4552_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4552_, 0, v___x_4551_);
                lean_ctor_set(v___x_4552_, 1, v___x_4547_);
                v___x_4553_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4553_, 0, v___x_4552_);
                lean_ctor_set(v___x_4553_, 1, v___x_4547_);
                v___x_4554_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4554_, 0, v___x_4548_);
                lean_ctor_set(v___x_4554_, 1, v___x_4553_);
                v___x_4555_ = l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0;
                v___x_4556_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_4554_, v___x_4555_);
                v___x_4557_ = l_Lean_Json_mkObj(v___x_4556_);
                lean_dec(v___x_4556_);
                return v___x_4557_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1(
    mut v_sz_4562_: usize,
    mut v_i_4563_: usize,
    mut v_bs_4564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4565_: u8 = 0;
    let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4572_: u8 = 0;
    let mut v___x_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4576_: u8 = 0;
    let mut v_a_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: usize = 0;
    let mut v___x_4581_: usize = 0;
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4565_ = lean_usize_dec_lt(v_i_4563_, v_sz_4562_);
                if v___x_4565_ == 0 {
                    v___x_4566_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4566_, 0, v_bs_4564_);
                    return v___x_4566_;
                } else {
                    v_v_4567_ = lean_array_uget_borrowed(v_bs_4564_, v_i_4563_);
                    lean_inc(v_v_4567_);
                    v___x_4568_ = l_Lean_Json_getStr_x3f(v_v_4567_);
                    if lean_obj_tag(v___x_4568_) == 0 {
                        lean_dec_ref(v_bs_4564_);
                        v_a_4569_ = lean_ctor_get(v___x_4568_, 0);
                        v_isSharedCheck_4576_ = (!lean_is_exclusive(v___x_4568_)) as u8;
                        if v_isSharedCheck_4576_ == 0 {
                            v___x_4571_ = v___x_4568_;
                            v_isShared_4572_ = v_isSharedCheck_4576_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4569_);
                            lean_dec(v___x_4568_);
                            v___x_4571_ = lean_box(0);
                            v_isShared_4572_ = v_isSharedCheck_4576_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4577_ = lean_ctor_get(v___x_4568_, 0);
                        lean_inc(v_a_4577_);
                        lean_dec_ref_known(v___x_4568_, 1);
                        v___x_4578_ = lean_unsigned_to_nat(0);
                        v_bs_x27_4579_ = lean_array_uset(v_bs_4564_, v_i_4563_, v___x_4578_);
                        v___x_4580_ = 1usize;
                        v___x_4581_ = lean_usize_add(v_i_4563_, v___x_4580_);
                        v___x_4582_ = lean_array_uset(v_bs_x27_4579_, v_i_4563_, v_a_4577_);
                        v_i_4563_ = v___x_4581_;
                        v_bs_4564_ = v___x_4582_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4572_ == 0 {
                    v___x_4574_ = v___x_4571_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4575_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4575_, 0, v_a_4569_);
                    v___x_4574_ = v_reuseFailAlloc_4575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4574_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1___boxed(
    mut v_sz_4584_: *mut LeanObject,
    mut v_i_4585_: *mut LeanObject,
    mut v_bs_4586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4587_: usize = 0;
    let mut v_i_boxed_4588_: usize = 0;
    let mut v_res_4589_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4587_ = lean_unbox_usize(v_sz_4584_);
    lean_dec(v_sz_4584_);
    v_i_boxed_4588_ = lean_unbox_usize(v_i_4585_);
    lean_dec(v_i_4585_);
    v_res_4589_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_4587_, v_i_boxed_4588_, v_bs_4586_);
    return v_res_4589_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0(
    mut v_x_4590_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4590_) == 4 {
        let mut v_elems_4591_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_4592_: usize = 0;
        let mut v___x_4593_: usize = 0;
        let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
        v_elems_4591_ = lean_ctor_get(v_x_4590_, 0);
        lean_inc_ref(v_elems_4591_);
        lean_dec_ref_known(v_x_4590_, 1);
        v_sz_4592_ = lean_array_size(v_elems_4591_);
        v___x_4593_ = 0usize;
        v___x_4594_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1(v_sz_4592_, v___x_4593_, v_elems_4591_);
        return v___x_4594_;
    } else {
        let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4597_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
        v___x_4595_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0;
        v___x_4596_ = lean_unsigned_to_nat(80);
        v___x_4597_ = l_Lean_Json_pretty(v_x_4590_, v___x_4596_);
        v___x_4598_ = lean_string_append(v___x_4595_, v___x_4597_);
        lean_dec_ref(v___x_4597_);
        v___x_4599_ = l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1;
        v___x_4600_ = lean_string_append(v___x_4598_, v___x_4599_);
        v___x_4601_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4601_, 0, v___x_4600_);
        return v___x_4601_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0(
    mut v_j_4602_: *mut LeanObject,
    mut v_k_4603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
    v___x_4604_ = l_Lean_Json_getObjValD(v_j_4602_, v_k_4603_);
    v___x_4605_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0(v___x_4604_);
    return v___x_4605_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0___boxed(
    mut v_j_4606_: *mut LeanObject,
    mut v_k_4607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4608_: *mut LeanObject = core::ptr::null_mut();
    v_res_4608_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0(
            v_j_4606_, v_k_4607_,
        );
    lean_dec_ref(v_k_4607_);
    return v_res_4608_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3() -> *mut LeanObject {
    let mut v___x_4615_: u8 = 0;
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    v___x_4615_ = 1;
    v___x_4616_ = l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__2;
    v___x_4617_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4616_, v___x_4615_);
    return v___x_4617_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4() -> *mut LeanObject {
    let mut v___x_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut LeanObject = core::ptr::null_mut();
    v___x_4618_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6;
    v___x_4619_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3,
    );
    v___x_4620_ = lean_string_append(v___x_4619_, v___x_4618_);
    return v___x_4620_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6() -> *mut LeanObject {
    let mut v___x_4623_: u8 = 0;
    let mut v___x_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut LeanObject = core::ptr::null_mut();
    v___x_4623_ = 1;
    v___x_4624_ = l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__5;
    v___x_4625_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4624_, v___x_4623_);
    return v___x_4625_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7() -> *mut LeanObject {
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    v___x_4626_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6,
    );
    v___x_4627_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4,
    );
    v___x_4628_ = lean_string_append(v___x_4627_, v___x_4626_);
    return v___x_4628_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8() -> *mut LeanObject {
    let mut v___x_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    v___x_4629_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_4630_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7_once),
        _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7,
    );
    v___x_4631_ = lean_string_append(v___x_4630_, v___x_4629_);
    return v___x_4631_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11() -> *mut LeanObject {
    let mut v___x_4635_: u8 = 0;
    let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    v___x_4635_ = 1;
    v___x_4636_ = l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__10;
    v___x_4637_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4636_, v___x_4635_);
    return v___x_4637_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12() -> *mut LeanObject {
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut LeanObject = core::ptr::null_mut();
    v___x_4638_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11_once),
        _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11,
    );
    v___x_4639_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4,
    );
    v___x_4640_ = lean_string_append(v___x_4639_, v___x_4638_);
    return v___x_4640_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13() -> *mut LeanObject {
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut LeanObject = core::ptr::null_mut();
    v___x_4641_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_4642_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12_once),
        _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12,
    );
    v___x_4643_ = lean_string_append(v___x_4642_, v___x_4641_);
    return v___x_4643_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonPlainGoal_fromJson(
    mut v_json_4644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4650_: u8 = 0;
    let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4656_: u8 = 0;
    let mut v_a_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4660_: u8 = 0;
    let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4664_: u8 = 0;
    let mut v_a_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4671_: u8 = 0;
    let mut v___x_4672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4677_: u8 = 0;
    let mut v_a_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4681_: u8 = 0;
    let mut v___x_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4685_: u8 = 0;
    let mut v_a_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4689_: u8 = 0;
    let mut v___x_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4645_ = l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__0;
                lean_inc(v_json_4644_);
                v___x_4646_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_4644_, v___x_4645_);
                if lean_obj_tag(v___x_4646_) == 0 {
                    lean_dec(v_json_4644_);
                    v_a_4647_ = lean_ctor_get(v___x_4646_, 0);
                    v_isSharedCheck_4656_ = (!lean_is_exclusive(v___x_4646_)) as u8;
                    if v_isSharedCheck_4656_ == 0 {
                        v___x_4649_ = v___x_4646_;
                        v_isShared_4650_ = v_isSharedCheck_4656_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4647_);
                        lean_dec(v___x_4646_);
                        v___x_4649_ = lean_box(0);
                        v_isShared_4650_ = v_isSharedCheck_4656_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_4646_) == 0 {
                        lean_dec(v_json_4644_);
                        v_a_4657_ = lean_ctor_get(v___x_4646_, 0);
                        v_isSharedCheck_4664_ = (!lean_is_exclusive(v___x_4646_)) as u8;
                        if v_isSharedCheck_4664_ == 0 {
                            v___x_4659_ = v___x_4646_;
                            v_isShared_4660_ = v_isSharedCheck_4664_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4657_);
                            lean_dec(v___x_4646_);
                            v___x_4659_ = lean_box(0);
                            v_isShared_4660_ = v_isSharedCheck_4664_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4665_ = lean_ctor_get(v___x_4646_, 0);
                        lean_inc(v_a_4665_);
                        lean_dec_ref_known(v___x_4646_, 1);
                        v___x_4666_ = l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__9;
                        v___x_4667_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0(v_json_4644_, v___x_4666_);
                        if lean_obj_tag(v___x_4667_) == 0 {
                            lean_dec(v_a_4665_);
                            v_a_4668_ = lean_ctor_get(v___x_4667_, 0);
                            v_isSharedCheck_4677_ = (!lean_is_exclusive(v___x_4667_)) as u8;
                            if v_isSharedCheck_4677_ == 0 {
                                v___x_4670_ = v___x_4667_;
                                v_isShared_4671_ = v_isSharedCheck_4677_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_4668_);
                                lean_dec(v___x_4667_);
                                v___x_4670_ = lean_box(0);
                                v_isShared_4671_ = v_isSharedCheck_4677_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_4667_) == 0 {
                                lean_dec(v_a_4665_);
                                v_a_4678_ = lean_ctor_get(v___x_4667_, 0);
                                v_isSharedCheck_4685_ = (!lean_is_exclusive(v___x_4667_)) as u8;
                                if v_isSharedCheck_4685_ == 0 {
                                    v___x_4680_ = v___x_4667_;
                                    v_isShared_4681_ = v_isSharedCheck_4685_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_4678_);
                                    lean_dec(v___x_4667_);
                                    v___x_4680_ = lean_box(0);
                                    v_isShared_4681_ = v_isSharedCheck_4685_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_4686_ = lean_ctor_get(v___x_4667_, 0);
                                v_isSharedCheck_4694_ = (!lean_is_exclusive(v___x_4667_)) as u8;
                                if v_isSharedCheck_4694_ == 0 {
                                    v___x_4688_ = v___x_4667_;
                                    v_isShared_4689_ = v_isSharedCheck_4694_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_4686_);
                                    lean_dec(v___x_4667_);
                                    v___x_4688_ = lean_box(0);
                                    v_isShared_4689_ = v_isSharedCheck_4694_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4651_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8,
                );
                v___x_4652_ = lean_string_append(v___x_4651_, v_a_4647_);
                lean_dec(v_a_4647_);
                if v_isShared_4650_ == 0 {
                    lean_ctor_set(v___x_4649_, 0, v___x_4652_);
                    v___x_4654_ = v___x_4649_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4655_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4655_, 0, v___x_4652_);
                    v___x_4654_ = v_reuseFailAlloc_4655_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4654_;
            }
            3 => {
                if v_isShared_4660_ == 0 {
                    lean_ctor_set_tag(v___x_4659_, 0);
                    v___x_4662_ = v___x_4659_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4663_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4663_, 0, v_a_4657_);
                    v___x_4662_ = v_reuseFailAlloc_4663_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4662_;
            }
            5 => {
                v___x_4672_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13,
                );
                v___x_4673_ = lean_string_append(v___x_4672_, v_a_4668_);
                lean_dec(v_a_4668_);
                if v_isShared_4671_ == 0 {
                    lean_ctor_set(v___x_4670_, 0, v___x_4673_);
                    v___x_4675_ = v___x_4670_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4676_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4676_, 0, v___x_4673_);
                    v___x_4675_ = v_reuseFailAlloc_4676_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4675_;
            }
            7 => {
                if v_isShared_4681_ == 0 {
                    lean_ctor_set_tag(v___x_4680_, 0);
                    v___x_4683_ = v___x_4680_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4684_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_a_4678_);
                    v___x_4683_ = v_reuseFailAlloc_4684_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4683_;
            }
            9 => {
                v___x_4690_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4690_, 0, v_a_4665_);
                lean_ctor_set(v___x_4690_, 1, v_a_4686_);
                if v_isShared_4689_ == 0 {
                    lean_ctor_set(v___x_4688_, 0, v___x_4690_);
                    v___x_4692_ = v___x_4688_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4693_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4693_, 0, v___x_4690_);
                    v___x_4692_ = v_reuseFailAlloc_4693_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4692_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0(
    mut v_sz_4697_: usize,
    mut v_i_4698_: usize,
    mut v_bs_4699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4700_: u8 = 0;
    let mut v_v_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: usize = 0;
    let mut v___x_4706_: usize = 0;
    let mut v___x_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4700_ = lean_usize_dec_lt(v_i_4698_, v_sz_4697_);
                if v___x_4700_ == 0 {
                    return v_bs_4699_;
                } else {
                    v_v_4701_ = lean_array_uget(v_bs_4699_, v_i_4698_);
                    v___x_4702_ = lean_unsigned_to_nat(0);
                    v_bs_x27_4703_ = lean_array_uset(v_bs_4699_, v_i_4698_, v___x_4702_);
                    v___x_4704_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_4704_, 0, v_v_4701_);
                    v___x_4705_ = 1usize;
                    v___x_4706_ = lean_usize_add(v_i_4698_, v___x_4705_);
                    v___x_4707_ = lean_array_uset(v_bs_x27_4703_, v_i_4698_, v___x_4704_);
                    v_i_4698_ = v___x_4706_;
                    v_bs_4699_ = v___x_4707_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0___boxed(
    mut v_sz_4709_: *mut LeanObject,
    mut v_i_4710_: *mut LeanObject,
    mut v_bs_4711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4712_: usize = 0;
    let mut v_i_boxed_4713_: usize = 0;
    let mut v_res_4714_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4712_ = lean_unbox_usize(v_sz_4709_);
    lean_dec(v_sz_4709_);
    v_i_boxed_4713_ = lean_unbox_usize(v_i_4710_);
    lean_dec(v_i_4710_);
    v_res_4714_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0(v_sz_boxed_4712_, v_i_boxed_4713_, v_bs_4711_);
    return v_res_4714_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0(
    mut v_a_4715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_4716_: usize = 0;
    let mut v___x_4717_: usize = 0;
    let mut v___x_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut LeanObject = core::ptr::null_mut();
    v_sz_4716_ = lean_array_size(v_a_4715_);
    v___x_4717_ = 0usize;
    v___x_4718_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0(v_sz_4716_, v___x_4717_, v_a_4715_);
    v___x_4719_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_4719_, 0, v___x_4718_);
    return v___x_4719_;
}
pub unsafe fn l_Lean_Lsp_instToJsonPlainGoal_toJson(
    mut v_x_4720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_rendered_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_goals_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4725_: u8 = 0;
    let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4742_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rendered_4721_ = lean_ctor_get(v_x_4720_, 0);
                v_goals_4722_ = lean_ctor_get(v_x_4720_, 1);
                v_isSharedCheck_4742_ = (!lean_is_exclusive(v_x_4720_)) as u8;
                if v_isSharedCheck_4742_ == 0 {
                    v___x_4724_ = v_x_4720_;
                    v_isShared_4725_ = v_isSharedCheck_4742_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_goals_4722_);
                    lean_inc(v_rendered_4721_);
                    lean_dec(v_x_4720_);
                    v___x_4724_ = lean_box(0);
                    v_isShared_4725_ = v_isSharedCheck_4742_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4726_ = l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__0;
                v___x_4727_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_4727_, 0, v_rendered_4721_);
                if v_isShared_4725_ == 0 {
                    lean_ctor_set(v___x_4724_, 1, v___x_4727_);
                    lean_ctor_set(v___x_4724_, 0, v___x_4726_);
                    v___x_4729_ = v___x_4724_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4741_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4741_, 0, v___x_4726_);
                    lean_ctor_set(v_reuseFailAlloc_4741_, 1, v___x_4727_);
                    v___x_4729_ = v_reuseFailAlloc_4741_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4730_ = lean_box(0);
                v___x_4731_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4731_, 0, v___x_4729_);
                lean_ctor_set(v___x_4731_, 1, v___x_4730_);
                v___x_4732_ = l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__9;
                v___x_4733_ = l_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0(
                    v_goals_4722_,
                );
                v___x_4734_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4734_, 0, v___x_4732_);
                lean_ctor_set(v___x_4734_, 1, v___x_4733_);
                v___x_4735_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4735_, 0, v___x_4734_);
                lean_ctor_set(v___x_4735_, 1, v___x_4730_);
                v___x_4736_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4736_, 0, v___x_4735_);
                lean_ctor_set(v___x_4736_, 1, v___x_4730_);
                v___x_4737_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4737_, 0, v___x_4731_);
                lean_ctor_set(v___x_4737_, 1, v___x_4736_);
                v___x_4738_ = l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0;
                v___x_4739_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_4737_, v___x_4738_);
                v___x_4740_ = l_Lean_Json_mkObj(v___x_4739_);
                lean_dec(v___x_4739_);
                return v___x_4740_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2()
-> *mut LeanObject {
    let mut v___x_4750_: u8 = 0;
    let mut v___x_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
    v___x_4750_ = 1;
    v___x_4751_ = l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__1;
    v___x_4752_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4751_, v___x_4750_);
    return v___x_4752_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3()
-> *mut LeanObject {
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut LeanObject = core::ptr::null_mut();
    v___x_4753_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6;
    v___x_4754_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2,
    );
    v___x_4755_ = lean_string_append(v___x_4754_, v___x_4753_);
    return v___x_4755_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4()
-> *mut LeanObject {
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut LeanObject = core::ptr::null_mut();
    v___x_4756_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9,
    );
    v___x_4757_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3,
    );
    v___x_4758_ = lean_string_append(v___x_4757_, v___x_4756_);
    return v___x_4758_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5()
-> *mut LeanObject {
    let mut v___x_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    v___x_4759_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_4760_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4,
    );
    v___x_4761_ = lean_string_append(v___x_4760_, v___x_4759_);
    return v___x_4761_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6()
-> *mut LeanObject {
    let mut v___x_4762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
    v___x_4762_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8_once),
        _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8,
    );
    v___x_4763_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3,
    );
    v___x_4764_ = lean_string_append(v___x_4763_, v___x_4762_);
    return v___x_4764_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7()
-> *mut LeanObject {
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
    v___x_4765_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_4766_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6,
    );
    v___x_4767_ = lean_string_append(v___x_4766_, v___x_4765_);
    return v___x_4767_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson(
    mut v_json_4768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4774_: u8 = 0;
    let mut v___x_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4780_: u8 = 0;
    let mut v_a_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4784_: u8 = 0;
    let mut v___x_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4788_: u8 = 0;
    let mut v_a_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4795_: u8 = 0;
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4801_: u8 = 0;
    let mut v_a_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4805_: u8 = 0;
    let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4809_: u8 = 0;
    let mut v_a_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4813_: u8 = 0;
    let mut v___x_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4818_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4769_ =
                    l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0;
                lean_inc(v_json_4768_);
                v___x_4770_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_json_4768_, v___x_4769_);
                if lean_obj_tag(v___x_4770_) == 0 {
                    lean_dec(v_json_4768_);
                    v_a_4771_ = lean_ctor_get(v___x_4770_, 0);
                    v_isSharedCheck_4780_ = (!lean_is_exclusive(v___x_4770_)) as u8;
                    if v_isSharedCheck_4780_ == 0 {
                        v___x_4773_ = v___x_4770_;
                        v_isShared_4774_ = v_isSharedCheck_4780_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4771_);
                        lean_dec(v___x_4770_);
                        v___x_4773_ = lean_box(0);
                        v_isShared_4774_ = v_isSharedCheck_4780_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_4770_) == 0 {
                        lean_dec(v_json_4768_);
                        v_a_4781_ = lean_ctor_get(v___x_4770_, 0);
                        v_isSharedCheck_4788_ = (!lean_is_exclusive(v___x_4770_)) as u8;
                        if v_isSharedCheck_4788_ == 0 {
                            v___x_4783_ = v___x_4770_;
                            v_isShared_4784_ = v_isSharedCheck_4788_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4781_);
                            lean_dec(v___x_4770_);
                            v___x_4783_ = lean_box(0);
                            v_isShared_4784_ = v_isSharedCheck_4788_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4789_ = lean_ctor_get(v___x_4770_, 0);
                        lean_inc(v_a_4789_);
                        lean_dec_ref_known(v___x_4770_, 1);
                        v___x_4790_ = l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6;
                        v___x_4791_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(v_json_4768_, v___x_4790_);
                        if lean_obj_tag(v___x_4791_) == 0 {
                            lean_dec(v_a_4789_);
                            v_a_4792_ = lean_ctor_get(v___x_4791_, 0);
                            v_isSharedCheck_4801_ = (!lean_is_exclusive(v___x_4791_)) as u8;
                            if v_isSharedCheck_4801_ == 0 {
                                v___x_4794_ = v___x_4791_;
                                v_isShared_4795_ = v_isSharedCheck_4801_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_4792_);
                                lean_dec(v___x_4791_);
                                v___x_4794_ = lean_box(0);
                                v_isShared_4795_ = v_isSharedCheck_4801_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_4791_) == 0 {
                                lean_dec(v_a_4789_);
                                v_a_4802_ = lean_ctor_get(v___x_4791_, 0);
                                v_isSharedCheck_4809_ = (!lean_is_exclusive(v___x_4791_)) as u8;
                                if v_isSharedCheck_4809_ == 0 {
                                    v___x_4804_ = v___x_4791_;
                                    v_isShared_4805_ = v_isSharedCheck_4809_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_4802_);
                                    lean_dec(v___x_4791_);
                                    v___x_4804_ = lean_box(0);
                                    v_isShared_4805_ = v_isSharedCheck_4809_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_4810_ = lean_ctor_get(v___x_4791_, 0);
                                v_isSharedCheck_4818_ = (!lean_is_exclusive(v___x_4791_)) as u8;
                                if v_isSharedCheck_4818_ == 0 {
                                    v___x_4812_ = v___x_4791_;
                                    v_isShared_4813_ = v_isSharedCheck_4818_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_4810_);
                                    lean_dec(v___x_4791_);
                                    v___x_4812_ = lean_box(0);
                                    v_isShared_4813_ = v_isSharedCheck_4818_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4775_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5,
                );
                v___x_4776_ = lean_string_append(v___x_4775_, v_a_4771_);
                lean_dec(v_a_4771_);
                if v_isShared_4774_ == 0 {
                    lean_ctor_set(v___x_4773_, 0, v___x_4776_);
                    v___x_4778_ = v___x_4773_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4779_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4779_, 0, v___x_4776_);
                    v___x_4778_ = v_reuseFailAlloc_4779_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4778_;
            }
            3 => {
                if v_isShared_4784_ == 0 {
                    lean_ctor_set_tag(v___x_4783_, 0);
                    v___x_4786_ = v___x_4783_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4787_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4787_, 0, v_a_4781_);
                    v___x_4786_ = v_reuseFailAlloc_4787_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4786_;
            }
            5 => {
                v___x_4796_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7,
                );
                v___x_4797_ = lean_string_append(v___x_4796_, v_a_4792_);
                lean_dec(v_a_4792_);
                if v_isShared_4795_ == 0 {
                    lean_ctor_set(v___x_4794_, 0, v___x_4797_);
                    v___x_4799_ = v___x_4794_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4800_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4800_, 0, v___x_4797_);
                    v___x_4799_ = v_reuseFailAlloc_4800_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4799_;
            }
            7 => {
                if v_isShared_4805_ == 0 {
                    lean_ctor_set_tag(v___x_4804_, 0);
                    v___x_4807_ = v___x_4804_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4808_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4808_, 0, v_a_4802_);
                    v___x_4807_ = v_reuseFailAlloc_4808_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4807_;
            }
            9 => {
                v___x_4814_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4814_, 0, v_a_4789_);
                lean_ctor_set(v___x_4814_, 1, v_a_4810_);
                if v_isShared_4813_ == 0 {
                    lean_ctor_set(v___x_4812_, 0, v___x_4814_);
                    v___x_4816_ = v___x_4812_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4817_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4817_, 0, v___x_4814_);
                    v___x_4816_ = v_reuseFailAlloc_4817_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4816_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonPlainTermGoalParams_toJson(
    mut v_x_4821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_textDocument_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_position_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4826_: u8 = 0;
    let mut v___x_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4843_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_textDocument_4822_ = lean_ctor_get(v_x_4821_, 0);
                v_position_4823_ = lean_ctor_get(v_x_4821_, 1);
                v_isSharedCheck_4843_ = (!lean_is_exclusive(v_x_4821_)) as u8;
                if v_isSharedCheck_4843_ == 0 {
                    v___x_4825_ = v_x_4821_;
                    v_isShared_4826_ = v_isSharedCheck_4843_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_position_4823_);
                    lean_inc(v_textDocument_4822_);
                    lean_dec(v_x_4821_);
                    v___x_4825_ = lean_box(0);
                    v_isShared_4826_ = v_isSharedCheck_4843_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4827_ =
                    l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0;
                v___x_4828_ =
                    l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_4822_);
                if v_isShared_4826_ == 0 {
                    lean_ctor_set(v___x_4825_, 1, v___x_4828_);
                    lean_ctor_set(v___x_4825_, 0, v___x_4827_);
                    v___x_4830_ = v___x_4825_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4842_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4842_, 0, v___x_4827_);
                    lean_ctor_set(v_reuseFailAlloc_4842_, 1, v___x_4828_);
                    v___x_4830_ = v_reuseFailAlloc_4842_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4831_ = lean_box(0);
                v___x_4832_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4832_, 0, v___x_4830_);
                lean_ctor_set(v___x_4832_, 1, v___x_4831_);
                v___x_4833_ = l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6;
                v___x_4834_ = l_Lean_Lsp_instToJsonPosition_toJson(v_position_4823_);
                v___x_4835_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4835_, 0, v___x_4833_);
                lean_ctor_set(v___x_4835_, 1, v___x_4834_);
                v___x_4836_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4836_, 0, v___x_4835_);
                lean_ctor_set(v___x_4836_, 1, v___x_4831_);
                v___x_4837_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4837_, 0, v___x_4836_);
                lean_ctor_set(v___x_4837_, 1, v___x_4831_);
                v___x_4838_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4838_, 0, v___x_4832_);
                lean_ctor_set(v___x_4838_, 1, v___x_4837_);
                v___x_4839_ = l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0;
                v___x_4840_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_4838_, v___x_4839_);
                v___x_4841_ = l_Lean_Json_mkObj(v___x_4840_);
                lean_dec(v___x_4840_);
                return v___x_4841_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3() -> *mut LeanObject {
    let mut v___x_4852_: u8 = 0;
    let mut v___x_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    v___x_4852_ = 1;
    v___x_4853_ = l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__2;
    v___x_4854_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4853_, v___x_4852_);
    return v___x_4854_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4() -> *mut LeanObject {
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    v___x_4855_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6;
    v___x_4856_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3,
    );
    v___x_4857_ = lean_string_append(v___x_4856_, v___x_4855_);
    return v___x_4857_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6() -> *mut LeanObject {
    let mut v___x_4860_: u8 = 0;
    let mut v___x_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    v___x_4860_ = 1;
    v___x_4861_ = l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__5;
    v___x_4862_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4861_, v___x_4860_);
    return v___x_4862_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7() -> *mut LeanObject {
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    v___x_4863_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6,
    );
    v___x_4864_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4,
    );
    v___x_4865_ = lean_string_append(v___x_4864_, v___x_4863_);
    return v___x_4865_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8() -> *mut LeanObject {
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    v___x_4866_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_4867_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7_once),
        _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7,
    );
    v___x_4868_ = lean_string_append(v___x_4867_, v___x_4866_);
    return v___x_4868_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9() -> *mut LeanObject {
    let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    v___x_4869_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6,
    );
    v___x_4870_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4,
    );
    v___x_4871_ = lean_string_append(v___x_4870_, v___x_4869_);
    return v___x_4871_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10() -> *mut LeanObject
{
    let mut v___x_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    v___x_4872_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_4873_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9_once),
        _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9,
    );
    v___x_4874_ = lean_string_append(v___x_4873_, v___x_4872_);
    return v___x_4874_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson(
    mut v_json_4875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4881_: u8 = 0;
    let mut v___x_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4887_: u8 = 0;
    let mut v_a_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4891_: u8 = 0;
    let mut v___x_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4895_: u8 = 0;
    let mut v_a_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4902_: u8 = 0;
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4908_: u8 = 0;
    let mut v_a_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4912_: u8 = 0;
    let mut v___x_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4916_: u8 = 0;
    let mut v_a_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4920_: u8 = 0;
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4925_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4876_ = l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__0;
                lean_inc(v_json_4875_);
                v___x_4877_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_4875_, v___x_4876_);
                if lean_obj_tag(v___x_4877_) == 0 {
                    lean_dec(v_json_4875_);
                    v_a_4878_ = lean_ctor_get(v___x_4877_, 0);
                    v_isSharedCheck_4887_ = (!lean_is_exclusive(v___x_4877_)) as u8;
                    if v_isSharedCheck_4887_ == 0 {
                        v___x_4880_ = v___x_4877_;
                        v_isShared_4881_ = v_isSharedCheck_4887_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4878_);
                        lean_dec(v___x_4877_);
                        v___x_4880_ = lean_box(0);
                        v_isShared_4881_ = v_isSharedCheck_4887_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_4877_) == 0 {
                        lean_dec(v_json_4875_);
                        v_a_4888_ = lean_ctor_get(v___x_4877_, 0);
                        v_isSharedCheck_4895_ = (!lean_is_exclusive(v___x_4877_)) as u8;
                        if v_isSharedCheck_4895_ == 0 {
                            v___x_4890_ = v___x_4877_;
                            v_isShared_4891_ = v_isSharedCheck_4895_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4888_);
                            lean_dec(v___x_4877_);
                            v___x_4890_ = lean_box(0);
                            v_isShared_4891_ = v_isSharedCheck_4895_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4896_ = lean_ctor_get(v___x_4877_, 0);
                        lean_inc(v_a_4896_);
                        lean_dec_ref_known(v___x_4877_, 1);
                        v___x_4897_ = l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0;
                        v___x_4898_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(v_json_4875_, v___x_4897_);
                        if lean_obj_tag(v___x_4898_) == 0 {
                            lean_dec(v_a_4896_);
                            v_a_4899_ = lean_ctor_get(v___x_4898_, 0);
                            v_isSharedCheck_4908_ = (!lean_is_exclusive(v___x_4898_)) as u8;
                            if v_isSharedCheck_4908_ == 0 {
                                v___x_4901_ = v___x_4898_;
                                v_isShared_4902_ = v_isSharedCheck_4908_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_4899_);
                                lean_dec(v___x_4898_);
                                v___x_4901_ = lean_box(0);
                                v_isShared_4902_ = v_isSharedCheck_4908_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_4898_) == 0 {
                                lean_dec(v_a_4896_);
                                v_a_4909_ = lean_ctor_get(v___x_4898_, 0);
                                v_isSharedCheck_4916_ = (!lean_is_exclusive(v___x_4898_)) as u8;
                                if v_isSharedCheck_4916_ == 0 {
                                    v___x_4911_ = v___x_4898_;
                                    v_isShared_4912_ = v_isSharedCheck_4916_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_4909_);
                                    lean_dec(v___x_4898_);
                                    v___x_4911_ = lean_box(0);
                                    v_isShared_4912_ = v_isSharedCheck_4916_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_4917_ = lean_ctor_get(v___x_4898_, 0);
                                v_isSharedCheck_4925_ = (!lean_is_exclusive(v___x_4898_)) as u8;
                                if v_isSharedCheck_4925_ == 0 {
                                    v___x_4919_ = v___x_4898_;
                                    v_isShared_4920_ = v_isSharedCheck_4925_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_4917_);
                                    lean_dec(v___x_4898_);
                                    v___x_4919_ = lean_box(0);
                                    v_isShared_4920_ = v_isSharedCheck_4925_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4882_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8,
                );
                v___x_4883_ = lean_string_append(v___x_4882_, v_a_4878_);
                lean_dec(v_a_4878_);
                if v_isShared_4881_ == 0 {
                    lean_ctor_set(v___x_4880_, 0, v___x_4883_);
                    v___x_4885_ = v___x_4880_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4886_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4886_, 0, v___x_4883_);
                    v___x_4885_ = v_reuseFailAlloc_4886_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4885_;
            }
            3 => {
                if v_isShared_4891_ == 0 {
                    lean_ctor_set_tag(v___x_4890_, 0);
                    v___x_4893_ = v___x_4890_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4894_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4894_, 0, v_a_4888_);
                    v___x_4893_ = v_reuseFailAlloc_4894_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4893_;
            }
            5 => {
                v___x_4903_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10,
                );
                v___x_4904_ = lean_string_append(v___x_4903_, v_a_4899_);
                lean_dec(v_a_4899_);
                if v_isShared_4902_ == 0 {
                    lean_ctor_set(v___x_4901_, 0, v___x_4904_);
                    v___x_4906_ = v___x_4901_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4907_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4907_, 0, v___x_4904_);
                    v___x_4906_ = v_reuseFailAlloc_4907_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4906_;
            }
            7 => {
                if v_isShared_4912_ == 0 {
                    lean_ctor_set_tag(v___x_4911_, 0);
                    v___x_4914_ = v___x_4911_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4915_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4915_, 0, v_a_4909_);
                    v___x_4914_ = v_reuseFailAlloc_4915_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4914_;
            }
            9 => {
                v___x_4921_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4921_, 0, v_a_4896_);
                lean_ctor_set(v___x_4921_, 1, v_a_4917_);
                if v_isShared_4920_ == 0 {
                    lean_ctor_set(v___x_4919_, 0, v___x_4921_);
                    v___x_4923_ = v___x_4919_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4924_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4924_, 0, v___x_4921_);
                    v___x_4923_ = v_reuseFailAlloc_4924_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4923_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonPlainTermGoal_toJson(
    mut v_x_4928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_goal_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4933_: u8 = 0;
    let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4950_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_goal_4929_ = lean_ctor_get(v_x_4928_, 0);
                v_range_4930_ = lean_ctor_get(v_x_4928_, 1);
                v_isSharedCheck_4950_ = (!lean_is_exclusive(v_x_4928_)) as u8;
                if v_isSharedCheck_4950_ == 0 {
                    v___x_4932_ = v_x_4928_;
                    v_isShared_4933_ = v_isSharedCheck_4950_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_range_4930_);
                    lean_inc(v_goal_4929_);
                    lean_dec(v_x_4928_);
                    v___x_4932_ = lean_box(0);
                    v_isShared_4933_ = v_isSharedCheck_4950_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4934_ = l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__0;
                v___x_4935_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_4935_, 0, v_goal_4929_);
                if v_isShared_4933_ == 0 {
                    lean_ctor_set(v___x_4932_, 1, v___x_4935_);
                    lean_ctor_set(v___x_4932_, 0, v___x_4934_);
                    v___x_4937_ = v___x_4932_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4949_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4949_, 0, v___x_4934_);
                    lean_ctor_set(v_reuseFailAlloc_4949_, 1, v___x_4935_);
                    v___x_4937_ = v_reuseFailAlloc_4949_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4938_ = lean_box(0);
                v___x_4939_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4939_, 0, v___x_4937_);
                lean_ctor_set(v___x_4939_, 1, v___x_4938_);
                v___x_4940_ =
                    l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0;
                v___x_4941_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_4930_);
                v___x_4942_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4942_, 0, v___x_4940_);
                lean_ctor_set(v___x_4942_, 1, v___x_4941_);
                v___x_4943_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4943_, 0, v___x_4942_);
                lean_ctor_set(v___x_4943_, 1, v___x_4938_);
                v___x_4944_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4944_, 0, v___x_4943_);
                lean_ctor_set(v___x_4944_, 1, v___x_4938_);
                v___x_4945_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4945_, 0, v___x_4939_);
                lean_ctor_set(v___x_4945_, 1, v___x_4944_);
                v___x_4946_ = l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0;
                v___x_4947_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_4945_, v___x_4946_);
                v___x_4948_ = l_Lean_Json_mkObj(v___x_4947_);
                lean_dec(v___x_4947_);
                return v___x_4948_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_ModuleHierarchyOptions_toCtorIdx(
    mut v_x_4953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    v___x_4954_ = lean_unsigned_to_nat(0);
    return v___x_4954_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson(
    mut v_json_4957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    v___x_4958_ = l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___closed__0;
    return v___x_4958_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___boxed(
    mut v_json_4959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4960_: *mut LeanObject = core::ptr::null_mut();
    v_res_4960_ = l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson(v_json_4959_);
    lean_dec(v_json_4959_);
    return v_res_4960_;
}
pub unsafe fn l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson(
    mut v_x_4963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
    v___x_4964_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1_once),
        _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1,
    );
    return v___x_4964_;
}
pub unsafe fn l_Lean_Lsp_HighlightMatchesOptions_toCtorIdx(
    mut v_x_4967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4968_: *mut LeanObject = core::ptr::null_mut();
    v___x_4968_ = lean_unsigned_to_nat(0);
    return v___x_4968_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson(
    mut v_json_4971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
    v___x_4972_ = l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0;
    return v___x_4972_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___boxed(
    mut v_json_4973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4974_: *mut LeanObject = core::ptr::null_mut();
    v_res_4974_ = l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson(v_json_4973_);
    lean_dec(v_json_4973_);
    return v_res_4974_;
}
pub unsafe fn l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson(
    mut v_x_4977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4978_: *mut LeanObject = core::ptr::null_mut();
    v___x_4978_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1_once),
        _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1,
    );
    return v___x_4978_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2(
    mut v_x_4983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4989_: u8 = 0;
    let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4993_: u8 = 0;
    let mut v_a_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4997_: u8 = 0;
    let mut v___x_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5002_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4983_) == 0 {
                    v___x_4984_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2___closed__0;
                    return v___x_4984_;
                } else {
                    v___x_4985_ = l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson(v_x_4983_);
                    if lean_obj_tag(v___x_4985_) == 0 {
                        v_a_4986_ = lean_ctor_get(v___x_4985_, 0);
                        v_isSharedCheck_4993_ = (!lean_is_exclusive(v___x_4985_)) as u8;
                        if v_isSharedCheck_4993_ == 0 {
                            v___x_4988_ = v___x_4985_;
                            v_isShared_4989_ = v_isSharedCheck_4993_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4986_);
                            lean_dec(v___x_4985_);
                            v___x_4988_ = lean_box(0);
                            v_isShared_4989_ = v_isSharedCheck_4993_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4994_ = lean_ctor_get(v___x_4985_, 0);
                        v_isSharedCheck_5002_ = (!lean_is_exclusive(v___x_4985_)) as u8;
                        if v_isSharedCheck_5002_ == 0 {
                            v___x_4996_ = v___x_4985_;
                            v_isShared_4997_ = v_isSharedCheck_5002_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4994_);
                            lean_dec(v___x_4985_);
                            v___x_4996_ = lean_box(0);
                            v_isShared_4997_ = v_isSharedCheck_5002_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4989_ == 0 {
                    v___x_4991_ = v___x_4988_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4992_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4992_, 0, v_a_4986_);
                    v___x_4991_ = v_reuseFailAlloc_4992_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4991_;
            }
            3 => {
                v___x_4998_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4998_, 0, v_a_4994_);
                if v_isShared_4997_ == 0 {
                    lean_ctor_set(v___x_4996_, 0, v___x_4998_);
                    v___x_5000_ = v___x_4996_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5001_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5001_, 0, v___x_4998_);
                    v___x_5000_ = v_reuseFailAlloc_5001_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5000_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1(
    mut v_j_5003_: *mut LeanObject,
    mut v_k_5004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    v___x_5005_ = l_Lean_Json_getObjValD(v_j_5003_, v_k_5004_);
    v___x_5006_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2(v___x_5005_);
    return v___x_5006_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1___boxed(
    mut v_j_5007_: *mut LeanObject,
    mut v_k_5008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5009_: *mut LeanObject = core::ptr::null_mut();
    v_res_5009_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1(
            v_j_5007_, v_k_5008_,
        );
    lean_dec_ref(v_k_5008_);
    return v_res_5009_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0(
    mut v_x_5012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5018_: u8 = 0;
    let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5023_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5012_) == 0 {
                    v___x_5013_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0___closed__0;
                    return v___x_5013_;
                } else {
                    v___x_5014_ =
                        l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson(v_x_5012_);
                    v_a_5015_ = lean_ctor_get(v___x_5014_, 0);
                    v_isSharedCheck_5023_ = (!lean_is_exclusive(v___x_5014_)) as u8;
                    if v_isSharedCheck_5023_ == 0 {
                        v___x_5017_ = v___x_5014_;
                        v_isShared_5018_ = v_isSharedCheck_5023_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5015_);
                        lean_dec(v___x_5014_);
                        v___x_5017_ = lean_box(0);
                        v_isShared_5018_ = v_isSharedCheck_5023_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5019_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5019_, 0, v_a_5015_);
                if v_isShared_5018_ == 0 {
                    lean_ctor_set(v___x_5017_, 0, v___x_5019_);
                    v___x_5021_ = v___x_5017_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5022_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5022_, 0, v___x_5019_);
                    v___x_5021_ = v_reuseFailAlloc_5022_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5021_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0___boxed(
    mut v_x_5024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5025_: *mut LeanObject = core::ptr::null_mut();
    v_res_5025_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0(v_x_5024_);
    lean_dec(v_x_5024_);
    return v_res_5025_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0(
    mut v_j_5026_: *mut LeanObject,
    mut v_k_5027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
    v___x_5028_ = l_Lean_Json_getObjValD(v_j_5026_, v_k_5027_);
    v___x_5029_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0(v___x_5028_);
    lean_dec(v___x_5028_);
    return v___x_5029_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0___boxed(
    mut v_j_5030_: *mut LeanObject,
    mut v_k_5031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5032_: *mut LeanObject = core::ptr::null_mut();
    v_res_5032_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0(
            v_j_5030_, v_k_5031_,
        );
    lean_dec_ref(v_k_5031_);
    return v_res_5032_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3() -> *mut LeanObject {
    let mut v___x_5039_: u8 = 0;
    let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut LeanObject = core::ptr::null_mut();
    v___x_5039_ = 1;
    v___x_5040_ = l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__2;
    v___x_5041_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5040_, v___x_5039_);
    return v___x_5041_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4() -> *mut LeanObject {
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut LeanObject = core::ptr::null_mut();
    v___x_5042_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6;
    v___x_5043_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3,
    );
    v___x_5044_ = lean_string_append(v___x_5043_, v___x_5042_);
    return v___x_5044_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7() -> *mut LeanObject {
    let mut v___x_5048_: u8 = 0;
    let mut v___x_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut LeanObject = core::ptr::null_mut();
    v___x_5048_ = 1;
    v___x_5049_ = l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__6;
    v___x_5050_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5049_, v___x_5048_);
    return v___x_5050_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8() -> *mut LeanObject {
    let mut v___x_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut LeanObject = core::ptr::null_mut();
    v___x_5051_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7_once),
        _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7,
    );
    v___x_5052_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4,
    );
    v___x_5053_ = lean_string_append(v___x_5052_, v___x_5051_);
    return v___x_5053_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9() -> *mut LeanObject {
    let mut v___x_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut LeanObject = core::ptr::null_mut();
    v___x_5054_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_5055_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8_once),
        _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8,
    );
    v___x_5056_ = lean_string_append(v___x_5055_, v___x_5054_);
    return v___x_5056_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13() -> *mut LeanObject {
    let mut v___x_5061_: u8 = 0;
    let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut LeanObject = core::ptr::null_mut();
    v___x_5061_ = 1;
    v___x_5062_ = l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__12;
    v___x_5063_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5062_, v___x_5061_);
    return v___x_5063_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14() -> *mut LeanObject {
    let mut v___x_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut LeanObject = core::ptr::null_mut();
    v___x_5064_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13_once),
        _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13,
    );
    v___x_5065_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4,
    );
    v___x_5066_ = lean_string_append(v___x_5065_, v___x_5064_);
    return v___x_5066_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15() -> *mut LeanObject {
    let mut v___x_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut LeanObject = core::ptr::null_mut();
    v___x_5067_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_5068_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14_once),
        _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14,
    );
    v___x_5069_ = lean_string_append(v___x_5068_, v___x_5067_);
    return v___x_5069_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonRpcOptions_fromJson(
    mut v_json_5070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5076_: u8 = 0;
    let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5082_: u8 = 0;
    let mut v_a_5083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5086_: u8 = 0;
    let mut v___x_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5090_: u8 = 0;
    let mut v_a_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5097_: u8 = 0;
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5103_: u8 = 0;
    let mut v_a_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5107_: u8 = 0;
    let mut v___x_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5111_: u8 = 0;
    let mut v_a_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5115_: u8 = 0;
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5120_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5071_ = l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__0;
                lean_inc(v_json_5070_);
                v___x_5072_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0(v_json_5070_, v___x_5071_);
                if lean_obj_tag(v___x_5072_) == 0 {
                    lean_dec(v_json_5070_);
                    v_a_5073_ = lean_ctor_get(v___x_5072_, 0);
                    v_isSharedCheck_5082_ = (!lean_is_exclusive(v___x_5072_)) as u8;
                    if v_isSharedCheck_5082_ == 0 {
                        v___x_5075_ = v___x_5072_;
                        v_isShared_5076_ = v_isSharedCheck_5082_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5073_);
                        lean_dec(v___x_5072_);
                        v___x_5075_ = lean_box(0);
                        v_isShared_5076_ = v_isSharedCheck_5082_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_5072_) == 0 {
                        lean_dec(v_json_5070_);
                        v_a_5083_ = lean_ctor_get(v___x_5072_, 0);
                        v_isSharedCheck_5090_ = (!lean_is_exclusive(v___x_5072_)) as u8;
                        if v_isSharedCheck_5090_ == 0 {
                            v___x_5085_ = v___x_5072_;
                            v_isShared_5086_ = v_isSharedCheck_5090_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5083_);
                            lean_dec(v___x_5072_);
                            v___x_5085_ = lean_box(0);
                            v_isShared_5086_ = v_isSharedCheck_5090_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5091_ = lean_ctor_get(v___x_5072_, 0);
                        lean_inc(v_a_5091_);
                        lean_dec_ref_known(v___x_5072_, 1);
                        v___x_5092_ = l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__10;
                        v___x_5093_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1(v_json_5070_, v___x_5092_);
                        if lean_obj_tag(v___x_5093_) == 0 {
                            lean_dec(v_a_5091_);
                            v_a_5094_ = lean_ctor_get(v___x_5093_, 0);
                            v_isSharedCheck_5103_ = (!lean_is_exclusive(v___x_5093_)) as u8;
                            if v_isSharedCheck_5103_ == 0 {
                                v___x_5096_ = v___x_5093_;
                                v_isShared_5097_ = v_isSharedCheck_5103_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_5094_);
                                lean_dec(v___x_5093_);
                                v___x_5096_ = lean_box(0);
                                v_isShared_5097_ = v_isSharedCheck_5103_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_5093_) == 0 {
                                lean_dec(v_a_5091_);
                                v_a_5104_ = lean_ctor_get(v___x_5093_, 0);
                                v_isSharedCheck_5111_ = (!lean_is_exclusive(v___x_5093_)) as u8;
                                if v_isSharedCheck_5111_ == 0 {
                                    v___x_5106_ = v___x_5093_;
                                    v_isShared_5107_ = v_isSharedCheck_5111_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_5104_);
                                    lean_dec(v___x_5093_);
                                    v___x_5106_ = lean_box(0);
                                    v_isShared_5107_ = v_isSharedCheck_5111_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_5112_ = lean_ctor_get(v___x_5093_, 0);
                                v_isSharedCheck_5120_ = (!lean_is_exclusive(v___x_5093_)) as u8;
                                if v_isSharedCheck_5120_ == 0 {
                                    v___x_5114_ = v___x_5093_;
                                    v_isShared_5115_ = v_isSharedCheck_5120_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_5112_);
                                    lean_dec(v___x_5093_);
                                    v___x_5114_ = lean_box(0);
                                    v_isShared_5115_ = v_isSharedCheck_5120_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5077_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9,
                );
                v___x_5078_ = lean_string_append(v___x_5077_, v_a_5073_);
                lean_dec(v_a_5073_);
                if v_isShared_5076_ == 0 {
                    lean_ctor_set(v___x_5075_, 0, v___x_5078_);
                    v___x_5080_ = v___x_5075_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5081_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5081_, 0, v___x_5078_);
                    v___x_5080_ = v_reuseFailAlloc_5081_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5080_;
            }
            3 => {
                if v_isShared_5086_ == 0 {
                    lean_ctor_set_tag(v___x_5085_, 0);
                    v___x_5088_ = v___x_5085_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5089_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5089_, 0, v_a_5083_);
                    v___x_5088_ = v_reuseFailAlloc_5089_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5088_;
            }
            5 => {
                v___x_5098_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15,
                );
                v___x_5099_ = lean_string_append(v___x_5098_, v_a_5094_);
                lean_dec(v_a_5094_);
                if v_isShared_5097_ == 0 {
                    lean_ctor_set(v___x_5096_, 0, v___x_5099_);
                    v___x_5101_ = v___x_5096_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5102_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5102_, 0, v___x_5099_);
                    v___x_5101_ = v_reuseFailAlloc_5102_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5101_;
            }
            7 => {
                if v_isShared_5107_ == 0 {
                    lean_ctor_set_tag(v___x_5106_, 0);
                    v___x_5109_ = v___x_5106_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5110_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5110_, 0, v_a_5104_);
                    v___x_5109_ = v_reuseFailAlloc_5110_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5109_;
            }
            9 => {
                v___x_5116_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5116_, 0, v_a_5091_);
                lean_ctor_set(v___x_5116_, 1, v_a_5112_);
                if v_isShared_5115_ == 0 {
                    lean_ctor_set(v___x_5114_, 0, v___x_5116_);
                    v___x_5118_ = v___x_5114_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5119_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5119_, 0, v___x_5116_);
                    v___x_5118_ = v_reuseFailAlloc_5119_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5118_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__0(
    mut v_k_5123_: *mut LeanObject,
    mut v_x_5124_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5124_) == 0 {
        let mut v___x_5125_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_k_5123_);
        v___x_5125_ = lean_box(0);
        return v___x_5125_;
    } else {
        let mut v_val_5126_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5127_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5129_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5130_: *mut LeanObject = core::ptr::null_mut();
        v_val_5126_ = lean_ctor_get(v_x_5124_, 0);
        lean_inc(v_val_5126_);
        lean_dec_ref_known(v_x_5124_, 1);
        v___x_5127_ = l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson(v_val_5126_);
        v___x_5128_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_5128_, 0, v_k_5123_);
        lean_ctor_set(v___x_5128_, 1, v___x_5127_);
        v___x_5129_ = lean_box(0);
        v___x_5130_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_5130_, 0, v___x_5128_);
        lean_ctor_set(v___x_5130_, 1, v___x_5129_);
        return v___x_5130_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1(
    mut v_k_5131_: *mut LeanObject,
    mut v_x_5132_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5132_) == 0 {
        let mut v___x_5133_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_k_5131_);
        v___x_5133_ = lean_box(0);
        return v___x_5133_;
    } else {
        let mut v_val_5134_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5135_: u8 = 0;
        let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5138_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5139_: *mut LeanObject = core::ptr::null_mut();
        v_val_5134_ = lean_ctor_get(v_x_5132_, 0);
        v___x_5135_ = (lean_unbox(v_val_5134_) as u8);
        v___x_5136_ = l_Lean_Lsp_instToJsonRpcWireFormat_toJson(v___x_5135_);
        v___x_5137_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_5137_, 0, v_k_5131_);
        lean_ctor_set(v___x_5137_, 1, v___x_5136_);
        v___x_5138_ = lean_box(0);
        v___x_5139_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_5139_, 0, v___x_5137_);
        lean_ctor_set(v___x_5139_, 1, v___x_5138_);
        return v___x_5139_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1___boxed(
    mut v_k_5140_: *mut LeanObject,
    mut v_x_5141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5142_: *mut LeanObject = core::ptr::null_mut();
    v_res_5142_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1(v_k_5140_, v_x_5141_);
    lean_dec(v_x_5141_);
    return v_res_5142_;
}
pub unsafe fn l_Lean_Lsp_instToJsonRpcOptions_toJson(
    mut v_x_5143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_highlightMatchesProvider_x3f_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rpcWireFormat_x3f_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5148_: u8 = 0;
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5161_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_highlightMatchesProvider_x3f_5144_ = lean_ctor_get(v_x_5143_, 0);
                v_rpcWireFormat_x3f_5145_ = lean_ctor_get(v_x_5143_, 1);
                v_isSharedCheck_5161_ = (!lean_is_exclusive(v_x_5143_)) as u8;
                if v_isSharedCheck_5161_ == 0 {
                    v___x_5147_ = v_x_5143_;
                    v_isShared_5148_ = v_isSharedCheck_5161_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rpcWireFormat_x3f_5145_);
                    lean_inc(v_highlightMatchesProvider_x3f_5144_);
                    lean_dec(v_x_5143_);
                    v___x_5147_ = lean_box(0);
                    v_isShared_5148_ = v_isSharedCheck_5161_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5149_ = l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__0;
                v___x_5150_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__0(
                    v___x_5149_,
                    v_highlightMatchesProvider_x3f_5144_,
                );
                v___x_5151_ = l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__10;
                v___x_5152_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1(
                    v___x_5151_,
                    v_rpcWireFormat_x3f_5145_,
                );
                lean_dec(v_rpcWireFormat_x3f_5145_);
                v___x_5153_ = lean_box(0);
                if v_isShared_5148_ == 0 {
                    lean_ctor_set_tag(v___x_5147_, 1);
                    lean_ctor_set(v___x_5147_, 1, v___x_5153_);
                    lean_ctor_set(v___x_5147_, 0, v___x_5152_);
                    v___x_5155_ = v___x_5147_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5160_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5160_, 0, v___x_5152_);
                    lean_ctor_set(v_reuseFailAlloc_5160_, 1, v___x_5153_);
                    v___x_5155_ = v_reuseFailAlloc_5160_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5156_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5156_, 0, v___x_5150_);
                lean_ctor_set(v___x_5156_, 1, v___x_5155_);
                v___x_5157_ = l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0;
                v___x_5158_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_5156_, v___x_5157_);
                v___x_5159_ = l_Lean_Json_mkObj(v___x_5158_);
                lean_dec(v___x_5158_);
                return v___x_5159_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0(
    mut v_x_5166_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5166_) == 0 {
        let mut v___x_5167_: *mut LeanObject = core::ptr::null_mut();
        v___x_5167_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0___closed__0;
        return v___x_5167_;
    } else {
        let mut v___x_5168_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5169_: *mut LeanObject = core::ptr::null_mut();
        v___x_5168_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_5168_, 0, v_x_5166_);
        v___x_5169_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_5169_, 0, v___x_5168_);
        return v___x_5169_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0(
    mut v_j_5170_: *mut LeanObject,
    mut v_k_5171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut LeanObject = core::ptr::null_mut();
    v___x_5172_ = l_Lean_Json_getObjValD(v_j_5170_, v_k_5171_);
    v___x_5173_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0(v___x_5172_);
    return v___x_5173_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0___boxed(
    mut v_j_5174_: *mut LeanObject,
    mut v_k_5175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5176_: *mut LeanObject = core::ptr::null_mut();
    v_res_5176_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0(
            v_j_5174_, v_k_5175_,
        );
    lean_dec_ref(v_k_5175_);
    return v_res_5176_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3() -> *mut LeanObject {
    let mut v___x_5183_: u8 = 0;
    let mut v___x_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut LeanObject = core::ptr::null_mut();
    v___x_5183_ = 1;
    v___x_5184_ = l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__2;
    v___x_5185_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5184_, v___x_5183_);
    return v___x_5185_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4() -> *mut LeanObject {
    let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
    v___x_5186_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6;
    v___x_5187_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3,
    );
    v___x_5188_ = lean_string_append(v___x_5187_, v___x_5186_);
    return v___x_5188_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6() -> *mut LeanObject {
    let mut v___x_5191_: u8 = 0;
    let mut v___x_5192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut LeanObject = core::ptr::null_mut();
    v___x_5191_ = 1;
    v___x_5192_ = l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__5;
    v___x_5193_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5192_, v___x_5191_);
    return v___x_5193_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7() -> *mut LeanObject {
    let mut v___x_5194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut LeanObject = core::ptr::null_mut();
    v___x_5194_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6,
    );
    v___x_5195_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4,
    );
    v___x_5196_ = lean_string_append(v___x_5195_, v___x_5194_);
    return v___x_5196_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8() -> *mut LeanObject {
    let mut v___x_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut LeanObject = core::ptr::null_mut();
    v___x_5197_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_5198_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7_once),
        _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7,
    );
    v___x_5199_ = lean_string_append(v___x_5198_, v___x_5197_);
    return v___x_5199_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9() -> *mut LeanObject {
    let mut v___x_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut LeanObject = core::ptr::null_mut();
    v___x_5200_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6,
    );
    v___x_5201_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4,
    );
    v___x_5202_ = lean_string_append(v___x_5201_, v___x_5200_);
    return v___x_5202_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10() -> *mut LeanObject {
    let mut v___x_5203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut LeanObject = core::ptr::null_mut();
    v___x_5203_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_5204_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9_once),
        _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9,
    );
    v___x_5205_ = lean_string_append(v___x_5204_, v___x_5203_);
    return v___x_5205_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonLeanModule_fromJson(
    mut v_json_5207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5213_: u8 = 0;
    let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5219_: u8 = 0;
    let mut v_a_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5223_: u8 = 0;
    let mut v___x_5225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5227_: u8 = 0;
    let mut v_a_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5234_: u8 = 0;
    let mut v___x_5235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5240_: u8 = 0;
    let mut v_a_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5244_: u8 = 0;
    let mut v___x_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5248_: u8 = 0;
    let mut v_a_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5255_: u8 = 0;
    let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5260_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5208_ = l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__0;
                lean_inc(v_json_5207_);
                v___x_5209_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_5207_, v___x_5208_);
                if lean_obj_tag(v___x_5209_) == 0 {
                    lean_dec(v_json_5207_);
                    v_a_5210_ = lean_ctor_get(v___x_5209_, 0);
                    v_isSharedCheck_5219_ = (!lean_is_exclusive(v___x_5209_)) as u8;
                    if v_isSharedCheck_5219_ == 0 {
                        v___x_5212_ = v___x_5209_;
                        v_isShared_5213_ = v_isSharedCheck_5219_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5210_);
                        lean_dec(v___x_5209_);
                        v___x_5212_ = lean_box(0);
                        v_isShared_5213_ = v_isSharedCheck_5219_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_5209_) == 0 {
                        lean_dec(v_json_5207_);
                        v_a_5220_ = lean_ctor_get(v___x_5209_, 0);
                        v_isSharedCheck_5227_ = (!lean_is_exclusive(v___x_5209_)) as u8;
                        if v_isSharedCheck_5227_ == 0 {
                            v___x_5222_ = v___x_5209_;
                            v_isShared_5223_ = v_isSharedCheck_5227_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5220_);
                            lean_dec(v___x_5209_);
                            v___x_5222_ = lean_box(0);
                            v_isShared_5223_ = v_isSharedCheck_5227_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5228_ = lean_ctor_get(v___x_5209_, 0);
                        lean_inc(v_a_5228_);
                        lean_dec_ref_known(v___x_5209_, 1);
                        v___x_5229_ =
                            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0;
                        lean_inc(v_json_5207_);
                        v___x_5230_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_5207_, v___x_5229_);
                        if lean_obj_tag(v___x_5230_) == 0 {
                            lean_dec(v_a_5228_);
                            lean_dec(v_json_5207_);
                            v_a_5231_ = lean_ctor_get(v___x_5230_, 0);
                            v_isSharedCheck_5240_ = (!lean_is_exclusive(v___x_5230_)) as u8;
                            if v_isSharedCheck_5240_ == 0 {
                                v___x_5233_ = v___x_5230_;
                                v_isShared_5234_ = v_isSharedCheck_5240_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_5231_);
                                lean_dec(v___x_5230_);
                                v___x_5233_ = lean_box(0);
                                v_isShared_5234_ = v_isSharedCheck_5240_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_5230_) == 0 {
                                lean_dec(v_a_5228_);
                                lean_dec(v_json_5207_);
                                v_a_5241_ = lean_ctor_get(v___x_5230_, 0);
                                v_isSharedCheck_5248_ = (!lean_is_exclusive(v___x_5230_)) as u8;
                                if v_isSharedCheck_5248_ == 0 {
                                    v___x_5243_ = v___x_5230_;
                                    v_isShared_5244_ = v_isSharedCheck_5248_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_5241_);
                                    lean_dec(v___x_5230_);
                                    v___x_5243_ = lean_box(0);
                                    v_isShared_5244_ = v_isSharedCheck_5248_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_5249_ = lean_ctor_get(v___x_5230_, 0);
                                lean_inc(v_a_5249_);
                                lean_dec_ref_known(v___x_5230_, 1);
                                v___x_5250_ =
                                    l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__11;
                                v___x_5251_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0(v_json_5207_, v___x_5250_);
                                v_a_5252_ = lean_ctor_get(v___x_5251_, 0);
                                v_isSharedCheck_5260_ = (!lean_is_exclusive(v___x_5251_)) as u8;
                                if v_isSharedCheck_5260_ == 0 {
                                    v___x_5254_ = v___x_5251_;
                                    v_isShared_5255_ = v_isSharedCheck_5260_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_5252_);
                                    lean_dec(v___x_5251_);
                                    v___x_5254_ = lean_box(0);
                                    v_isShared_5255_ = v_isSharedCheck_5260_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5214_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8,
                );
                v___x_5215_ = lean_string_append(v___x_5214_, v_a_5210_);
                lean_dec(v_a_5210_);
                if v_isShared_5213_ == 0 {
                    lean_ctor_set(v___x_5212_, 0, v___x_5215_);
                    v___x_5217_ = v___x_5212_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5218_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5218_, 0, v___x_5215_);
                    v___x_5217_ = v_reuseFailAlloc_5218_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5217_;
            }
            3 => {
                if v_isShared_5223_ == 0 {
                    lean_ctor_set_tag(v___x_5222_, 0);
                    v___x_5225_ = v___x_5222_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5226_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5226_, 0, v_a_5220_);
                    v___x_5225_ = v_reuseFailAlloc_5226_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5225_;
            }
            5 => {
                v___x_5235_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10,
                );
                v___x_5236_ = lean_string_append(v___x_5235_, v_a_5231_);
                lean_dec(v_a_5231_);
                if v_isShared_5234_ == 0 {
                    lean_ctor_set(v___x_5233_, 0, v___x_5236_);
                    v___x_5238_ = v___x_5233_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5239_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5239_, 0, v___x_5236_);
                    v___x_5238_ = v_reuseFailAlloc_5239_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5238_;
            }
            7 => {
                if v_isShared_5244_ == 0 {
                    lean_ctor_set_tag(v___x_5243_, 0);
                    v___x_5246_ = v___x_5243_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5247_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5247_, 0, v_a_5241_);
                    v___x_5246_ = v_reuseFailAlloc_5247_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5246_;
            }
            9 => {
                v___x_5256_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_5256_, 0, v_a_5228_);
                lean_ctor_set(v___x_5256_, 1, v_a_5249_);
                lean_ctor_set(v___x_5256_, 2, v_a_5252_);
                if v_isShared_5255_ == 0 {
                    lean_ctor_set(v___x_5254_, 0, v___x_5256_);
                    v___x_5258_ = v___x_5254_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5259_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5259_, 0, v___x_5256_);
                    v___x_5258_ = v_reuseFailAlloc_5259_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5258_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0(
    mut v_k_5263_: *mut LeanObject,
    mut v_x_5264_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5264_) == 0 {
        let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_k_5263_);
        v___x_5265_ = lean_box(0);
        return v___x_5265_;
    } else {
        let mut v_val_5266_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5267_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5269_: *mut LeanObject = core::ptr::null_mut();
        v_val_5266_ = lean_ctor_get(v_x_5264_, 0);
        lean_inc(v_val_5266_);
        v___x_5267_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_5267_, 0, v_k_5263_);
        lean_ctor_set(v___x_5267_, 1, v_val_5266_);
        v___x_5268_ = lean_box(0);
        v___x_5269_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_5269_, 0, v___x_5267_);
        lean_ctor_set(v___x_5269_, 1, v___x_5268_);
        return v___x_5269_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0___boxed(
    mut v_k_5270_: *mut LeanObject,
    mut v_x_5271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5272_: *mut LeanObject = core::ptr::null_mut();
    v_res_5272_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0(v_k_5270_, v_x_5271_);
    lean_dec(v_x_5271_);
    return v_res_5272_;
}
pub unsafe fn l_Lean_Lsp_instToJsonLeanModule_toJson(
    mut v_x_5273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uri_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut LeanObject = core::ptr::null_mut();
    v_name_5274_ = lean_ctor_get(v_x_5273_, 0);
    v_uri_5275_ = lean_ctor_get(v_x_5273_, 1);
    v_data_x3f_5276_ = lean_ctor_get(v_x_5273_, 2);
    v___x_5277_ = l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__0;
    lean_inc_ref(v_name_5274_);
    v___x_5278_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_5278_, 0, v_name_5274_);
    v___x_5279_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5279_, 0, v___x_5277_);
    lean_ctor_set(v___x_5279_, 1, v___x_5278_);
    v___x_5280_ = lean_box(0);
    v___x_5281_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5281_, 0, v___x_5279_);
    lean_ctor_set(v___x_5281_, 1, v___x_5280_);
    v___x_5282_ = l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0;
    lean_inc_ref(v_uri_5275_);
    v___x_5283_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_5283_, 0, v_uri_5275_);
    v___x_5284_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5284_, 0, v___x_5282_);
    lean_ctor_set(v___x_5284_, 1, v___x_5283_);
    v___x_5285_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5285_, 0, v___x_5284_);
    lean_ctor_set(v___x_5285_, 1, v___x_5280_);
    v___x_5286_ = l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__11;
    v___x_5287_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0(
        v___x_5286_,
        v_data_x3f_5276_,
    );
    v___x_5288_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5288_, 0, v___x_5287_);
    lean_ctor_set(v___x_5288_, 1, v___x_5280_);
    v___x_5289_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5289_, 0, v___x_5285_);
    lean_ctor_set(v___x_5289_, 1, v___x_5288_);
    v___x_5290_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5290_, 0, v___x_5281_);
    lean_ctor_set(v___x_5290_, 1, v___x_5289_);
    v___x_5291_ = l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0;
    v___x_5292_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_5290_, v___x_5291_);
    v___x_5293_ = l_Lean_Json_mkObj(v___x_5292_);
    lean_dec(v___x_5292_);
    return v___x_5293_;
}
pub unsafe fn l_Lean_Lsp_instToJsonLeanModule_toJson___boxed(
    mut v_x_5294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5295_: *mut LeanObject = core::ptr::null_mut();
    v_res_5295_ = l_Lean_Lsp_instToJsonLeanModule_toJson(v_x_5294_);
    lean_dec_ref(v_x_5294_);
    return v_res_5295_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2()
-> *mut LeanObject {
    let mut v___x_5303_: u8 = 0;
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    v___x_5303_ = 1;
    v___x_5304_ = l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__1;
    v___x_5305_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5304_, v___x_5303_);
    return v___x_5305_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3()
-> *mut LeanObject {
    let mut v___x_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut LeanObject = core::ptr::null_mut();
    v___x_5306_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6;
    v___x_5307_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2,
    );
    v___x_5308_ = lean_string_append(v___x_5307_, v___x_5306_);
    return v___x_5308_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4()
-> *mut LeanObject {
    let mut v___x_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut LeanObject = core::ptr::null_mut();
    v___x_5309_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9,
    );
    v___x_5310_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3,
    );
    v___x_5311_ = lean_string_append(v___x_5310_, v___x_5309_);
    return v___x_5311_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5()
-> *mut LeanObject {
    let mut v___x_5312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut LeanObject = core::ptr::null_mut();
    v___x_5312_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_5313_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4,
    );
    v___x_5314_ = lean_string_append(v___x_5313_, v___x_5312_);
    return v___x_5314_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson(
    mut v_json_5315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5321_: u8 = 0;
    let mut v___x_5322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5327_: u8 = 0;
    let mut v_a_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5331_: u8 = 0;
    let mut v___x_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5335_: u8 = 0;
    let mut v_a_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5339_: u8 = 0;
    let mut v___x_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5343_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5316_ =
                    l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0;
                v___x_5317_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_json_5315_, v___x_5316_);
                if lean_obj_tag(v___x_5317_) == 0 {
                    v_a_5318_ = lean_ctor_get(v___x_5317_, 0);
                    v_isSharedCheck_5327_ = (!lean_is_exclusive(v___x_5317_)) as u8;
                    if v_isSharedCheck_5327_ == 0 {
                        v___x_5320_ = v___x_5317_;
                        v_isShared_5321_ = v_isSharedCheck_5327_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5318_);
                        lean_dec(v___x_5317_);
                        v___x_5320_ = lean_box(0);
                        v_isShared_5321_ = v_isSharedCheck_5327_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_5317_) == 0 {
                        v_a_5328_ = lean_ctor_get(v___x_5317_, 0);
                        v_isSharedCheck_5335_ = (!lean_is_exclusive(v___x_5317_)) as u8;
                        if v_isSharedCheck_5335_ == 0 {
                            v___x_5330_ = v___x_5317_;
                            v_isShared_5331_ = v_isSharedCheck_5335_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5328_);
                            lean_dec(v___x_5317_);
                            v___x_5330_ = lean_box(0);
                            v_isShared_5331_ = v_isSharedCheck_5335_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5336_ = lean_ctor_get(v___x_5317_, 0);
                        v_isSharedCheck_5343_ = (!lean_is_exclusive(v___x_5317_)) as u8;
                        if v_isSharedCheck_5343_ == 0 {
                            v___x_5338_ = v___x_5317_;
                            v_isShared_5339_ = v_isSharedCheck_5343_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_5336_);
                            lean_dec(v___x_5317_);
                            v___x_5338_ = lean_box(0);
                            v_isShared_5339_ = v_isSharedCheck_5343_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5322_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5_once), _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5);
                v___x_5323_ = lean_string_append(v___x_5322_, v_a_5318_);
                lean_dec(v_a_5318_);
                if v_isShared_5321_ == 0 {
                    lean_ctor_set(v___x_5320_, 0, v___x_5323_);
                    v___x_5325_ = v___x_5320_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5326_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5326_, 0, v___x_5323_);
                    v___x_5325_ = v_reuseFailAlloc_5326_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5325_;
            }
            3 => {
                if v_isShared_5331_ == 0 {
                    lean_ctor_set_tag(v___x_5330_, 0);
                    v___x_5333_ = v___x_5330_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5334_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5334_, 0, v_a_5328_);
                    v___x_5333_ = v_reuseFailAlloc_5334_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5333_;
            }
            5 => {
                if v_isShared_5339_ == 0 {
                    v___x_5341_ = v___x_5338_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5342_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5342_, 0, v_a_5336_);
                    v___x_5341_ = v_reuseFailAlloc_5342_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5341_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams_toJson(
    mut v_x_5346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut LeanObject = core::ptr::null_mut();
    v___x_5347_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0;
    v___x_5348_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_x_5346_);
    v___x_5349_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5349_, 0, v___x_5347_);
    lean_ctor_set(v___x_5349_, 1, v___x_5348_);
    v___x_5350_ = lean_box(0);
    v___x_5351_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5351_, 0, v___x_5349_);
    lean_ctor_set(v___x_5351_, 1, v___x_5350_);
    v___x_5352_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5352_, 0, v___x_5351_);
    lean_ctor_set(v___x_5352_, 1, v___x_5350_);
    v___x_5353_ = l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0;
    v___x_5354_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_5352_, v___x_5353_);
    v___x_5355_ = l_Lean_Json_mkObj(v___x_5354_);
    lean_dec(v___x_5354_);
    return v___x_5355_;
}
pub unsafe fn l_Lean_Lsp_LeanImportMetaKind_ctorIdx(mut v_x_5358_: u8) -> *mut LeanObject {
    match v_x_5358_ {
        0 => {
            let mut v___x_5359_: *mut LeanObject = core::ptr::null_mut();
            v___x_5359_ = lean_unsigned_to_nat(0);
            return v___x_5359_;
        }
        1 => {
            let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
            v___x_5360_ = lean_unsigned_to_nat(1);
            return v___x_5360_;
        }
        _ => {
            let mut v___x_5361_: *mut LeanObject = core::ptr::null_mut();
            v___x_5361_ = lean_unsigned_to_nat(2);
            return v___x_5361_;
        }
    }
}
pub unsafe fn l_Lean_Lsp_LeanImportMetaKind_ctorIdx___boxed(
    mut v_x_5362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_5363_: u8 = 0;
    let mut v_res_5364_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_5363_ = (lean_unbox(v_x_5362_) as u8);
    v_res_5364_ = l_Lean_Lsp_LeanImportMetaKind_ctorIdx(v_x_boxed_5363_);
    return v_res_5364_;
}
pub unsafe fn l_Lean_Lsp_LeanImportMetaKind_toCtorIdx(mut v_x_5365_: u8) -> *mut LeanObject {
    let mut v___x_5366_: *mut LeanObject = core::ptr::null_mut();
    v___x_5366_ = l_Lean_Lsp_LeanImportMetaKind_ctorIdx(v_x_5365_);
    return v___x_5366_;
}
pub unsafe fn l_Lean_Lsp_LeanImportMetaKind_toCtorIdx___boxed(
    mut v_x_5367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_5368_: u8 = 0;
    let mut v_res_5369_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_5368_ = (lean_unbox(v_x_5367_) as u8);
    v_res_5369_ = l_Lean_Lsp_LeanImportMetaKind_toCtorIdx(v_x_4__boxed_5368_);
    return v_res_5369_;
}
pub unsafe fn l_Lean_Lsp_LeanImportMetaKind_ctorElim___redArg(
    mut v_k_5370_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_5370_);
    return v_k_5370_;
}
pub unsafe fn l_Lean_Lsp_LeanImportMetaKind_ctorElim___redArg___boxed(
    mut v_k_5371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5372_: *mut LeanObject = core::ptr::null_mut();
    v_res_5372_ = l_Lean_Lsp_LeanImportMetaKind_ctorElim___redArg(v_k_5371_);
    lean_dec(v_k_5371_);
    return v_res_5372_;
}
pub unsafe fn l_Lean_Lsp_LeanImportMetaKind_ctorElim(
    mut v_motive_5373_: *mut LeanObject,
    mut v_ctorIdx_5374_: *mut LeanObject,
    mut v_t_5375_: u8,
    mut v_h_5376_: *mut LeanObject,
    mut v_k_5377_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_5377_);
    return v_k_5377_;
}
pub unsafe fn l_Lean_Lsp_LeanImportMetaKind_ctorElim___boxed(
    mut v_motive_5378_: *mut LeanObject,
    mut v_ctorIdx_5379_: *mut LeanObject,
    mut v_t_5380_: *mut LeanObject,
    mut v_h_5381_: *mut LeanObject,
    mut v_k_5382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_5383_: u8 = 0;
    let mut v_res_5384_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_5383_ = (lean_unbox(v_t_5380_) as u8);
    v_res_5384_ = l_Lean_Lsp_LeanImportMetaKind_ctorElim(
        v_motive_5378_,
        v_ctorIdx_5379_,
        v_t_boxed_5383_,
        v_h_5381_,
        v_k_5382_,
    );
    lean_dec(v_k_5382_);
    lean_dec(v_ctorIdx_5379_);
    return v_res_5384_;
}
pub unsafe fn l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim___redArg(
    mut v_nonMeta_5385_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_nonMeta_5385_);
    return v_nonMeta_5385_;
}
pub unsafe fn l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim___redArg___boxed(
    mut v_nonMeta_5386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5387_: *mut LeanObject = core::ptr::null_mut();
    v_res_5387_ = l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim___redArg(v_nonMeta_5386_);
    lean_dec(v_nonMeta_5386_);
    return v_res_5387_;
}
pub unsafe fn l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim(
    mut v_motive_5388_: *mut LeanObject,
    mut v_t_5389_: u8,
    mut v_h_5390_: *mut LeanObject,
    mut v_nonMeta_5391_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_nonMeta_5391_);
    return v_nonMeta_5391_;
}
pub unsafe fn l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim___boxed(
    mut v_motive_5392_: *mut LeanObject,
    mut v_t_5393_: *mut LeanObject,
    mut v_h_5394_: *mut LeanObject,
    mut v_nonMeta_5395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_5396_: u8 = 0;
    let mut v_res_5397_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_5396_ = (lean_unbox(v_t_5393_) as u8);
    v_res_5397_ = l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim(
        v_motive_5392_,
        v_t_boxed_5396_,
        v_h_5394_,
        v_nonMeta_5395_,
    );
    lean_dec(v_nonMeta_5395_);
    return v_res_5397_;
}
pub unsafe fn l_Lean_Lsp_LeanImportMetaKind_meta_elim___redArg(
    mut v_meta_5398_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_meta_5398_);
    return v_meta_5398_;
}
pub unsafe fn l_Lean_Lsp_LeanImportMetaKind_meta_elim___redArg___boxed(
    mut v_meta_5399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5400_: *mut LeanObject = core::ptr::null_mut();
    v_res_5400_ = l_Lean_Lsp_LeanImportMetaKind_meta_elim___redArg(v_meta_5399_);
    lean_dec(v_meta_5399_);
    return v_res_5400_;
}
pub unsafe fn l_Lean_Lsp_LeanImportMetaKind_meta_elim(
    mut v_motive_5401_: *mut LeanObject,
    mut v_t_5402_: u8,
    mut v_h_5403_: *mut LeanObject,
    mut v_meta_5404_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_meta_5404_);
    return v_meta_5404_;
}
pub unsafe fn l_Lean_Lsp_LeanImportMetaKind_meta_elim___boxed(
    mut v_motive_5405_: *mut LeanObject,
    mut v_t_5406_: *mut LeanObject,
    mut v_h_5407_: *mut LeanObject,
    mut v_meta_5408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_5409_: u8 = 0;
    let mut v_res_5410_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_5409_ = (lean_unbox(v_t_5406_) as u8);
    v_res_5410_ = l_Lean_Lsp_LeanImportMetaKind_meta_elim(
        v_motive_5405_,
        v_t_boxed_5409_,
        v_h_5407_,
        v_meta_5408_,
    );
    lean_dec(v_meta_5408_);
    return v_res_5410_;
}
pub unsafe fn l_Lean_Lsp_LeanImportMetaKind_full_elim___redArg(
    mut v_full_5411_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_full_5411_);
    return v_full_5411_;
}
pub unsafe fn l_Lean_Lsp_LeanImportMetaKind_full_elim___redArg___boxed(
    mut v_full_5412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5413_: *mut LeanObject = core::ptr::null_mut();
    v_res_5413_ = l_Lean_Lsp_LeanImportMetaKind_full_elim___redArg(v_full_5412_);
    lean_dec(v_full_5412_);
    return v_res_5413_;
}
pub unsafe fn l_Lean_Lsp_LeanImportMetaKind_full_elim(
    mut v_motive_5414_: *mut LeanObject,
    mut v_t_5415_: u8,
    mut v_h_5416_: *mut LeanObject,
    mut v_full_5417_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_full_5417_);
    return v_full_5417_;
}
pub unsafe fn l_Lean_Lsp_LeanImportMetaKind_full_elim___boxed(
    mut v_motive_5418_: *mut LeanObject,
    mut v_t_5419_: *mut LeanObject,
    mut v_h_5420_: *mut LeanObject,
    mut v_full_5421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_5422_: u8 = 0;
    let mut v_res_5423_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_5422_ = (lean_unbox(v_t_5419_) as u8);
    v_res_5423_ = l_Lean_Lsp_LeanImportMetaKind_full_elim(
        v_motive_5418_,
        v_t_boxed_5422_,
        v_h_5420_,
        v_full_5421_,
    );
    lean_dec(v_full_5421_);
    return v_res_5423_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedLeanImportMetaKind_default() -> u8 {
    let mut v___x_5424_: u8 = 0;
    v___x_5424_ = 0;
    return v___x_5424_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedLeanImportMetaKind() -> u8 {
    let mut v___x_5425_: u8 = 0;
    v___x_5425_ = 0;
    return v___x_5425_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson(
    mut v_json_5442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5443_: *mut LeanObject = core::ptr::null_mut();
    v___x_5443_ = l_Lean_Json_getTag_x3f(v_json_5442_);
    if lean_obj_tag(v___x_5443_) == 0 {
        let mut v___x_5444_: *mut LeanObject = core::ptr::null_mut();
        v___x_5444_ = l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__0;
        return v___x_5444_;
    } else {
        let mut v_val_5445_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5446_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5447_: u8 = 0;
        v_val_5445_ = lean_ctor_get(v___x_5443_, 0);
        lean_inc(v_val_5445_);
        lean_dec_ref_known(v___x_5443_, 1);
        v___x_5446_ = l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__1;
        v___x_5447_ = lean_string_dec_eq(v_val_5445_, v___x_5446_);
        if v___x_5447_ == 0 {
            let mut v___x_5448_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5449_: u8 = 0;
            v___x_5448_ = l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__2;
            v___x_5449_ = lean_string_dec_eq(v_val_5445_, v___x_5448_);
            if v___x_5449_ == 0 {
                let mut v___x_5450_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5451_: u8 = 0;
                v___x_5450_ = l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__3;
                v___x_5451_ = lean_string_dec_eq(v_val_5445_, v___x_5450_);
                lean_dec(v_val_5445_);
                if v___x_5451_ == 0 {
                    let mut v___x_5452_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5452_ = l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__4;
                    return v___x_5452_;
                } else {
                    let mut v___x_5453_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5453_ = l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__5;
                    return v___x_5453_;
                }
            } else {
                let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_val_5445_);
                v___x_5454_ = l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__6;
                return v___x_5454_;
            }
        } else {
            let mut v___x_5455_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_val_5445_);
            v___x_5455_ = l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__7;
            return v___x_5455_;
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson(mut v_x_5464_: u8) -> *mut LeanObject {
    match v_x_5464_ {
        0 => {
            let mut v___x_5465_: *mut LeanObject = core::ptr::null_mut();
            v___x_5465_ = l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__0;
            return v___x_5465_;
        }
        1 => {
            let mut v___x_5466_: *mut LeanObject = core::ptr::null_mut();
            v___x_5466_ = l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__1;
            return v___x_5466_;
        }
        _ => {
            let mut v___x_5467_: *mut LeanObject = core::ptr::null_mut();
            v___x_5467_ = l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__2;
            return v___x_5467_;
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___boxed(
    mut v_x_5468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_64__boxed_5469_: u8 = 0;
    let mut v_res_5470_: *mut LeanObject = core::ptr::null_mut();
    v_x_64__boxed_5469_ = (lean_unbox(v_x_5468_) as u8);
    v_res_5470_ = l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson(v_x_64__boxed_5469_);
    return v_res_5470_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0(
    mut v_j_5473_: *mut LeanObject,
    mut v_k_5474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut LeanObject = core::ptr::null_mut();
    v___x_5475_ = l_Lean_Json_getObjValD(v_j_5473_, v_k_5474_);
    v___x_5476_ = l_Lean_Json_getBool_x3f(v___x_5475_);
    lean_dec(v___x_5475_);
    return v___x_5476_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0___boxed(
    mut v_j_5477_: *mut LeanObject,
    mut v_k_5478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5479_: *mut LeanObject = core::ptr::null_mut();
    v_res_5479_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0(
            v_j_5477_, v_k_5478_,
        );
    lean_dec_ref(v_k_5478_);
    return v_res_5479_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__1(
    mut v_j_5480_: *mut LeanObject,
    mut v_k_5481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: *mut LeanObject = core::ptr::null_mut();
    v___x_5482_ = l_Lean_Json_getObjValD(v_j_5480_, v_k_5481_);
    v___x_5483_ = l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson(v___x_5482_);
    return v___x_5483_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__1___boxed(
    mut v_j_5484_: *mut LeanObject,
    mut v_k_5485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5486_: *mut LeanObject = core::ptr::null_mut();
    v_res_5486_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__1(
            v_j_5484_, v_k_5485_,
        );
    lean_dec_ref(v_k_5485_);
    return v_res_5486_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3() -> *mut LeanObject
{
    let mut v___x_5493_: u8 = 0;
    let mut v___x_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut LeanObject = core::ptr::null_mut();
    v___x_5493_ = 1;
    v___x_5494_ = l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__2;
    v___x_5495_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5494_, v___x_5493_);
    return v___x_5495_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4() -> *mut LeanObject
{
    let mut v___x_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut LeanObject = core::ptr::null_mut();
    v___x_5496_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6;
    v___x_5497_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3,
    );
    v___x_5498_ = lean_string_append(v___x_5497_, v___x_5496_);
    return v___x_5498_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6() -> *mut LeanObject
{
    let mut v___x_5501_: u8 = 0;
    let mut v___x_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
    v___x_5501_ = 1;
    v___x_5502_ = l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__5;
    v___x_5503_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5502_, v___x_5501_);
    return v___x_5503_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7() -> *mut LeanObject
{
    let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut LeanObject = core::ptr::null_mut();
    v___x_5504_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6,
    );
    v___x_5505_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4,
    );
    v___x_5506_ = lean_string_append(v___x_5505_, v___x_5504_);
    return v___x_5506_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8() -> *mut LeanObject
{
    let mut v___x_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    v___x_5507_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_5508_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7_once),
        _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7,
    );
    v___x_5509_ = lean_string_append(v___x_5508_, v___x_5507_);
    return v___x_5509_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11() -> *mut LeanObject
{
    let mut v___x_5513_: u8 = 0;
    let mut v___x_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut LeanObject = core::ptr::null_mut();
    v___x_5513_ = 1;
    v___x_5514_ = l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__10;
    v___x_5515_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5514_, v___x_5513_);
    return v___x_5515_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12() -> *mut LeanObject
{
    let mut v___x_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut LeanObject = core::ptr::null_mut();
    v___x_5516_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11_once),
        _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11,
    );
    v___x_5517_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4,
    );
    v___x_5518_ = lean_string_append(v___x_5517_, v___x_5516_);
    return v___x_5518_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13() -> *mut LeanObject
{
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut LeanObject = core::ptr::null_mut();
    v___x_5519_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_5520_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12_once),
        _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12,
    );
    v___x_5521_ = lean_string_append(v___x_5520_, v___x_5519_);
    return v___x_5521_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16() -> *mut LeanObject
{
    let mut v___x_5525_: u8 = 0;
    let mut v___x_5526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut LeanObject = core::ptr::null_mut();
    v___x_5525_ = 1;
    v___x_5526_ = l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__15;
    v___x_5527_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5526_, v___x_5525_);
    return v___x_5527_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17() -> *mut LeanObject
{
    let mut v___x_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut LeanObject = core::ptr::null_mut();
    v___x_5528_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16_once),
        _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16,
    );
    v___x_5529_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4,
    );
    v___x_5530_ = lean_string_append(v___x_5529_, v___x_5528_);
    return v___x_5530_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18() -> *mut LeanObject
{
    let mut v___x_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut LeanObject = core::ptr::null_mut();
    v___x_5531_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_5532_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17_once),
        _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17,
    );
    v___x_5533_ = lean_string_append(v___x_5532_, v___x_5531_);
    return v___x_5533_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonLeanImportKind_fromJson(
    mut v_json_5534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5540_: u8 = 0;
    let mut v___x_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5546_: u8 = 0;
    let mut v_a_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5550_: u8 = 0;
    let mut v___x_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5554_: u8 = 0;
    let mut v_a_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5561_: u8 = 0;
    let mut v___x_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5567_: u8 = 0;
    let mut v_a_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5571_: u8 = 0;
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5575_: u8 = 0;
    let mut v_a_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5582_: u8 = 0;
    let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5588_: u8 = 0;
    let mut v_a_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5592_: u8 = 0;
    let mut v___x_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5596_: u8 = 0;
    let mut v_a_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5600_: u8 = 0;
    let mut v___x_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: u8 = 0;
    let mut v___x_5603_: u8 = 0;
    let mut v___x_5604_: u8 = 0;
    let mut v___x_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5608_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5535_ = l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__0;
                lean_inc(v_json_5534_);
                v___x_5536_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0(v_json_5534_, v___x_5535_);
                if lean_obj_tag(v___x_5536_) == 0 {
                    lean_dec(v_json_5534_);
                    v_a_5537_ = lean_ctor_get(v___x_5536_, 0);
                    v_isSharedCheck_5546_ = (!lean_is_exclusive(v___x_5536_)) as u8;
                    if v_isSharedCheck_5546_ == 0 {
                        v___x_5539_ = v___x_5536_;
                        v_isShared_5540_ = v_isSharedCheck_5546_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5537_);
                        lean_dec(v___x_5536_);
                        v___x_5539_ = lean_box(0);
                        v_isShared_5540_ = v_isSharedCheck_5546_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_5536_) == 0 {
                        lean_dec(v_json_5534_);
                        v_a_5547_ = lean_ctor_get(v___x_5536_, 0);
                        v_isSharedCheck_5554_ = (!lean_is_exclusive(v___x_5536_)) as u8;
                        if v_isSharedCheck_5554_ == 0 {
                            v___x_5549_ = v___x_5536_;
                            v_isShared_5550_ = v_isSharedCheck_5554_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5547_);
                            lean_dec(v___x_5536_);
                            v___x_5549_ = lean_box(0);
                            v_isShared_5550_ = v_isSharedCheck_5554_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5555_ = lean_ctor_get(v___x_5536_, 0);
                        lean_inc(v_a_5555_);
                        lean_dec_ref_known(v___x_5536_, 1);
                        v___x_5556_ = l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__9;
                        lean_inc(v_json_5534_);
                        v___x_5557_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0(v_json_5534_, v___x_5556_);
                        if lean_obj_tag(v___x_5557_) == 0 {
                            lean_dec(v_a_5555_);
                            lean_dec(v_json_5534_);
                            v_a_5558_ = lean_ctor_get(v___x_5557_, 0);
                            v_isSharedCheck_5567_ = (!lean_is_exclusive(v___x_5557_)) as u8;
                            if v_isSharedCheck_5567_ == 0 {
                                v___x_5560_ = v___x_5557_;
                                v_isShared_5561_ = v_isSharedCheck_5567_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_5558_);
                                lean_dec(v___x_5557_);
                                v___x_5560_ = lean_box(0);
                                v_isShared_5561_ = v_isSharedCheck_5567_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_5557_) == 0 {
                                lean_dec(v_a_5555_);
                                lean_dec(v_json_5534_);
                                v_a_5568_ = lean_ctor_get(v___x_5557_, 0);
                                v_isSharedCheck_5575_ = (!lean_is_exclusive(v___x_5557_)) as u8;
                                if v_isSharedCheck_5575_ == 0 {
                                    v___x_5570_ = v___x_5557_;
                                    v_isShared_5571_ = v_isSharedCheck_5575_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_5568_);
                                    lean_dec(v___x_5557_);
                                    v___x_5570_ = lean_box(0);
                                    v_isShared_5571_ = v_isSharedCheck_5575_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_5576_ = lean_ctor_get(v___x_5557_, 0);
                                lean_inc(v_a_5576_);
                                lean_dec_ref_known(v___x_5557_, 1);
                                v___x_5577_ =
                                    l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__14;
                                v___x_5578_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__1(v_json_5534_, v___x_5577_);
                                if lean_obj_tag(v___x_5578_) == 0 {
                                    lean_dec(v_a_5576_);
                                    lean_dec(v_a_5555_);
                                    v_a_5579_ = lean_ctor_get(v___x_5578_, 0);
                                    v_isSharedCheck_5588_ = (!lean_is_exclusive(v___x_5578_)) as u8;
                                    if v_isSharedCheck_5588_ == 0 {
                                        v___x_5581_ = v___x_5578_;
                                        v_isShared_5582_ = v_isSharedCheck_5588_;
                                        state = 9;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5579_);
                                        lean_dec(v___x_5578_);
                                        v___x_5581_ = lean_box(0);
                                        v_isShared_5582_ = v_isSharedCheck_5588_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if lean_obj_tag(v___x_5578_) == 0 {
                                        lean_dec(v_a_5576_);
                                        lean_dec(v_a_5555_);
                                        v_a_5589_ = lean_ctor_get(v___x_5578_, 0);
                                        v_isSharedCheck_5596_ =
                                            (!lean_is_exclusive(v___x_5578_)) as u8;
                                        if v_isSharedCheck_5596_ == 0 {
                                            v___x_5591_ = v___x_5578_;
                                            v_isShared_5592_ = v_isSharedCheck_5596_;
                                            state = 11;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5589_);
                                            lean_dec(v___x_5578_);
                                            v___x_5591_ = lean_box(0);
                                            v_isShared_5592_ = v_isSharedCheck_5596_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_5597_ = lean_ctor_get(v___x_5578_, 0);
                                        v_isSharedCheck_5608_ =
                                            (!lean_is_exclusive(v___x_5578_)) as u8;
                                        if v_isSharedCheck_5608_ == 0 {
                                            v___x_5599_ = v___x_5578_;
                                            v_isShared_5600_ = v_isSharedCheck_5608_;
                                            state = 13;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5597_);
                                            lean_dec(v___x_5578_);
                                            v___x_5599_ = lean_box(0);
                                            v_isShared_5600_ = v_isSharedCheck_5608_;
                                            state = 13;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5541_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8,
                );
                v___x_5542_ = lean_string_append(v___x_5541_, v_a_5537_);
                lean_dec(v_a_5537_);
                if v_isShared_5540_ == 0 {
                    lean_ctor_set(v___x_5539_, 0, v___x_5542_);
                    v___x_5544_ = v___x_5539_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5545_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5545_, 0, v___x_5542_);
                    v___x_5544_ = v_reuseFailAlloc_5545_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5544_;
            }
            3 => {
                if v_isShared_5550_ == 0 {
                    lean_ctor_set_tag(v___x_5549_, 0);
                    v___x_5552_ = v___x_5549_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5553_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5553_, 0, v_a_5547_);
                    v___x_5552_ = v_reuseFailAlloc_5553_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5552_;
            }
            5 => {
                v___x_5562_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13,
                );
                v___x_5563_ = lean_string_append(v___x_5562_, v_a_5558_);
                lean_dec(v_a_5558_);
                if v_isShared_5561_ == 0 {
                    lean_ctor_set(v___x_5560_, 0, v___x_5563_);
                    v___x_5565_ = v___x_5560_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5566_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5566_, 0, v___x_5563_);
                    v___x_5565_ = v_reuseFailAlloc_5566_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5565_;
            }
            7 => {
                if v_isShared_5571_ == 0 {
                    lean_ctor_set_tag(v___x_5570_, 0);
                    v___x_5573_ = v___x_5570_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5574_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5574_, 0, v_a_5568_);
                    v___x_5573_ = v_reuseFailAlloc_5574_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5573_;
            }
            9 => {
                v___x_5583_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18,
                );
                v___x_5584_ = lean_string_append(v___x_5583_, v_a_5579_);
                lean_dec(v_a_5579_);
                if v_isShared_5582_ == 0 {
                    lean_ctor_set(v___x_5581_, 0, v___x_5584_);
                    v___x_5586_ = v___x_5581_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5587_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5587_, 0, v___x_5584_);
                    v___x_5586_ = v_reuseFailAlloc_5587_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5586_;
            }
            11 => {
                if v_isShared_5592_ == 0 {
                    lean_ctor_set_tag(v___x_5591_, 0);
                    v___x_5594_ = v___x_5591_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5595_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5595_, 0, v_a_5589_);
                    v___x_5594_ = v_reuseFailAlloc_5595_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5594_;
            }
            13 => {
                v___x_5601_ = lean_alloc_ctor(0, 0, (3) as u32);
                v___x_5602_ = (lean_unbox(v_a_5555_) as u8);
                lean_dec(v_a_5555_);
                lean_ctor_set_uint8(v___x_5601_, 0 as u32, v___x_5602_);
                v___x_5603_ = (lean_unbox(v_a_5576_) as u8);
                lean_dec(v_a_5576_);
                lean_ctor_set_uint8(v___x_5601_, 1 as u32, v___x_5603_);
                v___x_5604_ = (lean_unbox(v_a_5597_) as u8);
                lean_dec(v_a_5597_);
                lean_ctor_set_uint8(v___x_5601_, 2 as u32, v___x_5604_);
                if v_isShared_5600_ == 0 {
                    lean_ctor_set(v___x_5599_, 0, v___x_5601_);
                    v___x_5606_ = v___x_5599_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5607_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5607_, 0, v___x_5601_);
                    v___x_5606_ = v_reuseFailAlloc_5607_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5606_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonLeanImportKind_toJson(
    mut v_x_5611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isPrivate_5612_: u8 = 0;
    let mut v_isAll_5613_: u8 = 0;
    let mut v_metaKind_5614_: u8 = 0;
    let mut v___x_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
    v_isPrivate_5612_ = lean_ctor_get_uint8(v_x_5611_, 0 as u32);
    v_isAll_5613_ = lean_ctor_get_uint8(v_x_5611_, 1 as u32);
    v_metaKind_5614_ = lean_ctor_get_uint8(v_x_5611_, 2 as u32);
    v___x_5615_ = l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__0;
    v___x_5616_ = lean_alloc_ctor(1, 0, (1) as u32);
    lean_ctor_set_uint8(v___x_5616_, 0 as u32, v_isPrivate_5612_);
    v___x_5617_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5617_, 0, v___x_5615_);
    lean_ctor_set(v___x_5617_, 1, v___x_5616_);
    v___x_5618_ = lean_box(0);
    v___x_5619_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5619_, 0, v___x_5617_);
    lean_ctor_set(v___x_5619_, 1, v___x_5618_);
    v___x_5620_ = l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__9;
    v___x_5621_ = lean_alloc_ctor(1, 0, (1) as u32);
    lean_ctor_set_uint8(v___x_5621_, 0 as u32, v_isAll_5613_);
    v___x_5622_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5622_, 0, v___x_5620_);
    lean_ctor_set(v___x_5622_, 1, v___x_5621_);
    v___x_5623_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5623_, 0, v___x_5622_);
    lean_ctor_set(v___x_5623_, 1, v___x_5618_);
    v___x_5624_ = l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__14;
    v___x_5625_ = l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson(v_metaKind_5614_);
    v___x_5626_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5626_, 0, v___x_5624_);
    lean_ctor_set(v___x_5626_, 1, v___x_5625_);
    v___x_5627_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5627_, 0, v___x_5626_);
    lean_ctor_set(v___x_5627_, 1, v___x_5618_);
    v___x_5628_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5628_, 0, v___x_5627_);
    lean_ctor_set(v___x_5628_, 1, v___x_5618_);
    v___x_5629_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5629_, 0, v___x_5623_);
    lean_ctor_set(v___x_5629_, 1, v___x_5628_);
    v___x_5630_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5630_, 0, v___x_5619_);
    lean_ctor_set(v___x_5630_, 1, v___x_5629_);
    v___x_5631_ = l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0;
    v___x_5632_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_5630_, v___x_5631_);
    v___x_5633_ = l_Lean_Json_mkObj(v___x_5632_);
    lean_dec(v___x_5632_);
    return v___x_5633_;
}
pub unsafe fn l_Lean_Lsp_instToJsonLeanImportKind_toJson___boxed(
    mut v_x_5634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5635_: *mut LeanObject = core::ptr::null_mut();
    v_res_5635_ = l_Lean_Lsp_instToJsonLeanImportKind_toJson(v_x_5634_);
    lean_dec_ref(v_x_5634_);
    return v_res_5635_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(
    mut v_j_5638_: *mut LeanObject,
    mut v_k_5639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut LeanObject = core::ptr::null_mut();
    v___x_5640_ = l_Lean_Json_getObjValD(v_j_5638_, v_k_5639_);
    v___x_5641_ = l_Lean_Lsp_instFromJsonLeanModule_fromJson(v___x_5640_);
    return v___x_5641_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0___boxed(
    mut v_j_5642_: *mut LeanObject,
    mut v_k_5643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5644_: *mut LeanObject = core::ptr::null_mut();
    v_res_5644_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(
            v_j_5642_, v_k_5643_,
        );
    lean_dec_ref(v_k_5643_);
    return v_res_5644_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__1(
    mut v_j_5645_: *mut LeanObject,
    mut v_k_5646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut LeanObject = core::ptr::null_mut();
    v___x_5647_ = l_Lean_Json_getObjValD(v_j_5645_, v_k_5646_);
    v___x_5648_ = l_Lean_Lsp_instFromJsonLeanImportKind_fromJson(v___x_5647_);
    return v___x_5648_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__1___boxed(
    mut v_j_5649_: *mut LeanObject,
    mut v_k_5650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5651_: *mut LeanObject = core::ptr::null_mut();
    v_res_5651_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__1(
            v_j_5649_, v_k_5650_,
        );
    lean_dec_ref(v_k_5650_);
    return v_res_5651_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3() -> *mut LeanObject {
    let mut v___x_5658_: u8 = 0;
    let mut v___x_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut LeanObject = core::ptr::null_mut();
    v___x_5658_ = 1;
    v___x_5659_ = l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__2;
    v___x_5660_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5659_, v___x_5658_);
    return v___x_5660_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4() -> *mut LeanObject {
    let mut v___x_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    v___x_5661_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6;
    v___x_5662_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3,
    );
    v___x_5663_ = lean_string_append(v___x_5662_, v___x_5661_);
    return v___x_5663_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6() -> *mut LeanObject {
    let mut v___x_5666_: u8 = 0;
    let mut v___x_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut LeanObject = core::ptr::null_mut();
    v___x_5666_ = 1;
    v___x_5667_ = l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__5;
    v___x_5668_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5667_, v___x_5666_);
    return v___x_5668_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7() -> *mut LeanObject {
    let mut v___x_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut LeanObject = core::ptr::null_mut();
    v___x_5669_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6,
    );
    v___x_5670_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4,
    );
    v___x_5671_ = lean_string_append(v___x_5670_, v___x_5669_);
    return v___x_5671_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8() -> *mut LeanObject {
    let mut v___x_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    v___x_5672_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_5673_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7_once),
        _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7,
    );
    v___x_5674_ = lean_string_append(v___x_5673_, v___x_5672_);
    return v___x_5674_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9() -> *mut LeanObject {
    let mut v___x_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut LeanObject = core::ptr::null_mut();
    v___x_5675_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11,
    );
    v___x_5676_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4,
    );
    v___x_5677_ = lean_string_append(v___x_5676_, v___x_5675_);
    return v___x_5677_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10() -> *mut LeanObject {
    let mut v___x_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut LeanObject = core::ptr::null_mut();
    v___x_5678_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_5679_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9_once),
        _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9,
    );
    v___x_5680_ = lean_string_append(v___x_5679_, v___x_5678_);
    return v___x_5680_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonLeanImport_fromJson(
    mut v_json_5681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5687_: u8 = 0;
    let mut v___x_5688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5693_: u8 = 0;
    let mut v_a_5694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5697_: u8 = 0;
    let mut v___x_5699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5701_: u8 = 0;
    let mut v_a_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5708_: u8 = 0;
    let mut v___x_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5714_: u8 = 0;
    let mut v_a_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5718_: u8 = 0;
    let mut v___x_5720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5722_: u8 = 0;
    let mut v_a_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5726_: u8 = 0;
    let mut v___x_5727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5731_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5682_ = l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0;
                lean_inc(v_json_5681_);
                v___x_5683_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(v_json_5681_, v___x_5682_);
                if lean_obj_tag(v___x_5683_) == 0 {
                    lean_dec(v_json_5681_);
                    v_a_5684_ = lean_ctor_get(v___x_5683_, 0);
                    v_isSharedCheck_5693_ = (!lean_is_exclusive(v___x_5683_)) as u8;
                    if v_isSharedCheck_5693_ == 0 {
                        v___x_5686_ = v___x_5683_;
                        v_isShared_5687_ = v_isSharedCheck_5693_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5684_);
                        lean_dec(v___x_5683_);
                        v___x_5686_ = lean_box(0);
                        v_isShared_5687_ = v_isSharedCheck_5693_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_5683_) == 0 {
                        lean_dec(v_json_5681_);
                        v_a_5694_ = lean_ctor_get(v___x_5683_, 0);
                        v_isSharedCheck_5701_ = (!lean_is_exclusive(v___x_5683_)) as u8;
                        if v_isSharedCheck_5701_ == 0 {
                            v___x_5696_ = v___x_5683_;
                            v_isShared_5697_ = v_isSharedCheck_5701_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5694_);
                            lean_dec(v___x_5683_);
                            v___x_5696_ = lean_box(0);
                            v_isShared_5697_ = v_isSharedCheck_5701_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5702_ = lean_ctor_get(v___x_5683_, 0);
                        lean_inc(v_a_5702_);
                        lean_dec_ref_known(v___x_5683_, 1);
                        v___x_5703_ = l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9;
                        v___x_5704_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__1(v_json_5681_, v___x_5703_);
                        if lean_obj_tag(v___x_5704_) == 0 {
                            lean_dec(v_a_5702_);
                            v_a_5705_ = lean_ctor_get(v___x_5704_, 0);
                            v_isSharedCheck_5714_ = (!lean_is_exclusive(v___x_5704_)) as u8;
                            if v_isSharedCheck_5714_ == 0 {
                                v___x_5707_ = v___x_5704_;
                                v_isShared_5708_ = v_isSharedCheck_5714_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_5705_);
                                lean_dec(v___x_5704_);
                                v___x_5707_ = lean_box(0);
                                v_isShared_5708_ = v_isSharedCheck_5714_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_5704_) == 0 {
                                lean_dec(v_a_5702_);
                                v_a_5715_ = lean_ctor_get(v___x_5704_, 0);
                                v_isSharedCheck_5722_ = (!lean_is_exclusive(v___x_5704_)) as u8;
                                if v_isSharedCheck_5722_ == 0 {
                                    v___x_5717_ = v___x_5704_;
                                    v_isShared_5718_ = v_isSharedCheck_5722_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_5715_);
                                    lean_dec(v___x_5704_);
                                    v___x_5717_ = lean_box(0);
                                    v_isShared_5718_ = v_isSharedCheck_5722_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_5723_ = lean_ctor_get(v___x_5704_, 0);
                                v_isSharedCheck_5731_ = (!lean_is_exclusive(v___x_5704_)) as u8;
                                if v_isSharedCheck_5731_ == 0 {
                                    v___x_5725_ = v___x_5704_;
                                    v_isShared_5726_ = v_isSharedCheck_5731_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_5723_);
                                    lean_dec(v___x_5704_);
                                    v___x_5725_ = lean_box(0);
                                    v_isShared_5726_ = v_isSharedCheck_5731_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5688_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8,
                );
                v___x_5689_ = lean_string_append(v___x_5688_, v_a_5684_);
                lean_dec(v_a_5684_);
                if v_isShared_5687_ == 0 {
                    lean_ctor_set(v___x_5686_, 0, v___x_5689_);
                    v___x_5691_ = v___x_5686_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5692_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5692_, 0, v___x_5689_);
                    v___x_5691_ = v_reuseFailAlloc_5692_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5691_;
            }
            3 => {
                if v_isShared_5697_ == 0 {
                    lean_ctor_set_tag(v___x_5696_, 0);
                    v___x_5699_ = v___x_5696_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5700_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5700_, 0, v_a_5694_);
                    v___x_5699_ = v_reuseFailAlloc_5700_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5699_;
            }
            5 => {
                v___x_5709_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10,
                );
                v___x_5710_ = lean_string_append(v___x_5709_, v_a_5705_);
                lean_dec(v_a_5705_);
                if v_isShared_5708_ == 0 {
                    lean_ctor_set(v___x_5707_, 0, v___x_5710_);
                    v___x_5712_ = v___x_5707_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5713_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5713_, 0, v___x_5710_);
                    v___x_5712_ = v_reuseFailAlloc_5713_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5712_;
            }
            7 => {
                if v_isShared_5718_ == 0 {
                    lean_ctor_set_tag(v___x_5717_, 0);
                    v___x_5720_ = v___x_5717_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5721_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5721_, 0, v_a_5715_);
                    v___x_5720_ = v_reuseFailAlloc_5721_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5720_;
            }
            9 => {
                v___x_5727_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5727_, 0, v_a_5702_);
                lean_ctor_set(v___x_5727_, 1, v_a_5723_);
                if v_isShared_5726_ == 0 {
                    lean_ctor_set(v___x_5725_, 0, v___x_5727_);
                    v___x_5729_ = v___x_5725_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5730_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5730_, 0, v___x_5727_);
                    v___x_5729_ = v_reuseFailAlloc_5730_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5729_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonLeanImport_toJson(
    mut v_x_5734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_module_5735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5739_: u8 = 0;
    let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5756_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_module_5735_ = lean_ctor_get(v_x_5734_, 0);
                v_kind_5736_ = lean_ctor_get(v_x_5734_, 1);
                v_isSharedCheck_5756_ = (!lean_is_exclusive(v_x_5734_)) as u8;
                if v_isSharedCheck_5756_ == 0 {
                    v___x_5738_ = v_x_5734_;
                    v_isShared_5739_ = v_isSharedCheck_5756_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_kind_5736_);
                    lean_inc(v_module_5735_);
                    lean_dec(v_x_5734_);
                    v___x_5738_ = lean_box(0);
                    v_isShared_5739_ = v_isSharedCheck_5756_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5740_ = l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0;
                v___x_5741_ = l_Lean_Lsp_instToJsonLeanModule_toJson(v_module_5735_);
                lean_dec_ref(v_module_5735_);
                if v_isShared_5739_ == 0 {
                    lean_ctor_set(v___x_5738_, 1, v___x_5741_);
                    lean_ctor_set(v___x_5738_, 0, v___x_5740_);
                    v___x_5743_ = v___x_5738_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5755_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5755_, 0, v___x_5740_);
                    lean_ctor_set(v_reuseFailAlloc_5755_, 1, v___x_5741_);
                    v___x_5743_ = v_reuseFailAlloc_5755_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5744_ = lean_box(0);
                v___x_5745_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5745_, 0, v___x_5743_);
                lean_ctor_set(v___x_5745_, 1, v___x_5744_);
                v___x_5746_ =
                    l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9;
                v___x_5747_ = l_Lean_Lsp_instToJsonLeanImportKind_toJson(v_kind_5736_);
                lean_dec_ref(v_kind_5736_);
                v___x_5748_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5748_, 0, v___x_5746_);
                lean_ctor_set(v___x_5748_, 1, v___x_5747_);
                v___x_5749_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5749_, 0, v___x_5748_);
                lean_ctor_set(v___x_5749_, 1, v___x_5744_);
                v___x_5750_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5750_, 0, v___x_5749_);
                lean_ctor_set(v___x_5750_, 1, v___x_5744_);
                v___x_5751_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_5751_, 0, v___x_5745_);
                lean_ctor_set(v___x_5751_, 1, v___x_5750_);
                v___x_5752_ = l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0;
                v___x_5753_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_5751_, v___x_5752_);
                v___x_5754_ = l_Lean_Json_mkObj(v___x_5753_);
                lean_dec(v___x_5753_);
                return v___x_5754_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2()
-> *mut LeanObject {
    let mut v___x_5764_: u8 = 0;
    let mut v___x_5765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut LeanObject = core::ptr::null_mut();
    v___x_5764_ = 1;
    v___x_5765_ = l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__1;
    v___x_5766_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5765_, v___x_5764_);
    return v___x_5766_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3()
-> *mut LeanObject {
    let mut v___x_5767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut LeanObject = core::ptr::null_mut();
    v___x_5767_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6;
    v___x_5768_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2,
    );
    v___x_5769_ = lean_string_append(v___x_5768_, v___x_5767_);
    return v___x_5769_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4()
-> *mut LeanObject {
    let mut v___x_5770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: *mut LeanObject = core::ptr::null_mut();
    v___x_5770_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6,
    );
    v___x_5771_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3,
    );
    v___x_5772_ = lean_string_append(v___x_5771_, v___x_5770_);
    return v___x_5772_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5()
-> *mut LeanObject {
    let mut v___x_5773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: *mut LeanObject = core::ptr::null_mut();
    v___x_5773_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_5774_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4,
    );
    v___x_5775_ = lean_string_append(v___x_5774_, v___x_5773_);
    return v___x_5775_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson(
    mut v_json_5776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5782_: u8 = 0;
    let mut v___x_5783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5788_: u8 = 0;
    let mut v_a_5789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5792_: u8 = 0;
    let mut v___x_5794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5796_: u8 = 0;
    let mut v_a_5797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5800_: u8 = 0;
    let mut v___x_5802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5804_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5777_ = l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0;
                v___x_5778_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(v_json_5776_, v___x_5777_);
                if lean_obj_tag(v___x_5778_) == 0 {
                    v_a_5779_ = lean_ctor_get(v___x_5778_, 0);
                    v_isSharedCheck_5788_ = (!lean_is_exclusive(v___x_5778_)) as u8;
                    if v_isSharedCheck_5788_ == 0 {
                        v___x_5781_ = v___x_5778_;
                        v_isShared_5782_ = v_isSharedCheck_5788_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5779_);
                        lean_dec(v___x_5778_);
                        v___x_5781_ = lean_box(0);
                        v_isShared_5782_ = v_isSharedCheck_5788_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_5778_) == 0 {
                        v_a_5789_ = lean_ctor_get(v___x_5778_, 0);
                        v_isSharedCheck_5796_ = (!lean_is_exclusive(v___x_5778_)) as u8;
                        if v_isSharedCheck_5796_ == 0 {
                            v___x_5791_ = v___x_5778_;
                            v_isShared_5792_ = v_isSharedCheck_5796_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5789_);
                            lean_dec(v___x_5778_);
                            v___x_5791_ = lean_box(0);
                            v_isShared_5792_ = v_isSharedCheck_5796_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5797_ = lean_ctor_get(v___x_5778_, 0);
                        v_isSharedCheck_5804_ = (!lean_is_exclusive(v___x_5778_)) as u8;
                        if v_isSharedCheck_5804_ == 0 {
                            v___x_5799_ = v___x_5778_;
                            v_isShared_5800_ = v_isSharedCheck_5804_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_5797_);
                            lean_dec(v___x_5778_);
                            v___x_5799_ = lean_box(0);
                            v_isShared_5800_ = v_isSharedCheck_5804_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5783_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5_once), _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5);
                v___x_5784_ = lean_string_append(v___x_5783_, v_a_5779_);
                lean_dec(v_a_5779_);
                if v_isShared_5782_ == 0 {
                    lean_ctor_set(v___x_5781_, 0, v___x_5784_);
                    v___x_5786_ = v___x_5781_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5787_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5787_, 0, v___x_5784_);
                    v___x_5786_ = v_reuseFailAlloc_5787_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5786_;
            }
            3 => {
                if v_isShared_5792_ == 0 {
                    lean_ctor_set_tag(v___x_5791_, 0);
                    v___x_5794_ = v___x_5791_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5795_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5795_, 0, v_a_5789_);
                    v___x_5794_ = v_reuseFailAlloc_5795_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5794_;
            }
            5 => {
                if v_isShared_5800_ == 0 {
                    v___x_5802_ = v___x_5799_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5803_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5803_, 0, v_a_5797_);
                    v___x_5802_ = v_reuseFailAlloc_5803_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5802_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson(
    mut v_x_5807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut LeanObject = core::ptr::null_mut();
    v___x_5808_ = l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0;
    v___x_5809_ = l_Lean_Lsp_instToJsonLeanModule_toJson(v_x_5807_);
    v___x_5810_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5810_, 0, v___x_5808_);
    lean_ctor_set(v___x_5810_, 1, v___x_5809_);
    v___x_5811_ = lean_box(0);
    v___x_5812_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5812_, 0, v___x_5810_);
    lean_ctor_set(v___x_5812_, 1, v___x_5811_);
    v___x_5813_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5813_, 0, v___x_5812_);
    lean_ctor_set(v___x_5813_, 1, v___x_5811_);
    v___x_5814_ = l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0;
    v___x_5815_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_5813_, v___x_5814_);
    v___x_5816_ = l_Lean_Json_mkObj(v___x_5815_);
    lean_dec(v___x_5815_);
    return v___x_5816_;
}
pub unsafe fn l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson___boxed(
    mut v_x_5817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5818_: *mut LeanObject = core::ptr::null_mut();
    v_res_5818_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson(v_x_5817_);
    lean_dec_ref(v_x_5817_);
    return v_res_5818_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2()
-> *mut LeanObject {
    let mut v___x_5826_: u8 = 0;
    let mut v___x_5827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut LeanObject = core::ptr::null_mut();
    v___x_5826_ = 1;
    v___x_5827_ = l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__1;
    v___x_5828_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5827_, v___x_5826_);
    return v___x_5828_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3()
-> *mut LeanObject {
    let mut v___x_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut LeanObject = core::ptr::null_mut();
    v___x_5829_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6;
    v___x_5830_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2,
    );
    v___x_5831_ = lean_string_append(v___x_5830_, v___x_5829_);
    return v___x_5831_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4()
-> *mut LeanObject {
    let mut v___x_5832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut LeanObject = core::ptr::null_mut();
    v___x_5832_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6,
    );
    v___x_5833_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3,
    );
    v___x_5834_ = lean_string_append(v___x_5833_, v___x_5832_);
    return v___x_5834_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5()
-> *mut LeanObject {
    let mut v___x_5835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut LeanObject = core::ptr::null_mut();
    v___x_5835_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_5836_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4,
    );
    v___x_5837_ = lean_string_append(v___x_5836_, v___x_5835_);
    return v___x_5837_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson(
    mut v_json_5838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5844_: u8 = 0;
    let mut v___x_5845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5850_: u8 = 0;
    let mut v_a_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5854_: u8 = 0;
    let mut v___x_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5858_: u8 = 0;
    let mut v_a_5859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5862_: u8 = 0;
    let mut v___x_5864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5866_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5839_ = l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0;
                v___x_5840_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(v_json_5838_, v___x_5839_);
                if lean_obj_tag(v___x_5840_) == 0 {
                    v_a_5841_ = lean_ctor_get(v___x_5840_, 0);
                    v_isSharedCheck_5850_ = (!lean_is_exclusive(v___x_5840_)) as u8;
                    if v_isSharedCheck_5850_ == 0 {
                        v___x_5843_ = v___x_5840_;
                        v_isShared_5844_ = v_isSharedCheck_5850_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5841_);
                        lean_dec(v___x_5840_);
                        v___x_5843_ = lean_box(0);
                        v_isShared_5844_ = v_isSharedCheck_5850_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_5840_) == 0 {
                        v_a_5851_ = lean_ctor_get(v___x_5840_, 0);
                        v_isSharedCheck_5858_ = (!lean_is_exclusive(v___x_5840_)) as u8;
                        if v_isSharedCheck_5858_ == 0 {
                            v___x_5853_ = v___x_5840_;
                            v_isShared_5854_ = v_isSharedCheck_5858_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5851_);
                            lean_dec(v___x_5840_);
                            v___x_5853_ = lean_box(0);
                            v_isShared_5854_ = v_isSharedCheck_5858_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5859_ = lean_ctor_get(v___x_5840_, 0);
                        v_isSharedCheck_5866_ = (!lean_is_exclusive(v___x_5840_)) as u8;
                        if v_isSharedCheck_5866_ == 0 {
                            v___x_5861_ = v___x_5840_;
                            v_isShared_5862_ = v_isSharedCheck_5866_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_5859_);
                            lean_dec(v___x_5840_);
                            v___x_5861_ = lean_box(0);
                            v_isShared_5862_ = v_isSharedCheck_5866_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5845_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5_once), _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5);
                v___x_5846_ = lean_string_append(v___x_5845_, v_a_5841_);
                lean_dec(v_a_5841_);
                if v_isShared_5844_ == 0 {
                    lean_ctor_set(v___x_5843_, 0, v___x_5846_);
                    v___x_5848_ = v___x_5843_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5849_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5849_, 0, v___x_5846_);
                    v___x_5848_ = v_reuseFailAlloc_5849_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5848_;
            }
            3 => {
                if v_isShared_5854_ == 0 {
                    lean_ctor_set_tag(v___x_5853_, 0);
                    v___x_5856_ = v___x_5853_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5857_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5857_, 0, v_a_5851_);
                    v___x_5856_ = v_reuseFailAlloc_5857_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5856_;
            }
            5 => {
                if v_isShared_5862_ == 0 {
                    v___x_5864_ = v___x_5861_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5865_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5865_, 0, v_a_5859_);
                    v___x_5864_ = v_reuseFailAlloc_5865_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5864_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson(
    mut v_x_5869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut LeanObject = core::ptr::null_mut();
    v___x_5870_ = l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0;
    v___x_5871_ = l_Lean_Lsp_instToJsonLeanModule_toJson(v_x_5869_);
    v___x_5872_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5872_, 0, v___x_5870_);
    lean_ctor_set(v___x_5872_, 1, v___x_5871_);
    v___x_5873_ = lean_box(0);
    v___x_5874_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5874_, 0, v___x_5872_);
    lean_ctor_set(v___x_5874_, 1, v___x_5873_);
    v___x_5875_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5875_, 0, v___x_5874_);
    lean_ctor_set(v___x_5875_, 1, v___x_5873_);
    v___x_5876_ = l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0;
    v___x_5877_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_5875_, v___x_5876_);
    v___x_5878_ = l_Lean_Json_mkObj(v___x_5877_);
    lean_dec(v___x_5877_);
    return v___x_5878_;
}
pub unsafe fn l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson___boxed(
    mut v_x_5879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5880_: *mut LeanObject = core::ptr::null_mut();
    v_res_5880_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson(v_x_5879_);
    lean_dec_ref(v_x_5879_);
    return v_res_5880_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2() -> *mut LeanObject
{
    let mut v___x_5888_: u8 = 0;
    let mut v___x_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    v___x_5888_ = 1;
    v___x_5889_ = l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__1;
    v___x_5890_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5889_, v___x_5888_);
    return v___x_5890_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3() -> *mut LeanObject
{
    let mut v___x_5891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut LeanObject = core::ptr::null_mut();
    v___x_5891_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6;
    v___x_5892_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2_once),
        _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2,
    );
    v___x_5893_ = lean_string_append(v___x_5892_, v___x_5891_);
    return v___x_5893_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4() -> *mut LeanObject
{
    let mut v___x_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: *mut LeanObject = core::ptr::null_mut();
    v___x_5894_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6,
    );
    v___x_5895_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3,
    );
    v___x_5896_ = lean_string_append(v___x_5895_, v___x_5894_);
    return v___x_5896_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5() -> *mut LeanObject
{
    let mut v___x_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut LeanObject = core::ptr::null_mut();
    v___x_5897_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_5898_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4,
    );
    v___x_5899_ = lean_string_append(v___x_5898_, v___x_5897_);
    return v___x_5899_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson(
    mut v_json_5900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5906_: u8 = 0;
    let mut v___x_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5912_: u8 = 0;
    let mut v_a_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5916_: u8 = 0;
    let mut v___x_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5920_: u8 = 0;
    let mut v_a_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5924_: u8 = 0;
    let mut v___x_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5928_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5901_ = l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0;
                v___x_5902_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_5900_, v___x_5901_);
                if lean_obj_tag(v___x_5902_) == 0 {
                    v_a_5903_ = lean_ctor_get(v___x_5902_, 0);
                    v_isSharedCheck_5912_ = (!lean_is_exclusive(v___x_5902_)) as u8;
                    if v_isSharedCheck_5912_ == 0 {
                        v___x_5905_ = v___x_5902_;
                        v_isShared_5906_ = v_isSharedCheck_5912_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5903_);
                        lean_dec(v___x_5902_);
                        v___x_5905_ = lean_box(0);
                        v_isShared_5906_ = v_isSharedCheck_5912_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_5902_) == 0 {
                        v_a_5913_ = lean_ctor_get(v___x_5902_, 0);
                        v_isSharedCheck_5920_ = (!lean_is_exclusive(v___x_5902_)) as u8;
                        if v_isSharedCheck_5920_ == 0 {
                            v___x_5915_ = v___x_5902_;
                            v_isShared_5916_ = v_isSharedCheck_5920_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5913_);
                            lean_dec(v___x_5902_);
                            v___x_5915_ = lean_box(0);
                            v_isShared_5916_ = v_isSharedCheck_5920_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5921_ = lean_ctor_get(v___x_5902_, 0);
                        v_isSharedCheck_5928_ = (!lean_is_exclusive(v___x_5902_)) as u8;
                        if v_isSharedCheck_5928_ == 0 {
                            v___x_5923_ = v___x_5902_;
                            v_isShared_5924_ = v_isSharedCheck_5928_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_5921_);
                            lean_dec(v___x_5902_);
                            v___x_5923_ = lean_box(0);
                            v_isShared_5924_ = v_isSharedCheck_5928_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5907_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5,
                );
                v___x_5908_ = lean_string_append(v___x_5907_, v_a_5903_);
                lean_dec(v_a_5903_);
                if v_isShared_5906_ == 0 {
                    lean_ctor_set(v___x_5905_, 0, v___x_5908_);
                    v___x_5910_ = v___x_5905_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5911_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5911_, 0, v___x_5908_);
                    v___x_5910_ = v_reuseFailAlloc_5911_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5910_;
            }
            3 => {
                if v_isShared_5916_ == 0 {
                    lean_ctor_set_tag(v___x_5915_, 0);
                    v___x_5918_ = v___x_5915_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5919_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5919_, 0, v_a_5913_);
                    v___x_5918_ = v_reuseFailAlloc_5919_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5918_;
            }
            5 => {
                if v_isShared_5924_ == 0 {
                    v___x_5926_ = v___x_5923_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5927_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5927_, 0, v_a_5921_);
                    v___x_5926_ = v_reuseFailAlloc_5927_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5926_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonRpcConnectParams_toJson(
    mut v_x_5931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut LeanObject = core::ptr::null_mut();
    v___x_5932_ = l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0;
    v___x_5933_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_5933_, 0, v_x_5931_);
    v___x_5934_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5934_, 0, v___x_5932_);
    lean_ctor_set(v___x_5934_, 1, v___x_5933_);
    v___x_5935_ = lean_box(0);
    v___x_5936_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5936_, 0, v___x_5934_);
    lean_ctor_set(v___x_5936_, 1, v___x_5935_);
    v___x_5937_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5937_, 0, v___x_5936_);
    lean_ctor_set(v___x_5937_, 1, v___x_5935_);
    v___x_5938_ = l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0;
    v___x_5939_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_5937_, v___x_5938_);
    v___x_5940_ = l_Lean_Json_mkObj(v___x_5939_);
    lean_dec(v___x_5939_);
    return v___x_5940_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(
    mut v_j_5943_: *mut LeanObject,
    mut v_k_5944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut LeanObject = core::ptr::null_mut();
    v___x_5945_ = l_Lean_Json_getObjValD(v_j_5943_, v_k_5944_);
    v___x_5946_ = l_UInt64_fromJson_x3f(v___x_5945_);
    return v___x_5946_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0___boxed(
    mut v_j_5947_: *mut LeanObject,
    mut v_k_5948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5949_: *mut LeanObject = core::ptr::null_mut();
    v_res_5949_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(
            v_j_5947_, v_k_5948_,
        );
    lean_dec_ref(v_k_5948_);
    return v_res_5949_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3() -> *mut LeanObject {
    let mut v___x_5956_: u8 = 0;
    let mut v___x_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut LeanObject = core::ptr::null_mut();
    v___x_5956_ = 1;
    v___x_5957_ = l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__2;
    v___x_5958_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5957_, v___x_5956_);
    return v___x_5958_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4() -> *mut LeanObject {
    let mut v___x_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut LeanObject = core::ptr::null_mut();
    v___x_5959_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6;
    v___x_5960_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3,
    );
    v___x_5961_ = lean_string_append(v___x_5960_, v___x_5959_);
    return v___x_5961_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6() -> *mut LeanObject {
    let mut v___x_5964_: u8 = 0;
    let mut v___x_5965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut LeanObject = core::ptr::null_mut();
    v___x_5964_ = 1;
    v___x_5965_ = l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__5;
    v___x_5966_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5965_, v___x_5964_);
    return v___x_5966_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7() -> *mut LeanObject {
    let mut v___x_5967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: *mut LeanObject = core::ptr::null_mut();
    v___x_5967_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6,
    );
    v___x_5968_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4,
    );
    v___x_5969_ = lean_string_append(v___x_5968_, v___x_5967_);
    return v___x_5969_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8() -> *mut LeanObject {
    let mut v___x_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut LeanObject = core::ptr::null_mut();
    v___x_5970_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_5971_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7_once),
        _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7,
    );
    v___x_5972_ = lean_string_append(v___x_5971_, v___x_5970_);
    return v___x_5972_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonRpcConnected_fromJson(
    mut v_json_5973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5979_: u8 = 0;
    let mut v___x_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5985_: u8 = 0;
    let mut v_a_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5989_: u8 = 0;
    let mut v___x_5991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5993_: u8 = 0;
    let mut v_a_5994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5997_: u8 = 0;
    let mut v___x_5999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6001_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5974_ = l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0;
                v___x_5975_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_json_5973_, v___x_5974_);
                if lean_obj_tag(v___x_5975_) == 0 {
                    v_a_5976_ = lean_ctor_get(v___x_5975_, 0);
                    v_isSharedCheck_5985_ = (!lean_is_exclusive(v___x_5975_)) as u8;
                    if v_isSharedCheck_5985_ == 0 {
                        v___x_5978_ = v___x_5975_;
                        v_isShared_5979_ = v_isSharedCheck_5985_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5976_);
                        lean_dec(v___x_5975_);
                        v___x_5978_ = lean_box(0);
                        v_isShared_5979_ = v_isSharedCheck_5985_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_5975_) == 0 {
                        v_a_5986_ = lean_ctor_get(v___x_5975_, 0);
                        v_isSharedCheck_5993_ = (!lean_is_exclusive(v___x_5975_)) as u8;
                        if v_isSharedCheck_5993_ == 0 {
                            v___x_5988_ = v___x_5975_;
                            v_isShared_5989_ = v_isSharedCheck_5993_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5986_);
                            lean_dec(v___x_5975_);
                            v___x_5988_ = lean_box(0);
                            v_isShared_5989_ = v_isSharedCheck_5993_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5994_ = lean_ctor_get(v___x_5975_, 0);
                        v_isSharedCheck_6001_ = (!lean_is_exclusive(v___x_5975_)) as u8;
                        if v_isSharedCheck_6001_ == 0 {
                            v___x_5996_ = v___x_5975_;
                            v_isShared_5997_ = v_isSharedCheck_6001_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_5994_);
                            lean_dec(v___x_5975_);
                            v___x_5996_ = lean_box(0);
                            v_isShared_5997_ = v_isSharedCheck_6001_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5980_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8,
                );
                v___x_5981_ = lean_string_append(v___x_5980_, v_a_5976_);
                lean_dec(v_a_5976_);
                if v_isShared_5979_ == 0 {
                    lean_ctor_set(v___x_5978_, 0, v___x_5981_);
                    v___x_5983_ = v___x_5978_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5984_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5984_, 0, v___x_5981_);
                    v___x_5983_ = v_reuseFailAlloc_5984_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5983_;
            }
            3 => {
                if v_isShared_5989_ == 0 {
                    lean_ctor_set_tag(v___x_5988_, 0);
                    v___x_5991_ = v___x_5988_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5992_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5992_, 0, v_a_5986_);
                    v___x_5991_ = v_reuseFailAlloc_5992_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5991_;
            }
            5 => {
                if v_isShared_5997_ == 0 {
                    v___x_5999_ = v___x_5996_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6000_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6000_, 0, v_a_5994_);
                    v___x_5999_ = v_reuseFailAlloc_6000_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5999_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonRpcConnected_toJson(mut v_x_6004_: u64) -> *mut LeanObject {
    let mut v___x_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: *mut LeanObject = core::ptr::null_mut();
    v___x_6005_ = l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0;
    v___x_6006_ = lean_uint64_to_nat(v_x_6004_);
    v___x_6007_ = l_Lean_bignumToJson(v___x_6006_);
    v___x_6008_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6008_, 0, v___x_6005_);
    lean_ctor_set(v___x_6008_, 1, v___x_6007_);
    v___x_6009_ = lean_box(0);
    v___x_6010_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6010_, 0, v___x_6008_);
    lean_ctor_set(v___x_6010_, 1, v___x_6009_);
    v___x_6011_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6011_, 0, v___x_6010_);
    lean_ctor_set(v___x_6011_, 1, v___x_6009_);
    v___x_6012_ = l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0;
    v___x_6013_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_6011_, v___x_6012_);
    v___x_6014_ = l_Lean_Json_mkObj(v___x_6013_);
    lean_dec(v___x_6013_);
    return v___x_6014_;
}
pub unsafe fn l_Lean_Lsp_instToJsonRpcConnected_toJson___boxed(
    mut v_x_6015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_30__boxed_6016_: u64 = 0;
    let mut v_res_6017_: *mut LeanObject = core::ptr::null_mut();
    v_x_30__boxed_6016_ = lean_unbox_uint64(v_x_6015_);
    lean_dec_ref(v_x_6015_);
    v_res_6017_ = l_Lean_Lsp_instToJsonRpcConnected_toJson(v_x_30__boxed_6016_);
    return v_res_6017_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__0(
    mut v_j_6020_: *mut LeanObject,
    mut v_k_6021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut LeanObject = core::ptr::null_mut();
    v___x_6022_ = l_Lean_Json_getObjValD(v_j_6020_, v_k_6021_);
    v___x_6023_ = l_Lean_Name_fromJson_x3f(v___x_6022_);
    return v___x_6023_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__0___boxed(
    mut v_j_6024_: *mut LeanObject,
    mut v_k_6025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6026_: *mut LeanObject = core::ptr::null_mut();
    v_res_6026_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__0(
            v_j_6024_, v_k_6025_,
        );
    lean_dec_ref(v_k_6025_);
    return v_res_6026_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__1(
    mut v_j_6027_: *mut LeanObject,
    mut v_k_6028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut LeanObject = core::ptr::null_mut();
    v___x_6029_ = l_Lean_Json_getObjValD(v_j_6027_, v_k_6028_);
    v___x_6030_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6030_, 0, v___x_6029_);
    return v___x_6030_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__1___boxed(
    mut v_j_6031_: *mut LeanObject,
    mut v_k_6032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6033_: *mut LeanObject = core::ptr::null_mut();
    v_res_6033_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__1(
            v_j_6031_, v_k_6032_,
        );
    lean_dec_ref(v_k_6032_);
    return v_res_6033_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2() -> *mut LeanObject {
    let mut v___x_6039_: u8 = 0;
    let mut v___x_6040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut LeanObject = core::ptr::null_mut();
    v___x_6039_ = 1;
    v___x_6040_ = l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__1;
    v___x_6041_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_6040_, v___x_6039_);
    return v___x_6041_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3() -> *mut LeanObject {
    let mut v___x_6042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut LeanObject = core::ptr::null_mut();
    v___x_6042_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6;
    v___x_6043_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2_once),
        _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2,
    );
    v___x_6044_ = lean_string_append(v___x_6043_, v___x_6042_);
    return v___x_6044_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4() -> *mut LeanObject {
    let mut v___x_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
    v___x_6045_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once
        ),
        _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9,
    );
    v___x_6046_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3,
    );
    v___x_6047_ = lean_string_append(v___x_6046_, v___x_6045_);
    return v___x_6047_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5() -> *mut LeanObject {
    let mut v___x_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
    v___x_6048_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_6049_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4,
    );
    v___x_6050_ = lean_string_append(v___x_6049_, v___x_6048_);
    return v___x_6050_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6() -> *mut LeanObject {
    let mut v___x_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut LeanObject = core::ptr::null_mut();
    v___x_6051_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8_once),
        _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8,
    );
    v___x_6052_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3,
    );
    v___x_6053_ = lean_string_append(v___x_6052_, v___x_6051_);
    return v___x_6053_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7() -> *mut LeanObject {
    let mut v___x_6054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut LeanObject = core::ptr::null_mut();
    v___x_6054_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_6055_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6,
    );
    v___x_6056_ = lean_string_append(v___x_6055_, v___x_6054_);
    return v___x_6056_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8() -> *mut LeanObject {
    let mut v___x_6057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut LeanObject = core::ptr::null_mut();
    v___x_6057_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6,
    );
    v___x_6058_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3,
    );
    v___x_6059_ = lean_string_append(v___x_6058_, v___x_6057_);
    return v___x_6059_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9() -> *mut LeanObject {
    let mut v___x_6060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut LeanObject = core::ptr::null_mut();
    v___x_6060_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_6061_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8_once),
        _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8,
    );
    v___x_6062_ = lean_string_append(v___x_6061_, v___x_6060_);
    return v___x_6062_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12() -> *mut LeanObject
{
    let mut v___x_6066_: u8 = 0;
    let mut v___x_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut LeanObject = core::ptr::null_mut();
    v___x_6066_ = 1;
    v___x_6067_ = l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__11;
    v___x_6068_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_6067_, v___x_6066_);
    return v___x_6068_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13() -> *mut LeanObject
{
    let mut v___x_6069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut LeanObject = core::ptr::null_mut();
    v___x_6069_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12_once),
        _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12,
    );
    v___x_6070_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3,
    );
    v___x_6071_ = lean_string_append(v___x_6070_, v___x_6069_);
    return v___x_6071_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14() -> *mut LeanObject
{
    let mut v___x_6072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6074_: *mut LeanObject = core::ptr::null_mut();
    v___x_6072_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_6073_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13_once),
        _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13,
    );
    v___x_6074_ = lean_string_append(v___x_6073_, v___x_6072_);
    return v___x_6074_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonRpcCallParams_fromJson(
    mut v_json_6076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6082_: u8 = 0;
    let mut v___x_6083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6088_: u8 = 0;
    let mut v_a_6089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6092_: u8 = 0;
    let mut v___x_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6096_: u8 = 0;
    let mut v_a_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6103_: u8 = 0;
    let mut v___x_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6109_: u8 = 0;
    let mut v_a_6110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6113_: u8 = 0;
    let mut v___x_6115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6117_: u8 = 0;
    let mut v_a_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6124_: u8 = 0;
    let mut v___x_6125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6130_: u8 = 0;
    let mut v_a_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6134_: u8 = 0;
    let mut v___x_6136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6138_: u8 = 0;
    let mut v_a_6139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6145_: u8 = 0;
    let mut v___x_6146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6151_: u8 = 0;
    let mut v_a_6152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6155_: u8 = 0;
    let mut v___x_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6159_: u8 = 0;
    let mut v_a_6160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6166_: u8 = 0;
    let mut v___x_6167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: u64 = 0;
    let mut v___x_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6173_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6077_ =
                    l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0;
                lean_inc(v_json_6076_);
                v___x_6078_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_json_6076_, v___x_6077_);
                if lean_obj_tag(v___x_6078_) == 0 {
                    lean_dec(v_json_6076_);
                    v_a_6079_ = lean_ctor_get(v___x_6078_, 0);
                    v_isSharedCheck_6088_ = (!lean_is_exclusive(v___x_6078_)) as u8;
                    if v_isSharedCheck_6088_ == 0 {
                        v___x_6081_ = v___x_6078_;
                        v_isShared_6082_ = v_isSharedCheck_6088_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6079_);
                        lean_dec(v___x_6078_);
                        v___x_6081_ = lean_box(0);
                        v_isShared_6082_ = v_isSharedCheck_6088_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_6078_) == 0 {
                        lean_dec(v_json_6076_);
                        v_a_6089_ = lean_ctor_get(v___x_6078_, 0);
                        v_isSharedCheck_6096_ = (!lean_is_exclusive(v___x_6078_)) as u8;
                        if v_isSharedCheck_6096_ == 0 {
                            v___x_6091_ = v___x_6078_;
                            v_isShared_6092_ = v_isSharedCheck_6096_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6089_);
                            lean_dec(v___x_6078_);
                            v___x_6091_ = lean_box(0);
                            v_isShared_6092_ = v_isSharedCheck_6096_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_6097_ = lean_ctor_get(v___x_6078_, 0);
                        lean_inc(v_a_6097_);
                        lean_dec_ref_known(v___x_6078_, 1);
                        v___x_6098_ = l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6;
                        lean_inc(v_json_6076_);
                        v___x_6099_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(v_json_6076_, v___x_6098_);
                        if lean_obj_tag(v___x_6099_) == 0 {
                            lean_dec(v_a_6097_);
                            lean_dec(v_json_6076_);
                            v_a_6100_ = lean_ctor_get(v___x_6099_, 0);
                            v_isSharedCheck_6109_ = (!lean_is_exclusive(v___x_6099_)) as u8;
                            if v_isSharedCheck_6109_ == 0 {
                                v___x_6102_ = v___x_6099_;
                                v_isShared_6103_ = v_isSharedCheck_6109_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_6100_);
                                lean_dec(v___x_6099_);
                                v___x_6102_ = lean_box(0);
                                v_isShared_6103_ = v_isSharedCheck_6109_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_6099_) == 0 {
                                lean_dec(v_a_6097_);
                                lean_dec(v_json_6076_);
                                v_a_6110_ = lean_ctor_get(v___x_6099_, 0);
                                v_isSharedCheck_6117_ = (!lean_is_exclusive(v___x_6099_)) as u8;
                                if v_isSharedCheck_6117_ == 0 {
                                    v___x_6112_ = v___x_6099_;
                                    v_isShared_6113_ = v_isSharedCheck_6117_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_6110_);
                                    lean_dec(v___x_6099_);
                                    v___x_6112_ = lean_box(0);
                                    v_isShared_6113_ = v_isSharedCheck_6117_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_6118_ = lean_ctor_get(v___x_6099_, 0);
                                lean_inc(v_a_6118_);
                                lean_dec_ref_known(v___x_6099_, 1);
                                v___x_6119_ =
                                    l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0;
                                lean_inc(v_json_6076_);
                                v___x_6120_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_json_6076_, v___x_6119_);
                                if lean_obj_tag(v___x_6120_) == 0 {
                                    lean_dec(v_a_6118_);
                                    lean_dec(v_a_6097_);
                                    lean_dec(v_json_6076_);
                                    v_a_6121_ = lean_ctor_get(v___x_6120_, 0);
                                    v_isSharedCheck_6130_ = (!lean_is_exclusive(v___x_6120_)) as u8;
                                    if v_isSharedCheck_6130_ == 0 {
                                        v___x_6123_ = v___x_6120_;
                                        v_isShared_6124_ = v_isSharedCheck_6130_;
                                        state = 9;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6121_);
                                        lean_dec(v___x_6120_);
                                        v___x_6123_ = lean_box(0);
                                        v_isShared_6124_ = v_isSharedCheck_6130_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if lean_obj_tag(v___x_6120_) == 0 {
                                        lean_dec(v_a_6118_);
                                        lean_dec(v_a_6097_);
                                        lean_dec(v_json_6076_);
                                        v_a_6131_ = lean_ctor_get(v___x_6120_, 0);
                                        v_isSharedCheck_6138_ =
                                            (!lean_is_exclusive(v___x_6120_)) as u8;
                                        if v_isSharedCheck_6138_ == 0 {
                                            v___x_6133_ = v___x_6120_;
                                            v_isShared_6134_ = v_isSharedCheck_6138_;
                                            state = 11;
                                            continue;
                                        } else {
                                            lean_inc(v_a_6131_);
                                            lean_dec(v___x_6120_);
                                            v___x_6133_ = lean_box(0);
                                            v_isShared_6134_ = v_isSharedCheck_6138_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_6139_ = lean_ctor_get(v___x_6120_, 0);
                                        lean_inc(v_a_6139_);
                                        lean_dec_ref_known(v___x_6120_, 1);
                                        v___x_6140_ = l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__10;
                                        lean_inc(v_json_6076_);
                                        v___x_6141_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__0(v_json_6076_, v___x_6140_);
                                        if lean_obj_tag(v___x_6141_) == 0 {
                                            lean_dec(v_a_6139_);
                                            lean_dec(v_a_6118_);
                                            lean_dec(v_a_6097_);
                                            lean_dec(v_json_6076_);
                                            v_a_6142_ = lean_ctor_get(v___x_6141_, 0);
                                            v_isSharedCheck_6151_ =
                                                (!lean_is_exclusive(v___x_6141_)) as u8;
                                            if v_isSharedCheck_6151_ == 0 {
                                                v___x_6144_ = v___x_6141_;
                                                v_isShared_6145_ = v_isSharedCheck_6151_;
                                                state = 13;
                                                continue;
                                            } else {
                                                lean_inc(v_a_6142_);
                                                lean_dec(v___x_6141_);
                                                v___x_6144_ = lean_box(0);
                                                v_isShared_6145_ = v_isSharedCheck_6151_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            if lean_obj_tag(v___x_6141_) == 0 {
                                                lean_dec(v_a_6139_);
                                                lean_dec(v_a_6118_);
                                                lean_dec(v_a_6097_);
                                                lean_dec(v_json_6076_);
                                                v_a_6152_ = lean_ctor_get(v___x_6141_, 0);
                                                v_isSharedCheck_6159_ =
                                                    (!lean_is_exclusive(v___x_6141_)) as u8;
                                                if v_isSharedCheck_6159_ == 0 {
                                                    v___x_6154_ = v___x_6141_;
                                                    v_isShared_6155_ = v_isSharedCheck_6159_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_6152_);
                                                    lean_dec(v___x_6141_);
                                                    v___x_6154_ = lean_box(0);
                                                    v_isShared_6155_ = v_isSharedCheck_6159_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_6160_ = lean_ctor_get(v___x_6141_, 0);
                                                lean_inc(v_a_6160_);
                                                lean_dec_ref_known(v___x_6141_, 1);
                                                v___x_6161_ = l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__15;
                                                v___x_6162_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__1(v_json_6076_, v___x_6161_);
                                                v_a_6163_ = lean_ctor_get(v___x_6162_, 0);
                                                v_isSharedCheck_6173_ =
                                                    (!lean_is_exclusive(v___x_6162_)) as u8;
                                                if v_isSharedCheck_6173_ == 0 {
                                                    v___x_6165_ = v___x_6162_;
                                                    v_isShared_6166_ = v_isSharedCheck_6173_;
                                                    state = 17;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_6163_);
                                                    lean_dec(v___x_6162_);
                                                    v___x_6165_ = lean_box(0);
                                                    v_isShared_6166_ = v_isSharedCheck_6173_;
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
                v___x_6083_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5,
                );
                v___x_6084_ = lean_string_append(v___x_6083_, v_a_6079_);
                lean_dec(v_a_6079_);
                if v_isShared_6082_ == 0 {
                    lean_ctor_set(v___x_6081_, 0, v___x_6084_);
                    v___x_6086_ = v___x_6081_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6087_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6087_, 0, v___x_6084_);
                    v___x_6086_ = v_reuseFailAlloc_6087_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6086_;
            }
            3 => {
                if v_isShared_6092_ == 0 {
                    lean_ctor_set_tag(v___x_6091_, 0);
                    v___x_6094_ = v___x_6091_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6095_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6095_, 0, v_a_6089_);
                    v___x_6094_ = v_reuseFailAlloc_6095_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6094_;
            }
            5 => {
                v___x_6104_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7,
                );
                v___x_6105_ = lean_string_append(v___x_6104_, v_a_6100_);
                lean_dec(v_a_6100_);
                if v_isShared_6103_ == 0 {
                    lean_ctor_set(v___x_6102_, 0, v___x_6105_);
                    v___x_6107_ = v___x_6102_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6108_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6108_, 0, v___x_6105_);
                    v___x_6107_ = v_reuseFailAlloc_6108_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6107_;
            }
            7 => {
                if v_isShared_6113_ == 0 {
                    lean_ctor_set_tag(v___x_6112_, 0);
                    v___x_6115_ = v___x_6112_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6116_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6116_, 0, v_a_6110_);
                    v___x_6115_ = v_reuseFailAlloc_6116_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6115_;
            }
            9 => {
                v___x_6125_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9,
                );
                v___x_6126_ = lean_string_append(v___x_6125_, v_a_6121_);
                lean_dec(v_a_6121_);
                if v_isShared_6124_ == 0 {
                    lean_ctor_set(v___x_6123_, 0, v___x_6126_);
                    v___x_6128_ = v___x_6123_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6129_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6129_, 0, v___x_6126_);
                    v___x_6128_ = v_reuseFailAlloc_6129_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6128_;
            }
            11 => {
                if v_isShared_6134_ == 0 {
                    lean_ctor_set_tag(v___x_6133_, 0);
                    v___x_6136_ = v___x_6133_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6137_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6137_, 0, v_a_6131_);
                    v___x_6136_ = v_reuseFailAlloc_6137_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6136_;
            }
            13 => {
                v___x_6146_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14,
                );
                v___x_6147_ = lean_string_append(v___x_6146_, v_a_6142_);
                lean_dec(v_a_6142_);
                if v_isShared_6145_ == 0 {
                    lean_ctor_set(v___x_6144_, 0, v___x_6147_);
                    v___x_6149_ = v___x_6144_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6150_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6150_, 0, v___x_6147_);
                    v___x_6149_ = v_reuseFailAlloc_6150_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6149_;
            }
            15 => {
                if v_isShared_6155_ == 0 {
                    lean_ctor_set_tag(v___x_6154_, 0);
                    v___x_6157_ = v___x_6154_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6158_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6158_, 0, v_a_6152_);
                    v___x_6157_ = v_reuseFailAlloc_6158_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_6157_;
            }
            17 => {
                v___x_6167_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6167_, 0, v_a_6097_);
                lean_ctor_set(v___x_6167_, 1, v_a_6118_);
                v___x_6168_ = lean_alloc_ctor(0, 3, (8) as u32);
                lean_ctor_set(v___x_6168_, 0, v___x_6167_);
                lean_ctor_set(v___x_6168_, 1, v_a_6160_);
                lean_ctor_set(v___x_6168_, 2, v_a_6163_);
                v___x_6169_ = lean_unbox_uint64(v_a_6139_);
                lean_dec(v_a_6139_);
                lean_ctor_set_uint64(
                    v___x_6168_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_6169_,
                );
                if v_isShared_6166_ == 0 {
                    lean_ctor_set(v___x_6165_, 0, v___x_6168_);
                    v___x_6171_ = v___x_6165_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6172_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6172_, 0, v___x_6168_);
                    v___x_6171_ = v_reuseFailAlloc_6172_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_6171_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonRpcCallParams_toJson(
    mut v_x_6176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toTextDocumentPositionParams_6177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sessionId_6178_: u64 = 0;
    let mut v_method_6179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_6180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_textDocument_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_position_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6185_: u8 = 0;
    let mut v___x_6186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6202_: u8 = 0;
    let mut v___x_6203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6219_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toTextDocumentPositionParams_6177_ = lean_ctor_get(v_x_6176_, 0);
                lean_inc_ref(v_toTextDocumentPositionParams_6177_);
                v_sessionId_6178_ = lean_ctor_get_uint64(
                    v_x_6176_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_method_6179_ = lean_ctor_get(v_x_6176_, 1);
                lean_inc(v_method_6179_);
                v_params_6180_ = lean_ctor_get(v_x_6176_, 2);
                lean_inc(v_params_6180_);
                lean_dec_ref(v_x_6176_);
                v_textDocument_6181_ = lean_ctor_get(v_toTextDocumentPositionParams_6177_, 0);
                v_position_6182_ = lean_ctor_get(v_toTextDocumentPositionParams_6177_, 1);
                v_isSharedCheck_6219_ =
                    (!lean_is_exclusive(v_toTextDocumentPositionParams_6177_)) as u8;
                if v_isSharedCheck_6219_ == 0 {
                    v___x_6184_ = v_toTextDocumentPositionParams_6177_;
                    v_isShared_6185_ = v_isSharedCheck_6219_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_position_6182_);
                    lean_inc(v_textDocument_6181_);
                    lean_dec(v_toTextDocumentPositionParams_6177_);
                    v___x_6184_ = lean_box(0);
                    v_isShared_6185_ = v_isSharedCheck_6219_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6186_ =
                    l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0;
                v___x_6187_ =
                    l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_6181_);
                if v_isShared_6185_ == 0 {
                    lean_ctor_set(v___x_6184_, 1, v___x_6187_);
                    lean_ctor_set(v___x_6184_, 0, v___x_6186_);
                    v___x_6189_ = v___x_6184_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6218_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6218_, 0, v___x_6186_);
                    lean_ctor_set(v_reuseFailAlloc_6218_, 1, v___x_6187_);
                    v___x_6189_ = v_reuseFailAlloc_6218_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6190_ = lean_box(0);
                v___x_6191_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6191_, 0, v___x_6189_);
                lean_ctor_set(v___x_6191_, 1, v___x_6190_);
                v___x_6192_ = l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6;
                v___x_6193_ = l_Lean_Lsp_instToJsonPosition_toJson(v_position_6182_);
                v___x_6194_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6194_, 0, v___x_6192_);
                lean_ctor_set(v___x_6194_, 1, v___x_6193_);
                v___x_6195_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6195_, 0, v___x_6194_);
                lean_ctor_set(v___x_6195_, 1, v___x_6190_);
                v___x_6196_ = l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0;
                v___x_6197_ = lean_uint64_to_nat(v_sessionId_6178_);
                v___x_6198_ = l_Lean_bignumToJson(v___x_6197_);
                v___x_6199_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6199_, 0, v___x_6196_);
                lean_ctor_set(v___x_6199_, 1, v___x_6198_);
                v___x_6200_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6200_, 0, v___x_6199_);
                lean_ctor_set(v___x_6200_, 1, v___x_6190_);
                v___x_6201_ = l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__10;
                v___x_6202_ = 1;
                v___x_6203_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_method_6179_,
                    v___x_6202_,
                );
                v___x_6204_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6204_, 0, v___x_6203_);
                v___x_6205_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6205_, 0, v___x_6201_);
                lean_ctor_set(v___x_6205_, 1, v___x_6204_);
                v___x_6206_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6206_, 0, v___x_6205_);
                lean_ctor_set(v___x_6206_, 1, v___x_6190_);
                v___x_6207_ = l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__15;
                v___x_6208_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6208_, 0, v___x_6207_);
                lean_ctor_set(v___x_6208_, 1, v_params_6180_);
                v___x_6209_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6209_, 0, v___x_6208_);
                lean_ctor_set(v___x_6209_, 1, v___x_6190_);
                v___x_6210_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6210_, 0, v___x_6209_);
                lean_ctor_set(v___x_6210_, 1, v___x_6190_);
                v___x_6211_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6211_, 0, v___x_6206_);
                lean_ctor_set(v___x_6211_, 1, v___x_6210_);
                v___x_6212_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6212_, 0, v___x_6200_);
                lean_ctor_set(v___x_6212_, 1, v___x_6211_);
                v___x_6213_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6213_, 0, v___x_6195_);
                lean_ctor_set(v___x_6213_, 1, v___x_6212_);
                v___x_6214_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6214_, 0, v___x_6191_);
                lean_ctor_set(v___x_6214_, 1, v___x_6213_);
                v___x_6215_ = l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0;
                v___x_6216_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_6214_, v___x_6215_);
                v___x_6217_ = l_Lean_Json_mkObj(v___x_6216_);
                lean_dec(v___x_6216_);
                return v___x_6217_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1(
    mut v_sz_6222_: usize,
    mut v_i_6223_: usize,
    mut v_bs_6224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6225_: u8 = 0;
    let mut v___x_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: usize = 0;
    let mut v___x_6231_: usize = 0;
    let mut v___x_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6225_ = lean_usize_dec_lt(v_i_6223_, v_sz_6222_);
                if v___x_6225_ == 0 {
                    v___x_6226_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6226_, 0, v_bs_6224_);
                    return v___x_6226_;
                } else {
                    v_v_6227_ = lean_array_uget(v_bs_6224_, v_i_6223_);
                    v___x_6228_ = lean_unsigned_to_nat(0);
                    v_bs_x27_6229_ = lean_array_uset(v_bs_6224_, v_i_6223_, v___x_6228_);
                    v___x_6230_ = 1usize;
                    v___x_6231_ = lean_usize_add(v_i_6223_, v___x_6230_);
                    v___x_6232_ = lean_array_uset(v_bs_x27_6229_, v_i_6223_, v_v_6227_);
                    v_i_6223_ = v___x_6231_;
                    v_bs_6224_ = v___x_6232_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1___boxed(
    mut v_sz_6234_: *mut LeanObject,
    mut v_i_6235_: *mut LeanObject,
    mut v_bs_6236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6237_: usize = 0;
    let mut v_i_boxed_6238_: usize = 0;
    let mut v_res_6239_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6237_ = lean_unbox_usize(v_sz_6234_);
    lean_dec(v_sz_6234_);
    v_i_boxed_6238_ = lean_unbox_usize(v_i_6235_);
    lean_dec(v_i_6235_);
    v_res_6239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_6237_, v_i_boxed_6238_, v_bs_6236_);
    return v_res_6239_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0(
    mut v_x_6240_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6240_) == 4 {
        let mut v_elems_6241_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_6242_: usize = 0;
        let mut v___x_6243_: usize = 0;
        let mut v___x_6244_: *mut LeanObject = core::ptr::null_mut();
        v_elems_6241_ = lean_ctor_get(v_x_6240_, 0);
        lean_inc_ref(v_elems_6241_);
        lean_dec_ref_known(v_x_6240_, 1);
        v_sz_6242_ = lean_array_size(v_elems_6241_);
        v___x_6243_ = 0usize;
        v___x_6244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1(v_sz_6242_, v___x_6243_, v_elems_6241_);
        return v___x_6244_;
    } else {
        let mut v___x_6245_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6246_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6247_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6248_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6249_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6250_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6251_: *mut LeanObject = core::ptr::null_mut();
        v___x_6245_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0;
        v___x_6246_ = lean_unsigned_to_nat(80);
        v___x_6247_ = l_Lean_Json_pretty(v_x_6240_, v___x_6246_);
        v___x_6248_ = lean_string_append(v___x_6245_, v___x_6247_);
        lean_dec_ref(v___x_6247_);
        v___x_6249_ = l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1;
        v___x_6250_ = lean_string_append(v___x_6248_, v___x_6249_);
        v___x_6251_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_6251_, 0, v___x_6250_);
        return v___x_6251_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0(
    mut v_j_6252_: *mut LeanObject,
    mut v_k_6253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6255_: *mut LeanObject = core::ptr::null_mut();
    v___x_6254_ = l_Lean_Json_getObjValD(v_j_6252_, v_k_6253_);
    v___x_6255_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0(v___x_6254_);
    return v___x_6255_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0___boxed(
    mut v_j_6256_: *mut LeanObject,
    mut v_k_6257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6258_: *mut LeanObject = core::ptr::null_mut();
    v_res_6258_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0(
            v_j_6256_, v_k_6257_,
        );
    lean_dec_ref(v_k_6257_);
    return v_res_6258_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2() -> *mut LeanObject
{
    let mut v___x_6264_: u8 = 0;
    let mut v___x_6265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6266_: *mut LeanObject = core::ptr::null_mut();
    v___x_6264_ = 1;
    v___x_6265_ = l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__1;
    v___x_6266_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_6265_, v___x_6264_);
    return v___x_6266_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3() -> *mut LeanObject
{
    let mut v___x_6267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6269_: *mut LeanObject = core::ptr::null_mut();
    v___x_6267_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6;
    v___x_6268_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2_once),
        _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2,
    );
    v___x_6269_ = lean_string_append(v___x_6268_, v___x_6267_);
    return v___x_6269_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4() -> *mut LeanObject
{
    let mut v___x_6270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut LeanObject = core::ptr::null_mut();
    v___x_6270_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6,
    );
    v___x_6271_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3,
    );
    v___x_6272_ = lean_string_append(v___x_6271_, v___x_6270_);
    return v___x_6272_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5() -> *mut LeanObject
{
    let mut v___x_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6275_: *mut LeanObject = core::ptr::null_mut();
    v___x_6273_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_6274_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4,
    );
    v___x_6275_ = lean_string_append(v___x_6274_, v___x_6273_);
    return v___x_6275_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6() -> *mut LeanObject
{
    let mut v___x_6276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut LeanObject = core::ptr::null_mut();
    v___x_6276_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6,
    );
    v___x_6277_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3,
    );
    v___x_6278_ = lean_string_append(v___x_6277_, v___x_6276_);
    return v___x_6278_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7() -> *mut LeanObject
{
    let mut v___x_6279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut LeanObject = core::ptr::null_mut();
    v___x_6279_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_6280_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6,
    );
    v___x_6281_ = lean_string_append(v___x_6280_, v___x_6279_);
    return v___x_6281_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10()
-> *mut LeanObject {
    let mut v___x_6285_: u8 = 0;
    let mut v___x_6286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: *mut LeanObject = core::ptr::null_mut();
    v___x_6285_ = 1;
    v___x_6286_ = l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__9;
    v___x_6287_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_6286_, v___x_6285_);
    return v___x_6287_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11()
-> *mut LeanObject {
    let mut v___x_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6290_: *mut LeanObject = core::ptr::null_mut();
    v___x_6288_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10_once),
        _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10,
    );
    v___x_6289_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3,
    );
    v___x_6290_ = lean_string_append(v___x_6289_, v___x_6288_);
    return v___x_6290_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12()
-> *mut LeanObject {
    let mut v___x_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut LeanObject = core::ptr::null_mut();
    v___x_6291_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_6292_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11_once),
        _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11,
    );
    v___x_6293_ = lean_string_append(v___x_6292_, v___x_6291_);
    return v___x_6293_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson(
    mut v_json_6294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6300_: u8 = 0;
    let mut v___x_6301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6306_: u8 = 0;
    let mut v_a_6307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6310_: u8 = 0;
    let mut v___x_6312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6314_: u8 = 0;
    let mut v_a_6315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6321_: u8 = 0;
    let mut v___x_6322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6327_: u8 = 0;
    let mut v_a_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6331_: u8 = 0;
    let mut v___x_6333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6335_: u8 = 0;
    let mut v_a_6336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6342_: u8 = 0;
    let mut v___x_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6348_: u8 = 0;
    let mut v_a_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6352_: u8 = 0;
    let mut v___x_6354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6356_: u8 = 0;
    let mut v_a_6357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6360_: u8 = 0;
    let mut v___x_6361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: u64 = 0;
    let mut v___x_6364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6366_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6295_ = l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0;
                lean_inc(v_json_6294_);
                v___x_6296_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_6294_, v___x_6295_);
                if lean_obj_tag(v___x_6296_) == 0 {
                    lean_dec(v_json_6294_);
                    v_a_6297_ = lean_ctor_get(v___x_6296_, 0);
                    v_isSharedCheck_6306_ = (!lean_is_exclusive(v___x_6296_)) as u8;
                    if v_isSharedCheck_6306_ == 0 {
                        v___x_6299_ = v___x_6296_;
                        v_isShared_6300_ = v_isSharedCheck_6306_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6297_);
                        lean_dec(v___x_6296_);
                        v___x_6299_ = lean_box(0);
                        v_isShared_6300_ = v_isSharedCheck_6306_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_6296_) == 0 {
                        lean_dec(v_json_6294_);
                        v_a_6307_ = lean_ctor_get(v___x_6296_, 0);
                        v_isSharedCheck_6314_ = (!lean_is_exclusive(v___x_6296_)) as u8;
                        if v_isSharedCheck_6314_ == 0 {
                            v___x_6309_ = v___x_6296_;
                            v_isShared_6310_ = v_isSharedCheck_6314_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6307_);
                            lean_dec(v___x_6296_);
                            v___x_6309_ = lean_box(0);
                            v_isShared_6310_ = v_isSharedCheck_6314_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_6315_ = lean_ctor_get(v___x_6296_, 0);
                        lean_inc(v_a_6315_);
                        lean_dec_ref_known(v___x_6296_, 1);
                        v___x_6316_ = l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0;
                        lean_inc(v_json_6294_);
                        v___x_6317_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_json_6294_, v___x_6316_);
                        if lean_obj_tag(v___x_6317_) == 0 {
                            lean_dec(v_a_6315_);
                            lean_dec(v_json_6294_);
                            v_a_6318_ = lean_ctor_get(v___x_6317_, 0);
                            v_isSharedCheck_6327_ = (!lean_is_exclusive(v___x_6317_)) as u8;
                            if v_isSharedCheck_6327_ == 0 {
                                v___x_6320_ = v___x_6317_;
                                v_isShared_6321_ = v_isSharedCheck_6327_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_6318_);
                                lean_dec(v___x_6317_);
                                v___x_6320_ = lean_box(0);
                                v_isShared_6321_ = v_isSharedCheck_6327_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_6317_) == 0 {
                                lean_dec(v_a_6315_);
                                lean_dec(v_json_6294_);
                                v_a_6328_ = lean_ctor_get(v___x_6317_, 0);
                                v_isSharedCheck_6335_ = (!lean_is_exclusive(v___x_6317_)) as u8;
                                if v_isSharedCheck_6335_ == 0 {
                                    v___x_6330_ = v___x_6317_;
                                    v_isShared_6331_ = v_isSharedCheck_6335_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_6328_);
                                    lean_dec(v___x_6317_);
                                    v___x_6330_ = lean_box(0);
                                    v_isShared_6331_ = v_isSharedCheck_6335_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_6336_ = lean_ctor_get(v___x_6317_, 0);
                                lean_inc(v_a_6336_);
                                lean_dec_ref_known(v___x_6317_, 1);
                                v___x_6337_ =
                                    l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__8;
                                v___x_6338_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0(v_json_6294_, v___x_6337_);
                                if lean_obj_tag(v___x_6338_) == 0 {
                                    lean_dec(v_a_6336_);
                                    lean_dec(v_a_6315_);
                                    v_a_6339_ = lean_ctor_get(v___x_6338_, 0);
                                    v_isSharedCheck_6348_ = (!lean_is_exclusive(v___x_6338_)) as u8;
                                    if v_isSharedCheck_6348_ == 0 {
                                        v___x_6341_ = v___x_6338_;
                                        v_isShared_6342_ = v_isSharedCheck_6348_;
                                        state = 9;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6339_);
                                        lean_dec(v___x_6338_);
                                        v___x_6341_ = lean_box(0);
                                        v_isShared_6342_ = v_isSharedCheck_6348_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if lean_obj_tag(v___x_6338_) == 0 {
                                        lean_dec(v_a_6336_);
                                        lean_dec(v_a_6315_);
                                        v_a_6349_ = lean_ctor_get(v___x_6338_, 0);
                                        v_isSharedCheck_6356_ =
                                            (!lean_is_exclusive(v___x_6338_)) as u8;
                                        if v_isSharedCheck_6356_ == 0 {
                                            v___x_6351_ = v___x_6338_;
                                            v_isShared_6352_ = v_isSharedCheck_6356_;
                                            state = 11;
                                            continue;
                                        } else {
                                            lean_inc(v_a_6349_);
                                            lean_dec(v___x_6338_);
                                            v___x_6351_ = lean_box(0);
                                            v_isShared_6352_ = v_isSharedCheck_6356_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_6357_ = lean_ctor_get(v___x_6338_, 0);
                                        v_isSharedCheck_6366_ =
                                            (!lean_is_exclusive(v___x_6338_)) as u8;
                                        if v_isSharedCheck_6366_ == 0 {
                                            v___x_6359_ = v___x_6338_;
                                            v_isShared_6360_ = v_isSharedCheck_6366_;
                                            state = 13;
                                            continue;
                                        } else {
                                            lean_inc(v_a_6357_);
                                            lean_dec(v___x_6338_);
                                            v___x_6359_ = lean_box(0);
                                            v_isShared_6360_ = v_isSharedCheck_6366_;
                                            state = 13;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_6301_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5,
                );
                v___x_6302_ = lean_string_append(v___x_6301_, v_a_6297_);
                lean_dec(v_a_6297_);
                if v_isShared_6300_ == 0 {
                    lean_ctor_set(v___x_6299_, 0, v___x_6302_);
                    v___x_6304_ = v___x_6299_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6305_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6305_, 0, v___x_6302_);
                    v___x_6304_ = v_reuseFailAlloc_6305_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6304_;
            }
            3 => {
                if v_isShared_6310_ == 0 {
                    lean_ctor_set_tag(v___x_6309_, 0);
                    v___x_6312_ = v___x_6309_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6313_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6313_, 0, v_a_6307_);
                    v___x_6312_ = v_reuseFailAlloc_6313_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6312_;
            }
            5 => {
                v___x_6322_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7,
                );
                v___x_6323_ = lean_string_append(v___x_6322_, v_a_6318_);
                lean_dec(v_a_6318_);
                if v_isShared_6321_ == 0 {
                    lean_ctor_set(v___x_6320_, 0, v___x_6323_);
                    v___x_6325_ = v___x_6320_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6326_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6326_, 0, v___x_6323_);
                    v___x_6325_ = v_reuseFailAlloc_6326_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6325_;
            }
            7 => {
                if v_isShared_6331_ == 0 {
                    lean_ctor_set_tag(v___x_6330_, 0);
                    v___x_6333_ = v___x_6330_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6334_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6334_, 0, v_a_6328_);
                    v___x_6333_ = v_reuseFailAlloc_6334_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6333_;
            }
            9 => {
                v___x_6343_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12,
                );
                v___x_6344_ = lean_string_append(v___x_6343_, v_a_6339_);
                lean_dec(v_a_6339_);
                if v_isShared_6342_ == 0 {
                    lean_ctor_set(v___x_6341_, 0, v___x_6344_);
                    v___x_6346_ = v___x_6341_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6347_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6347_, 0, v___x_6344_);
                    v___x_6346_ = v_reuseFailAlloc_6347_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6346_;
            }
            11 => {
                if v_isShared_6352_ == 0 {
                    lean_ctor_set_tag(v___x_6351_, 0);
                    v___x_6354_ = v___x_6351_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6355_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6355_, 0, v_a_6349_);
                    v___x_6354_ = v_reuseFailAlloc_6355_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6354_;
            }
            13 => {
                v___x_6361_ = lean_alloc_ctor(0, 2, (8) as u32);
                lean_ctor_set(v___x_6361_, 0, v_a_6315_);
                lean_ctor_set(v___x_6361_, 1, v_a_6357_);
                v___x_6362_ = lean_unbox_uint64(v_a_6336_);
                lean_dec(v_a_6336_);
                lean_ctor_set_uint64(
                    v___x_6361_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_6362_,
                );
                if v_isShared_6360_ == 0 {
                    lean_ctor_set(v___x_6359_, 0, v___x_6361_);
                    v___x_6364_ = v___x_6359_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6365_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6365_, 0, v___x_6361_);
                    v___x_6364_ = v_reuseFailAlloc_6365_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6364_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0(
    mut v_sz_6369_: usize,
    mut v_i_6370_: usize,
    mut v_bs_6371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6372_: u8 = 0;
    let mut v_v_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: usize = 0;
    let mut v___x_6377_: usize = 0;
    let mut v___x_6378_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6372_ = lean_usize_dec_lt(v_i_6370_, v_sz_6369_);
                if v___x_6372_ == 0 {
                    return v_bs_6371_;
                } else {
                    v_v_6373_ = lean_array_uget(v_bs_6371_, v_i_6370_);
                    v___x_6374_ = lean_unsigned_to_nat(0);
                    v_bs_x27_6375_ = lean_array_uset(v_bs_6371_, v_i_6370_, v___x_6374_);
                    v___x_6376_ = 1usize;
                    v___x_6377_ = lean_usize_add(v_i_6370_, v___x_6376_);
                    v___x_6378_ = lean_array_uset(v_bs_x27_6375_, v_i_6370_, v_v_6373_);
                    v_i_6370_ = v___x_6377_;
                    v_bs_6371_ = v___x_6378_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0___boxed(
    mut v_sz_6380_: *mut LeanObject,
    mut v_i_6381_: *mut LeanObject,
    mut v_bs_6382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6383_: usize = 0;
    let mut v_i_boxed_6384_: usize = 0;
    let mut v_res_6385_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6383_ = lean_unbox_usize(v_sz_6380_);
    lean_dec(v_sz_6380_);
    v_i_boxed_6384_ = lean_unbox_usize(v_i_6381_);
    lean_dec(v_i_6381_);
    v_res_6385_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0(v_sz_boxed_6383_, v_i_boxed_6384_, v_bs_6382_);
    return v_res_6385_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0(
    mut v_a_6386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_6387_: usize = 0;
    let mut v___x_6388_: usize = 0;
    let mut v___x_6389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6390_: *mut LeanObject = core::ptr::null_mut();
    v_sz_6387_ = lean_array_size(v_a_6386_);
    v___x_6388_ = 0usize;
    v___x_6389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0(v_sz_6387_, v___x_6388_, v_a_6386_);
    v___x_6390_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_6390_, 0, v___x_6389_);
    return v___x_6390_;
}
pub unsafe fn l_Lean_Lsp_instToJsonRpcReleaseParams_toJson(
    mut v_x_6391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_uri_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sessionId_6393_: u64 = 0;
    let mut v_refs_6394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6414_: *mut LeanObject = core::ptr::null_mut();
    v_uri_6392_ = lean_ctor_get(v_x_6391_, 0);
    lean_inc_ref(v_uri_6392_);
    v_sessionId_6393_ = lean_ctor_get_uint64(
        v_x_6391_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    v_refs_6394_ = lean_ctor_get(v_x_6391_, 1);
    lean_inc_ref(v_refs_6394_);
    lean_dec_ref(v_x_6391_);
    v___x_6395_ = l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0;
    v___x_6396_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_6396_, 0, v_uri_6392_);
    v___x_6397_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6397_, 0, v___x_6395_);
    lean_ctor_set(v___x_6397_, 1, v___x_6396_);
    v___x_6398_ = lean_box(0);
    v___x_6399_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6399_, 0, v___x_6397_);
    lean_ctor_set(v___x_6399_, 1, v___x_6398_);
    v___x_6400_ = l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0;
    v___x_6401_ = lean_uint64_to_nat(v_sessionId_6393_);
    v___x_6402_ = l_Lean_bignumToJson(v___x_6401_);
    v___x_6403_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6403_, 0, v___x_6400_);
    lean_ctor_set(v___x_6403_, 1, v___x_6402_);
    v___x_6404_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6404_, 0, v___x_6403_);
    lean_ctor_set(v___x_6404_, 1, v___x_6398_);
    v___x_6405_ = l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__8;
    v___x_6406_ =
        l_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0(v_refs_6394_);
    v___x_6407_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6407_, 0, v___x_6405_);
    lean_ctor_set(v___x_6407_, 1, v___x_6406_);
    v___x_6408_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6408_, 0, v___x_6407_);
    lean_ctor_set(v___x_6408_, 1, v___x_6398_);
    v___x_6409_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6409_, 0, v___x_6408_);
    lean_ctor_set(v___x_6409_, 1, v___x_6398_);
    v___x_6410_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6410_, 0, v___x_6404_);
    lean_ctor_set(v___x_6410_, 1, v___x_6409_);
    v___x_6411_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6411_, 0, v___x_6399_);
    lean_ctor_set(v___x_6411_, 1, v___x_6410_);
    v___x_6412_ = l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0;
    v___x_6413_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_6411_, v___x_6412_);
    v___x_6414_ = l_Lean_Json_mkObj(v___x_6413_);
    lean_dec(v___x_6413_);
    return v___x_6414_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2()
-> *mut LeanObject {
    let mut v___x_6422_: u8 = 0;
    let mut v___x_6423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6424_: *mut LeanObject = core::ptr::null_mut();
    v___x_6422_ = 1;
    v___x_6423_ = l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__1;
    v___x_6424_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_6423_, v___x_6422_);
    return v___x_6424_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3()
-> *mut LeanObject {
    let mut v___x_6425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut LeanObject = core::ptr::null_mut();
    v___x_6425_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6;
    v___x_6426_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2,
    );
    v___x_6427_ = lean_string_append(v___x_6426_, v___x_6425_);
    return v___x_6427_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4()
-> *mut LeanObject {
    let mut v___x_6428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6430_: *mut LeanObject = core::ptr::null_mut();
    v___x_6428_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6,
    );
    v___x_6429_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3,
    );
    v___x_6430_ = lean_string_append(v___x_6429_, v___x_6428_);
    return v___x_6430_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5()
-> *mut LeanObject {
    let mut v___x_6431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut LeanObject = core::ptr::null_mut();
    v___x_6431_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_6432_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4,
    );
    v___x_6433_ = lean_string_append(v___x_6432_, v___x_6431_);
    return v___x_6433_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6()
-> *mut LeanObject {
    let mut v___x_6434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut LeanObject = core::ptr::null_mut();
    v___x_6434_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6,
    );
    v___x_6435_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3,
    );
    v___x_6436_ = lean_string_append(v___x_6435_, v___x_6434_);
    return v___x_6436_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7()
-> *mut LeanObject {
    let mut v___x_6437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut LeanObject = core::ptr::null_mut();
    v___x_6437_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_6438_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6,
    );
    v___x_6439_ = lean_string_append(v___x_6438_, v___x_6437_);
    return v___x_6439_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson(
    mut v_json_6440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6446_: u8 = 0;
    let mut v___x_6447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6452_: u8 = 0;
    let mut v_a_6453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6456_: u8 = 0;
    let mut v___x_6458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6460_: u8 = 0;
    let mut v_a_6461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6467_: u8 = 0;
    let mut v___x_6468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6473_: u8 = 0;
    let mut v_a_6474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6477_: u8 = 0;
    let mut v___x_6479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6481_: u8 = 0;
    let mut v_a_6482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6485_: u8 = 0;
    let mut v___x_6486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6487_: u64 = 0;
    let mut v___x_6489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6491_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6441_ = l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0;
                lean_inc(v_json_6440_);
                v___x_6442_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_6440_, v___x_6441_);
                if lean_obj_tag(v___x_6442_) == 0 {
                    lean_dec(v_json_6440_);
                    v_a_6443_ = lean_ctor_get(v___x_6442_, 0);
                    v_isSharedCheck_6452_ = (!lean_is_exclusive(v___x_6442_)) as u8;
                    if v_isSharedCheck_6452_ == 0 {
                        v___x_6445_ = v___x_6442_;
                        v_isShared_6446_ = v_isSharedCheck_6452_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6443_);
                        lean_dec(v___x_6442_);
                        v___x_6445_ = lean_box(0);
                        v_isShared_6446_ = v_isSharedCheck_6452_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_6442_) == 0 {
                        lean_dec(v_json_6440_);
                        v_a_6453_ = lean_ctor_get(v___x_6442_, 0);
                        v_isSharedCheck_6460_ = (!lean_is_exclusive(v___x_6442_)) as u8;
                        if v_isSharedCheck_6460_ == 0 {
                            v___x_6455_ = v___x_6442_;
                            v_isShared_6456_ = v_isSharedCheck_6460_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6453_);
                            lean_dec(v___x_6442_);
                            v___x_6455_ = lean_box(0);
                            v_isShared_6456_ = v_isSharedCheck_6460_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_6461_ = lean_ctor_get(v___x_6442_, 0);
                        lean_inc(v_a_6461_);
                        lean_dec_ref_known(v___x_6442_, 1);
                        v___x_6462_ = l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0;
                        v___x_6463_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_json_6440_, v___x_6462_);
                        if lean_obj_tag(v___x_6463_) == 0 {
                            lean_dec(v_a_6461_);
                            v_a_6464_ = lean_ctor_get(v___x_6463_, 0);
                            v_isSharedCheck_6473_ = (!lean_is_exclusive(v___x_6463_)) as u8;
                            if v_isSharedCheck_6473_ == 0 {
                                v___x_6466_ = v___x_6463_;
                                v_isShared_6467_ = v_isSharedCheck_6473_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_6464_);
                                lean_dec(v___x_6463_);
                                v___x_6466_ = lean_box(0);
                                v_isShared_6467_ = v_isSharedCheck_6473_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_6463_) == 0 {
                                lean_dec(v_a_6461_);
                                v_a_6474_ = lean_ctor_get(v___x_6463_, 0);
                                v_isSharedCheck_6481_ = (!lean_is_exclusive(v___x_6463_)) as u8;
                                if v_isSharedCheck_6481_ == 0 {
                                    v___x_6476_ = v___x_6463_;
                                    v_isShared_6477_ = v_isSharedCheck_6481_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_6474_);
                                    lean_dec(v___x_6463_);
                                    v___x_6476_ = lean_box(0);
                                    v_isShared_6477_ = v_isSharedCheck_6481_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_6482_ = lean_ctor_get(v___x_6463_, 0);
                                v_isSharedCheck_6491_ = (!lean_is_exclusive(v___x_6463_)) as u8;
                                if v_isSharedCheck_6491_ == 0 {
                                    v___x_6484_ = v___x_6463_;
                                    v_isShared_6485_ = v_isSharedCheck_6491_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_6482_);
                                    lean_dec(v___x_6463_);
                                    v___x_6484_ = lean_box(0);
                                    v_isShared_6485_ = v_isSharedCheck_6491_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_6447_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5,
                );
                v___x_6448_ = lean_string_append(v___x_6447_, v_a_6443_);
                lean_dec(v_a_6443_);
                if v_isShared_6446_ == 0 {
                    lean_ctor_set(v___x_6445_, 0, v___x_6448_);
                    v___x_6450_ = v___x_6445_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6451_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6451_, 0, v___x_6448_);
                    v___x_6450_ = v_reuseFailAlloc_6451_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6450_;
            }
            3 => {
                if v_isShared_6456_ == 0 {
                    lean_ctor_set_tag(v___x_6455_, 0);
                    v___x_6458_ = v___x_6455_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6459_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6459_, 0, v_a_6453_);
                    v___x_6458_ = v_reuseFailAlloc_6459_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6458_;
            }
            5 => {
                v___x_6468_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7,
                );
                v___x_6469_ = lean_string_append(v___x_6468_, v_a_6464_);
                lean_dec(v_a_6464_);
                if v_isShared_6467_ == 0 {
                    lean_ctor_set(v___x_6466_, 0, v___x_6469_);
                    v___x_6471_ = v___x_6466_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6472_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6472_, 0, v___x_6469_);
                    v___x_6471_ = v_reuseFailAlloc_6472_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6471_;
            }
            7 => {
                if v_isShared_6477_ == 0 {
                    lean_ctor_set_tag(v___x_6476_, 0);
                    v___x_6479_ = v___x_6476_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6480_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6480_, 0, v_a_6474_);
                    v___x_6479_ = v_reuseFailAlloc_6480_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6479_;
            }
            9 => {
                v___x_6486_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_6486_, 0, v_a_6461_);
                v___x_6487_ = lean_unbox_uint64(v_a_6482_);
                lean_dec(v_a_6482_);
                lean_ctor_set_uint64(
                    v___x_6486_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_6487_,
                );
                if v_isShared_6485_ == 0 {
                    lean_ctor_set(v___x_6484_, 0, v___x_6486_);
                    v___x_6489_ = v___x_6484_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6490_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6490_, 0, v___x_6486_);
                    v___x_6489_ = v_reuseFailAlloc_6490_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6489_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonRpcKeepAliveParams_toJson(
    mut v_x_6494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_uri_6495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sessionId_6496_: u64 = 0;
    let mut v___x_6497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut LeanObject = core::ptr::null_mut();
    v_uri_6495_ = lean_ctor_get(v_x_6494_, 0);
    v_sessionId_6496_ = lean_ctor_get_uint64(
        v_x_6494_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v___x_6497_ = l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0;
    lean_inc_ref(v_uri_6495_);
    v___x_6498_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_6498_, 0, v_uri_6495_);
    v___x_6499_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6499_, 0, v___x_6497_);
    lean_ctor_set(v___x_6499_, 1, v___x_6498_);
    v___x_6500_ = lean_box(0);
    v___x_6501_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6501_, 0, v___x_6499_);
    lean_ctor_set(v___x_6501_, 1, v___x_6500_);
    v___x_6502_ = l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0;
    v___x_6503_ = lean_uint64_to_nat(v_sessionId_6496_);
    v___x_6504_ = l_Lean_bignumToJson(v___x_6503_);
    v___x_6505_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6505_, 0, v___x_6502_);
    lean_ctor_set(v___x_6505_, 1, v___x_6504_);
    v___x_6506_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6506_, 0, v___x_6505_);
    lean_ctor_set(v___x_6506_, 1, v___x_6500_);
    v___x_6507_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6507_, 0, v___x_6506_);
    lean_ctor_set(v___x_6507_, 1, v___x_6500_);
    v___x_6508_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6508_, 0, v___x_6501_);
    lean_ctor_set(v___x_6508_, 1, v___x_6507_);
    v___x_6509_ = l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0;
    v___x_6510_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_6508_, v___x_6509_);
    v___x_6511_ = l_Lean_Json_mkObj(v___x_6510_);
    lean_dec(v___x_6510_);
    return v___x_6511_;
}
pub unsafe fn l_Lean_Lsp_instToJsonRpcKeepAliveParams_toJson___boxed(
    mut v_x_6512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6513_: *mut LeanObject = core::ptr::null_mut();
    v_res_6513_ = l_Lean_Lsp_instToJsonRpcKeepAliveParams_toJson(v_x_6512_);
    lean_dec_ref(v_x_6512_);
    return v_res_6513_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Lsp_instReprLineRange_repr_spec__0(
    mut v_a_6520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6521_: *mut LeanObject = core::ptr::null_mut();
    v___x_6521_ = lean_nat_to_int(v_a_6520_);
    return v___x_6521_;
}
pub unsafe fn _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_6535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut LeanObject = core::ptr::null_mut();
    v___x_6535_ = lean_unsigned_to_nat(9);
    v___x_6536_ = lean_nat_to_int(v___x_6535_);
    return v___x_6536_;
}
pub unsafe fn _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12() -> *mut LeanObject {
    let mut v___x_6543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut LeanObject = core::ptr::null_mut();
    v___x_6543_ = lean_unsigned_to_nat(7);
    v___x_6544_ = lean_nat_to_int(v___x_6543_);
    return v___x_6544_;
}
pub unsafe fn _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14() -> *mut LeanObject {
    let mut v___x_6546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: *mut LeanObject = core::ptr::null_mut();
    v___x_6546_ = l_Lean_Lsp_instReprLineRange_repr___redArg___closed__0;
    v___x_6547_ = lean_string_length(v___x_6546_);
    return v___x_6547_;
}
pub unsafe fn _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15() -> *mut LeanObject {
    let mut v___x_6548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut LeanObject = core::ptr::null_mut();
    v___x_6548_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14_once),
        _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14,
    );
    v___x_6549_ = lean_nat_to_int(v___x_6548_);
    return v___x_6549_;
}
pub unsafe fn l_Lean_Lsp_instReprLineRange_repr___redArg(
    mut v_x_6554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_start_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_end_6556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6559_: u8 = 0;
    let mut v___x_6560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: u8 = 0;
    let mut v___x_6568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6591_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_6555_ = lean_ctor_get(v_x_6554_, 0);
                v_end_6556_ = lean_ctor_get(v_x_6554_, 1);
                v_isSharedCheck_6591_ = (!lean_is_exclusive(v_x_6554_)) as u8;
                if v_isSharedCheck_6591_ == 0 {
                    v___x_6558_ = v_x_6554_;
                    v_isShared_6559_ = v_isSharedCheck_6591_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_end_6556_);
                    lean_inc(v_start_6555_);
                    lean_dec(v_x_6554_);
                    v___x_6558_ = lean_box(0);
                    v_isShared_6559_ = v_isSharedCheck_6591_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6560_ = l_Lean_Lsp_instReprLineRange_repr___redArg___closed__5;
                v___x_6561_ = l_Lean_Lsp_instReprLineRange_repr___redArg___closed__6;
                v___x_6562_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7_once
                    ),
                    _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7,
                );
                v___x_6563_ = l_Nat_reprFast(v_start_6555_);
                v___x_6564_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6564_, 0, v___x_6563_);
                if v_isShared_6559_ == 0 {
                    lean_ctor_set_tag(v___x_6558_, 4);
                    lean_ctor_set(v___x_6558_, 1, v___x_6564_);
                    lean_ctor_set(v___x_6558_, 0, v___x_6562_);
                    v___x_6566_ = v___x_6558_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6590_ = lean_alloc_ctor(4, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6590_, 0, v___x_6562_);
                    lean_ctor_set(v_reuseFailAlloc_6590_, 1, v___x_6564_);
                    v___x_6566_ = v_reuseFailAlloc_6590_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6567_ = 0;
                v___x_6568_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_6568_, 0, v___x_6566_);
                lean_ctor_set_uint8(
                    v___x_6568_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_6567_,
                );
                v___x_6569_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6569_, 0, v___x_6561_);
                lean_ctor_set(v___x_6569_, 1, v___x_6568_);
                v___x_6570_ = l_Lean_Lsp_instReprLineRange_repr___redArg___closed__9;
                v___x_6571_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6571_, 0, v___x_6569_);
                lean_ctor_set(v___x_6571_, 1, v___x_6570_);
                v___x_6572_ = lean_box(1);
                v___x_6573_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6573_, 0, v___x_6571_);
                lean_ctor_set(v___x_6573_, 1, v___x_6572_);
                v___x_6574_ = l_Lean_Lsp_instReprLineRange_repr___redArg___closed__11;
                v___x_6575_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6575_, 0, v___x_6573_);
                lean_ctor_set(v___x_6575_, 1, v___x_6574_);
                v___x_6576_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6576_, 0, v___x_6575_);
                lean_ctor_set(v___x_6576_, 1, v___x_6560_);
                v___x_6577_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12_once
                    ),
                    _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12,
                );
                v___x_6578_ = l_Nat_reprFast(v_end_6556_);
                v___x_6579_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_6579_, 0, v___x_6578_);
                v___x_6580_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_6580_, 0, v___x_6577_);
                lean_ctor_set(v___x_6580_, 1, v___x_6579_);
                v___x_6581_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_6581_, 0, v___x_6580_);
                lean_ctor_set_uint8(
                    v___x_6581_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_6567_,
                );
                v___x_6582_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6582_, 0, v___x_6576_);
                lean_ctor_set(v___x_6582_, 1, v___x_6581_);
                v___x_6583_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15_once
                    ),
                    _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15,
                );
                v___x_6584_ = l_Lean_Lsp_instReprLineRange_repr___redArg___closed__16;
                v___x_6585_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6585_, 0, v___x_6584_);
                lean_ctor_set(v___x_6585_, 1, v___x_6582_);
                v___x_6586_ = l_Lean_Lsp_instReprLineRange_repr___redArg___closed__17;
                v___x_6587_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_6587_, 0, v___x_6585_);
                lean_ctor_set(v___x_6587_, 1, v___x_6586_);
                v___x_6588_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_6588_, 0, v___x_6583_);
                lean_ctor_set(v___x_6588_, 1, v___x_6587_);
                v___x_6589_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_6589_, 0, v___x_6588_);
                lean_ctor_set_uint8(
                    v___x_6589_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_6567_,
                );
                return v___x_6589_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instReprLineRange_repr(
    mut v_x_6592_: *mut LeanObject,
    mut v_prec_6593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6594_: *mut LeanObject = core::ptr::null_mut();
    v___x_6594_ = l_Lean_Lsp_instReprLineRange_repr___redArg(v_x_6592_);
    return v___x_6594_;
}
pub unsafe fn l_Lean_Lsp_instReprLineRange_repr___boxed(
    mut v_x_6595_: *mut LeanObject,
    mut v_prec_6596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6597_: *mut LeanObject = core::ptr::null_mut();
    v_res_6597_ = l_Lean_Lsp_instReprLineRange_repr(v_x_6595_, v_prec_6596_);
    lean_dec(v_prec_6596_);
    return v_res_6597_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2() -> *mut LeanObject {
    let mut v___x_6605_: u8 = 0;
    let mut v___x_6606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: *mut LeanObject = core::ptr::null_mut();
    v___x_6605_ = 1;
    v___x_6606_ = l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__1;
    v___x_6607_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_6606_, v___x_6605_);
    return v___x_6607_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3() -> *mut LeanObject {
    let mut v___x_6608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6610_: *mut LeanObject = core::ptr::null_mut();
    v___x_6608_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6;
    v___x_6609_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2_once),
        _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2,
    );
    v___x_6610_ = lean_string_append(v___x_6609_, v___x_6608_);
    return v___x_6610_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5() -> *mut LeanObject {
    let mut v___x_6613_: u8 = 0;
    let mut v___x_6614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut LeanObject = core::ptr::null_mut();
    v___x_6613_ = 1;
    v___x_6614_ = l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__4;
    v___x_6615_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_6614_, v___x_6613_);
    return v___x_6615_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6() -> *mut LeanObject {
    let mut v___x_6616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6618_: *mut LeanObject = core::ptr::null_mut();
    v___x_6616_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5_once),
        _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5,
    );
    v___x_6617_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3,
    );
    v___x_6618_ = lean_string_append(v___x_6617_, v___x_6616_);
    return v___x_6618_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7() -> *mut LeanObject {
    let mut v___x_6619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6621_: *mut LeanObject = core::ptr::null_mut();
    v___x_6619_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_6620_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6,
    );
    v___x_6621_ = lean_string_append(v___x_6620_, v___x_6619_);
    return v___x_6621_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9() -> *mut LeanObject {
    let mut v___x_6624_: u8 = 0;
    let mut v___x_6625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6626_: *mut LeanObject = core::ptr::null_mut();
    v___x_6624_ = 1;
    v___x_6625_ = l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__8;
    v___x_6626_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_6625_, v___x_6624_);
    return v___x_6626_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10() -> *mut LeanObject {
    let mut v___x_6627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6629_: *mut LeanObject = core::ptr::null_mut();
    v___x_6627_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9_once),
        _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9,
    );
    v___x_6628_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3,
    );
    v___x_6629_ = lean_string_append(v___x_6628_, v___x_6627_);
    return v___x_6629_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11() -> *mut LeanObject {
    let mut v___x_6630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut LeanObject = core::ptr::null_mut();
    v___x_6630_ = l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11;
    v___x_6631_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10_once),
        _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10,
    );
    v___x_6632_ = lean_string_append(v___x_6631_, v___x_6630_);
    return v___x_6632_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonLineRange_fromJson(
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
    let mut v___x_6677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6678_: u8 = 0;
    let mut v___x_6679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6683_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6634_ = l_Lean_Lsp_instReprLineRange_repr___redArg___closed__1;
                lean_inc(v_json_6633_);
                v___x_6635_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1(v_json_6633_, v___x_6634_);
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
                        v___x_6655_ = l_Lean_Lsp_instReprLineRange_repr___redArg___closed__10;
                        v___x_6656_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1(v_json_6633_, v___x_6655_);
                        if lean_obj_tag(v___x_6656_) == 0 {
                            lean_dec(v_a_6654_);
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
                                v_isSharedCheck_6683_ = (!lean_is_exclusive(v___x_6656_)) as u8;
                                if v_isSharedCheck_6683_ == 0 {
                                    v___x_6677_ = v___x_6656_;
                                    v_isShared_6678_ = v_isSharedCheck_6683_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_6675_);
                                    lean_dec(v___x_6656_);
                                    v___x_6677_ = lean_box(0);
                                    v_isShared_6678_ = v_isSharedCheck_6683_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_6640_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7,
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
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11,
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
                v___x_6679_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6679_, 0, v_a_6654_);
                lean_ctor_set(v___x_6679_, 1, v_a_6675_);
                if v_isShared_6678_ == 0 {
                    lean_ctor_set(v___x_6677_, 0, v___x_6679_);
                    v___x_6681_ = v___x_6677_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6682_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6682_, 0, v___x_6679_);
                    v___x_6681_ = v_reuseFailAlloc_6682_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6681_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonLineRange_toJson(
    mut v_x_6686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_start_6687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_end_6688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6691_: u8 = 0;
    let mut v___x_6692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6710_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_6687_ = lean_ctor_get(v_x_6686_, 0);
                v_end_6688_ = lean_ctor_get(v_x_6686_, 1);
                v_isSharedCheck_6710_ = (!lean_is_exclusive(v_x_6686_)) as u8;
                if v_isSharedCheck_6710_ == 0 {
                    v___x_6690_ = v_x_6686_;
                    v_isShared_6691_ = v_isSharedCheck_6710_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_end_6688_);
                    lean_inc(v_start_6687_);
                    lean_dec(v_x_6686_);
                    v___x_6690_ = lean_box(0);
                    v_isShared_6691_ = v_isSharedCheck_6710_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6692_ = l_Lean_Lsp_instReprLineRange_repr___redArg___closed__1;
                v___x_6693_ = l_Lean_JsonNumber_fromNat(v_start_6687_);
                v___x_6694_ = lean_alloc_ctor(2, 1, (0) as u32);
                lean_ctor_set(v___x_6694_, 0, v___x_6693_);
                if v_isShared_6691_ == 0 {
                    lean_ctor_set(v___x_6690_, 1, v___x_6694_);
                    lean_ctor_set(v___x_6690_, 0, v___x_6692_);
                    v___x_6696_ = v___x_6690_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6709_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6709_, 0, v___x_6692_);
                    lean_ctor_set(v_reuseFailAlloc_6709_, 1, v___x_6694_);
                    v___x_6696_ = v_reuseFailAlloc_6709_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6697_ = lean_box(0);
                v___x_6698_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6698_, 0, v___x_6696_);
                lean_ctor_set(v___x_6698_, 1, v___x_6697_);
                v___x_6699_ = l_Lean_Lsp_instReprLineRange_repr___redArg___closed__10;
                v___x_6700_ = l_Lean_JsonNumber_fromNat(v_end_6688_);
                v___x_6701_ = lean_alloc_ctor(2, 1, (0) as u32);
                lean_ctor_set(v___x_6701_, 0, v___x_6700_);
                v___x_6702_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6702_, 0, v___x_6699_);
                lean_ctor_set(v___x_6702_, 1, v___x_6701_);
                v___x_6703_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6703_, 0, v___x_6702_);
                lean_ctor_set(v___x_6703_, 1, v___x_6697_);
                v___x_6704_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6704_, 0, v___x_6703_);
                lean_ctor_set(v___x_6704_, 1, v___x_6697_);
                v___x_6705_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6705_, 0, v___x_6698_);
                lean_ctor_set(v___x_6705_, 1, v___x_6704_);
                v___x_6706_ = l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0;
                v___x_6707_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_6705_, v___x_6706_);
                v___x_6708_ = l_Lean_Json_mkObj(v___x_6707_);
                lean_dec(v___x_6707_);
                return v___x_6708_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Lsp_Extra(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Lsp_TextSync(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Rpc_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Lsp_instInhabitedDependencyBuildMode_default =
        _init_l_Lean_Lsp_instInhabitedDependencyBuildMode_default();
    l_Lean_Lsp_instInhabitedDependencyBuildMode =
        _init_l_Lean_Lsp_instInhabitedDependencyBuildMode();
    l_Lean_Lsp_instInhabitedLeanFileProgressKind_default =
        _init_l_Lean_Lsp_instInhabitedLeanFileProgressKind_default();
    l_Lean_Lsp_instInhabitedLeanFileProgressKind =
        _init_l_Lean_Lsp_instInhabitedLeanFileProgressKind();
    l_Lean_Lsp_instInhabitedLeanImportMetaKind_default =
        _init_l_Lean_Lsp_instInhabitedLeanImportMetaKind_default();
    l_Lean_Lsp_instInhabitedLeanImportMetaKind = _init_l_Lean_Lsp_instInhabitedLeanImportMetaKind();
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Lsp_Extra(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Lsp_Extra(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Lsp_TextSync(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Server_Rpc_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Lsp_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_Lsp_Extra(builtin);
}
