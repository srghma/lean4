// Lean compiler output
// Module: Lean.Widget.InteractiveCode
// Imports: Lean.Widget.TaggedText Lean.Widget.Basic
use crate::ffi::{
    lean_array_size, lean_array_to_list, lean_array_uget_borrowed, lean_array_uset,
    lean_expr_dbg_to_string, lean_nat_dec_eq, lean_nat_dec_lt, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_string_dec_eq, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_defWidth;
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getObjValD, l_Lean_Json_getStr_x3f, l_Lean_Json_mkObj,
};
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::l_Lean_Json_getTag_x3f;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_empty;
use crate::r#gen::Lean::Data::Position::l_Lean_instInhabitedFileMap_default;
use crate::r#gen::Lean::Expr::l_Lean_Expr_hasMVar;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::PrettyPrinter::Delaborator::Options::l_Lean_getPPInstantiateMVars;
use crate::r#gen::Lean::PrettyPrinter::l_Lean_PrettyPrinter_ppExprWithInfos;
use crate::r#gen::Lean::Server::Rpc::Basic::{
    l_Lean_Server_WithRpcRef_mk___redArg,
    l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg,
    l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg,
};
use crate::r#gen::Lean::SubExpr::{l_Lean_SubExpr_Pos_fromString_x3f, l_Lean_SubExpr_Pos_toString};
use crate::r#gen::Lean::Util::PPExt::l_Lean_pp_raw;
use crate::r#gen::Lean::Widget::Basic::{
    initialize_Lean_Widget_Basic,
    l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3_,
    runtime_initialize_Lean_Widget_Basic,
};
use crate::r#gen::Lean::Widget::TaggedText::{
    initialize_Lean_Widget_TaggedText, l_Lean_Widget_TaggedText_mapM___redArg,
    l_Lean_Widget_TaggedText_prettyTagged, l_Lean_Widget_TaggedText_stripTags___redArg,
    runtime_initialize_Lean_Widget_TaggedText,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__0_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [119, 97, 115, 67, 104, 97, 110, 103, 101, 100, 0],
};
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__2_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [119, 105, 108, 108, 67, 104, 97, 110, 103, 101, 0],
};
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__3_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__4_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [119, 97, 115, 68, 101, 108, 101, 116, 101, 100, 0],
};
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__5_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__6_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [119, 105, 108, 108, 68, 101, 108, 101, 116, 101, 0],
};
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__7_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__8_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [119, 97, 115, 73, 110, 115, 101, 114, 116, 101, 100, 0],
};
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__9_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__10_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [119, 105, 108, 108, 73, 110, 115, 101, 114, 116, 0],
};
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__11_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__10_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Widget_instToJsonDiffTag_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Widget_instToJsonDiffTag___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Widget_instToJsonDiffTag: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__0_value:
    leanh::LeanStringObject<23> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__2_value:
    leanh::LeanStringObject<33> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__4_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((4 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((3 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__6_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((2 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__7_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__8_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__9_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((5 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonDiffTag___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Widget_instFromJsonDiffTag_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Widget_instFromJsonDiffTag___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Widget_instFromJsonDiffTag: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [105, 110, 102, 111, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 117, 98, 101, 120, 112, 114, 80, 111, 115, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 105, 102, 102, 83, 116, 97, 116, 117, 115, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Widget_instToJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableSubexprInfo___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableSubexprInfo_enc_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableSubexprInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableSubexprInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableSubexprInfo___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableSubexprInfo___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableSubexprInfo___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableSubexprInfo___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableSubexprInfo___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableSubexprInfo___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instRpcEncodableSubexprInfo___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableSubexprInfo___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Widget_instRpcEncodableSubexprInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableSubexprInfo___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Widget_ppExprTagged___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Widget_ppExprTagged___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_ppExprTagged___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Widget_DiffTag_ctorIdx(mut v_x_750_: u8) -> *mut leanh::LeanObject {
    match v_x_750_ {
        0 => {
            let mut v___x_751_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_751_ = leanh::lean_unsigned_to_nat(0);
            return v___x_751_;
        }
        1 => {
            let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_752_ = leanh::lean_unsigned_to_nat(1);
            return v___x_752_;
        }
        2 => {
            let mut v___x_753_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_753_ = leanh::lean_unsigned_to_nat(2);
            return v___x_753_;
        }
        3 => {
            let mut v___x_754_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_754_ = leanh::lean_unsigned_to_nat(3);
            return v___x_754_;
        }
        4 => {
            let mut v___x_755_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_755_ = leanh::lean_unsigned_to_nat(4);
            return v___x_755_;
        }
        _ => {
            let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_756_ = leanh::lean_unsigned_to_nat(5);
            return v___x_756_;
        }
    }
}
pub unsafe fn l_Lean_Widget_DiffTag_ctorIdx___boxed(
    mut v_x_757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_758_: u8 = 0;
    let mut v_res_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_758_ = (leanh::lean_unbox(v_x_757_) as u8);
    v_res_759_ = l_Lean_Widget_DiffTag_ctorIdx(v_x_boxed_758_);
    return v_res_759_;
}
pub unsafe fn l_Lean_Widget_DiffTag_toCtorIdx(mut v_x_760_: u8) -> *mut leanh::LeanObject {
    let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_761_ = l_Lean_Widget_DiffTag_ctorIdx(v_x_760_);
    return v___x_761_;
}
pub unsafe fn l_Lean_Widget_DiffTag_toCtorIdx___boxed(
    mut v_x_762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_763_: u8 = 0;
    let mut v_res_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_763_ = (leanh::lean_unbox(v_x_762_) as u8);
    v_res_764_ = l_Lean_Widget_DiffTag_toCtorIdx(v_x_4__boxed_763_);
    return v_res_764_;
}
pub unsafe fn l_Lean_Widget_DiffTag_ctorElim___redArg(
    mut v_k_765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_765_);
    return v_k_765_;
}
pub unsafe fn l_Lean_Widget_DiffTag_ctorElim___redArg___boxed(
    mut v_k_766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_767_ = l_Lean_Widget_DiffTag_ctorElim___redArg(v_k_766_);
    leanh::lean_dec(v_k_766_);
    return v_res_767_;
}
pub unsafe fn l_Lean_Widget_DiffTag_ctorElim(
    mut v_motive_768_: *mut leanh::LeanObject,
    mut v_ctorIdx_769_: *mut leanh::LeanObject,
    mut v_t_770_: u8,
    mut v_h_771_: *mut leanh::LeanObject,
    mut v_k_772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_772_);
    return v_k_772_;
}
pub unsafe fn l_Lean_Widget_DiffTag_ctorElim___boxed(
    mut v_motive_773_: *mut leanh::LeanObject,
    mut v_ctorIdx_774_: *mut leanh::LeanObject,
    mut v_t_775_: *mut leanh::LeanObject,
    mut v_h_776_: *mut leanh::LeanObject,
    mut v_k_777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_778_: u8 = 0;
    let mut v_res_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_778_ = (leanh::lean_unbox(v_t_775_) as u8);
    v_res_779_ = l_Lean_Widget_DiffTag_ctorElim(
        v_motive_773_,
        v_ctorIdx_774_,
        v_t_boxed_778_,
        v_h_776_,
        v_k_777_,
    );
    leanh::lean_dec(v_k_777_);
    leanh::lean_dec(v_ctorIdx_774_);
    return v_res_779_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasChanged_elim___redArg(
    mut v_wasChanged_780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_wasChanged_780_);
    return v_wasChanged_780_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasChanged_elim___redArg___boxed(
    mut v_wasChanged_781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_782_ = l_Lean_Widget_DiffTag_wasChanged_elim___redArg(v_wasChanged_781_);
    leanh::lean_dec(v_wasChanged_781_);
    return v_res_782_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasChanged_elim(
    mut v_motive_783_: *mut leanh::LeanObject,
    mut v_t_784_: u8,
    mut v_h_785_: *mut leanh::LeanObject,
    mut v_wasChanged_786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_wasChanged_786_);
    return v_wasChanged_786_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasChanged_elim___boxed(
    mut v_motive_787_: *mut leanh::LeanObject,
    mut v_t_788_: *mut leanh::LeanObject,
    mut v_h_789_: *mut leanh::LeanObject,
    mut v_wasChanged_790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_791_: u8 = 0;
    let mut v_res_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_791_ = (leanh::lean_unbox(v_t_788_) as u8);
    v_res_792_ = l_Lean_Widget_DiffTag_wasChanged_elim(
        v_motive_787_,
        v_t_boxed_791_,
        v_h_789_,
        v_wasChanged_790_,
    );
    leanh::lean_dec(v_wasChanged_790_);
    return v_res_792_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willChange_elim___redArg(
    mut v_willChange_793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_willChange_793_);
    return v_willChange_793_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willChange_elim___redArg___boxed(
    mut v_willChange_794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_795_ = l_Lean_Widget_DiffTag_willChange_elim___redArg(v_willChange_794_);
    leanh::lean_dec(v_willChange_794_);
    return v_res_795_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willChange_elim(
    mut v_motive_796_: *mut leanh::LeanObject,
    mut v_t_797_: u8,
    mut v_h_798_: *mut leanh::LeanObject,
    mut v_willChange_799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_willChange_799_);
    return v_willChange_799_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willChange_elim___boxed(
    mut v_motive_800_: *mut leanh::LeanObject,
    mut v_t_801_: *mut leanh::LeanObject,
    mut v_h_802_: *mut leanh::LeanObject,
    mut v_willChange_803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_804_: u8 = 0;
    let mut v_res_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_804_ = (leanh::lean_unbox(v_t_801_) as u8);
    v_res_805_ = l_Lean_Widget_DiffTag_willChange_elim(
        v_motive_800_,
        v_t_boxed_804_,
        v_h_802_,
        v_willChange_803_,
    );
    leanh::lean_dec(v_willChange_803_);
    return v_res_805_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasDeleted_elim___redArg(
    mut v_wasDeleted_806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_wasDeleted_806_);
    return v_wasDeleted_806_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasDeleted_elim___redArg___boxed(
    mut v_wasDeleted_807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_808_ = l_Lean_Widget_DiffTag_wasDeleted_elim___redArg(v_wasDeleted_807_);
    leanh::lean_dec(v_wasDeleted_807_);
    return v_res_808_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasDeleted_elim(
    mut v_motive_809_: *mut leanh::LeanObject,
    mut v_t_810_: u8,
    mut v_h_811_: *mut leanh::LeanObject,
    mut v_wasDeleted_812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_wasDeleted_812_);
    return v_wasDeleted_812_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasDeleted_elim___boxed(
    mut v_motive_813_: *mut leanh::LeanObject,
    mut v_t_814_: *mut leanh::LeanObject,
    mut v_h_815_: *mut leanh::LeanObject,
    mut v_wasDeleted_816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_817_: u8 = 0;
    let mut v_res_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_817_ = (leanh::lean_unbox(v_t_814_) as u8);
    v_res_818_ = l_Lean_Widget_DiffTag_wasDeleted_elim(
        v_motive_813_,
        v_t_boxed_817_,
        v_h_815_,
        v_wasDeleted_816_,
    );
    leanh::lean_dec(v_wasDeleted_816_);
    return v_res_818_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willDelete_elim___redArg(
    mut v_willDelete_819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_willDelete_819_);
    return v_willDelete_819_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willDelete_elim___redArg___boxed(
    mut v_willDelete_820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_821_ = l_Lean_Widget_DiffTag_willDelete_elim___redArg(v_willDelete_820_);
    leanh::lean_dec(v_willDelete_820_);
    return v_res_821_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willDelete_elim(
    mut v_motive_822_: *mut leanh::LeanObject,
    mut v_t_823_: u8,
    mut v_h_824_: *mut leanh::LeanObject,
    mut v_willDelete_825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_willDelete_825_);
    return v_willDelete_825_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willDelete_elim___boxed(
    mut v_motive_826_: *mut leanh::LeanObject,
    mut v_t_827_: *mut leanh::LeanObject,
    mut v_h_828_: *mut leanh::LeanObject,
    mut v_willDelete_829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_830_: u8 = 0;
    let mut v_res_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_830_ = (leanh::lean_unbox(v_t_827_) as u8);
    v_res_831_ = l_Lean_Widget_DiffTag_willDelete_elim(
        v_motive_826_,
        v_t_boxed_830_,
        v_h_828_,
        v_willDelete_829_,
    );
    leanh::lean_dec(v_willDelete_829_);
    return v_res_831_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasInserted_elim___redArg(
    mut v_wasInserted_832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_wasInserted_832_);
    return v_wasInserted_832_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasInserted_elim___redArg___boxed(
    mut v_wasInserted_833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_834_ = l_Lean_Widget_DiffTag_wasInserted_elim___redArg(v_wasInserted_833_);
    leanh::lean_dec(v_wasInserted_833_);
    return v_res_834_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasInserted_elim(
    mut v_motive_835_: *mut leanh::LeanObject,
    mut v_t_836_: u8,
    mut v_h_837_: *mut leanh::LeanObject,
    mut v_wasInserted_838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_wasInserted_838_);
    return v_wasInserted_838_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasInserted_elim___boxed(
    mut v_motive_839_: *mut leanh::LeanObject,
    mut v_t_840_: *mut leanh::LeanObject,
    mut v_h_841_: *mut leanh::LeanObject,
    mut v_wasInserted_842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_843_: u8 = 0;
    let mut v_res_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_843_ = (leanh::lean_unbox(v_t_840_) as u8);
    v_res_844_ = l_Lean_Widget_DiffTag_wasInserted_elim(
        v_motive_839_,
        v_t_boxed_843_,
        v_h_841_,
        v_wasInserted_842_,
    );
    leanh::lean_dec(v_wasInserted_842_);
    return v_res_844_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willInsert_elim___redArg(
    mut v_willInsert_845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_willInsert_845_);
    return v_willInsert_845_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willInsert_elim___redArg___boxed(
    mut v_willInsert_846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_847_ = l_Lean_Widget_DiffTag_willInsert_elim___redArg(v_willInsert_846_);
    leanh::lean_dec(v_willInsert_846_);
    return v_res_847_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willInsert_elim(
    mut v_motive_848_: *mut leanh::LeanObject,
    mut v_t_849_: u8,
    mut v_h_850_: *mut leanh::LeanObject,
    mut v_willInsert_851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_willInsert_851_);
    return v_willInsert_851_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willInsert_elim___boxed(
    mut v_motive_852_: *mut leanh::LeanObject,
    mut v_t_853_: *mut leanh::LeanObject,
    mut v_h_854_: *mut leanh::LeanObject,
    mut v_willInsert_855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_856_: u8 = 0;
    let mut v_res_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_856_ = (leanh::lean_unbox(v_t_853_) as u8);
    v_res_857_ = l_Lean_Widget_DiffTag_willInsert_elim(
        v_motive_852_,
        v_t_boxed_856_,
        v_h_854_,
        v_willInsert_855_,
    );
    leanh::lean_dec(v_willInsert_855_);
    return v_res_857_;
}
pub unsafe fn l_Lean_Widget_instToJsonDiffTag_toJson(
    mut v_x_876_: u8,
) -> *mut leanh::LeanObject {
    match v_x_876_ {
        0 => {
            let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_877_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__1;
            return v___x_877_;
        }
        1 => {
            let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_878_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__3;
            return v___x_878_;
        }
        2 => {
            let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_879_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__5;
            return v___x_879_;
        }
        3 => {
            let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_880_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__7;
            return v___x_880_;
        }
        4 => {
            let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_881_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__9;
            return v___x_881_;
        }
        _ => {
            let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_882_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__11;
            return v___x_882_;
        }
    }
}
pub unsafe fn l_Lean_Widget_instToJsonDiffTag_toJson___boxed(
    mut v_x_883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_130__boxed_884_: u8 = 0;
    let mut v_res_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_130__boxed_884_ = (leanh::lean_unbox(v_x_883_) as u8);
    v_res_885_ = l_Lean_Widget_instToJsonDiffTag_toJson(v_x_130__boxed_884_);
    return v_res_885_;
}
pub unsafe fn l_Lean_Widget_instFromJsonDiffTag_fromJson(
    mut v_json_912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_913_ = l_Lean_Json_getTag_x3f(v_json_912_);
    if leanh::lean_obj_tag(v___x_913_) == 0 {
        let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_914_ = l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__1;
        return v___x_914_;
    } else {
        let mut v_val_915_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_917_: u8 = 0;
        v_val_915_ = leanh::lean_ctor_get(v___x_913_, 0);
        leanh::lean_inc(v_val_915_);
        leanh::lean_dec_ref_known(v___x_913_, 1);
        v___x_916_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__10;
        v___x_917_ = lean_string_dec_eq(v_val_915_, v___x_916_);
        if v___x_917_ == 0 {
            let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_919_: u8 = 0;
            v___x_918_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__0;
            v___x_919_ = lean_string_dec_eq(v_val_915_, v___x_918_);
            if v___x_919_ == 0 {
                let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_921_: u8 = 0;
                v___x_920_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__2;
                v___x_921_ = lean_string_dec_eq(v_val_915_, v___x_920_);
                if v___x_921_ == 0 {
                    let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_923_: u8 = 0;
                    v___x_922_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__4;
                    v___x_923_ = lean_string_dec_eq(v_val_915_, v___x_922_);
                    if v___x_923_ == 0 {
                        let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_925_: u8 = 0;
                        v___x_924_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__6;
                        v___x_925_ = lean_string_dec_eq(v_val_915_, v___x_924_);
                        if v___x_925_ == 0 {
                            let mut v___x_926_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_927_: u8 = 0;
                            v___x_926_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__8;
                            v___x_927_ = lean_string_dec_eq(v_val_915_, v___x_926_);
                            leanh::lean_dec(v_val_915_);
                            if v___x_927_ == 0 {
                                let mut v___x_928_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                v___x_928_ = l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__3;
                                return v___x_928_;
                            } else {
                                let mut v___x_929_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                v___x_929_ = l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__4;
                                return v___x_929_;
                            }
                        } else {
                            let mut v___x_930_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            leanh::lean_dec(v_val_915_);
                            v___x_930_ = l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__5;
                            return v___x_930_;
                        }
                    } else {
                        let mut v___x_931_: *mut leanh::LeanObject = core::ptr::null_mut();
                        leanh::lean_dec(v_val_915_);
                        v___x_931_ = l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__6;
                        return v___x_931_;
                    }
                } else {
                    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_val_915_);
                    v___x_932_ = l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__7;
                    return v___x_932_;
                }
            } else {
                let mut v___x_933_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_val_915_);
                v___x_933_ = l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__8;
                return v___x_933_;
            }
        } else {
            let mut v___x_934_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_val_915_);
            v___x_934_ = l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__9;
            return v___x_934_;
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0(
    mut v_j_937_: *mut leanh::LeanObject,
    mut v_k_938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_939_ = l_Lean_Json_getObjValD(v_j_937_, v_k_938_);
    v___x_940_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_940_, 0, v___x_939_);
    return v___x_940_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0___boxed(
    mut v_j_941_: *mut leanh::LeanObject,
    mut v_k_942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_943_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0(v_j_941_, v_k_942_);
    leanh::lean_dec_ref(v_k_942_);
    return v_res_943_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1(
    mut v_x_946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_946_) == 0 {
        let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_947_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1___closed__0;
        return v___x_947_;
    } else {
        let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_948_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_948_, 0, v_x_946_);
        v___x_949_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_949_, 0, v___x_948_);
        return v___x_949_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1(
    mut v_j_950_: *mut leanh::LeanObject,
    mut v_k_951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_952_ = l_Lean_Json_getObjValD(v_j_950_, v_k_951_);
    v___x_953_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1(v___x_952_);
    return v___x_953_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1___boxed(
    mut v_j_954_: *mut leanh::LeanObject,
    mut v_k_955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_956_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1(v_j_954_, v_k_955_);
    leanh::lean_dec_ref(v_k_955_);
    return v_res_956_;
}
pub unsafe fn l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_(
    mut v_json_960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_972_: u8 = 0;
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_977_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_961_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_;
                leanh::lean_inc_n(v_json_960_, 2);
                v___x_962_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0(v_json_960_, v___x_961_);
                v_a_963_ = leanh::lean_ctor_get(v___x_962_, 0);
                leanh::lean_inc(v_a_963_);
                leanh::lean_dec_ref(v___x_962_);
                v___x_964_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_;
                v___x_965_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0(v_json_960_, v___x_964_);
                v_a_966_ = leanh::lean_ctor_get(v___x_965_, 0);
                leanh::lean_inc(v_a_966_);
                leanh::lean_dec_ref(v___x_965_);
                v___x_967_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_;
                v___x_968_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1(v_json_960_, v___x_967_);
                v_a_969_ = leanh::lean_ctor_get(v___x_968_, 0);
                v_isSharedCheck_977_ = (!leanh::lean_is_exclusive(v___x_968_)) as u8;
                if v_isSharedCheck_977_ == 0 {
                    v___x_971_ = v___x_968_;
                    v_isShared_972_ = v_isSharedCheck_977_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_969_);
                    leanh::lean_dec(v___x_968_);
                    v___x_971_ = leanh::lean_box(0);
                    v_isShared_972_ = v_isSharedCheck_977_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_973_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_973_, 0, v_a_963_);
                leanh::lean_ctor_set(v___x_973_, 1, v_a_966_);
                leanh::lean_ctor_set(v___x_973_, 2, v_a_969_);
                if v_isShared_972_ == 0 {
                    leanh::lean_ctor_set(v___x_971_, 0, v___x_973_);
                    v___x_975_ = v___x_971_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_976_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
                    v___x_975_ = v_reuseFailAlloc_976_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_975_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__spec__0(
    mut v_k_980_: *mut leanh::LeanObject,
    mut v_x_981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_981_) == 0 {
        let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_980_);
        v___x_982_ = leanh::lean_box(0);
        return v___x_982_;
    } else {
        let mut v_val_983_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_983_ = leanh::lean_ctor_get(v_x_981_, 0);
        leanh::lean_inc(v_val_983_);
        v___x_984_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_984_, 0, v_k_980_);
        leanh::lean_ctor_set(v___x_984_, 1, v_val_983_);
        v___x_985_ = leanh::lean_box(0);
        v___x_986_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_986_, 0, v___x_984_);
        leanh::lean_ctor_set(v___x_986_, 1, v___x_985_);
        return v___x_986_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__spec__0___boxed(
    mut v_k_987_: *mut leanh::LeanObject,
    mut v_x_988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_989_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__spec__0(v_k_987_, v_x_988_);
    leanh::lean_dec(v_x_988_);
    return v_res_989_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__spec__1(
    mut v_a_990_: *mut leanh::LeanObject,
    mut v_a_991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_990_) == 0 {
                    v___x_992_ = lean_array_to_list(v_a_991_);
                    return v___x_992_;
                } else {
                    v_head_993_ = leanh::lean_ctor_get(v_a_990_, 0);
                    leanh::lean_inc(v_head_993_);
                    v_tail_994_ = leanh::lean_ctor_get(v_a_990_, 1);
                    leanh::lean_inc(v_tail_994_);
                    leanh::lean_dec_ref_known(v_a_990_, 2);
                    v___x_995_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_991_,
                        v_head_993_,
                    );
                    v_a_990_ = v_tail_994_;
                    v_a_991_ = v___x_995_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33_(
    mut v_x_999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_info_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subexprPos_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diffStatus_x3f_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_info_1000_ = leanh::lean_ctor_get(v_x_999_, 0);
    v_subexprPos_1001_ = leanh::lean_ctor_get(v_x_999_, 1);
    v_diffStatus_x3f_1002_ = leanh::lean_ctor_get(v_x_999_, 2);
    v___x_1003_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_;
    leanh::lean_inc(v_info_1000_);
    v___x_1004_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1004_, 0, v___x_1003_);
    leanh::lean_ctor_set(v___x_1004_, 1, v_info_1000_);
    v___x_1005_ = leanh::lean_box(0);
    v___x_1006_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1006_, 0, v___x_1004_);
    leanh::lean_ctor_set(v___x_1006_, 1, v___x_1005_);
    v___x_1007_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_;
    leanh::lean_inc(v_subexprPos_1001_);
    v___x_1008_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1008_, 0, v___x_1007_);
    leanh::lean_ctor_set(v___x_1008_, 1, v_subexprPos_1001_);
    v___x_1009_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1009_, 0, v___x_1008_);
    leanh::lean_ctor_set(v___x_1009_, 1, v___x_1005_);
    v___x_1010_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_;
    v___x_1011_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__spec__0(v___x_1010_, v_diffStatus_x3f_1002_);
    v___x_1012_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1012_, 0, v___x_1011_);
    leanh::lean_ctor_set(v___x_1012_, 1, v___x_1005_);
    v___x_1013_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1013_, 0, v___x_1009_);
    leanh::lean_ctor_set(v___x_1013_, 1, v___x_1012_);
    v___x_1014_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1014_, 0, v___x_1006_);
    leanh::lean_ctor_set(v___x_1014_, 1, v___x_1013_);
    v___x_1015_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33_;
    v___x_1016_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__spec__1(v___x_1014_, v___x_1015_);
    v___x_1017_ = l_Lean_Json_mkObj(v___x_1016_);
    leanh::lean_dec(v___x_1016_);
    return v___x_1017_;
}
pub unsafe fn l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33____boxed(
    mut v_x_1018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1019_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33_(v_x_1018_);
    leanh::lean_dec_ref(v_x_1018_);
    return v_res_1019_;
}
pub unsafe fn l_Lean_Widget_instRpcEncodableSubexprInfo_enc_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_(
    mut v_a_1022_: *mut leanh::LeanObject,
    mut v_a_1023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_info_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subexprPos_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diffStatus_x3f_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1029_: u8 = 0;
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1036_: u8 = 0;
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1052_: u8 = 0;
    let mut v___x_1053_: u8 = 0;
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1058_: u8 = 0;
    let mut v_isSharedCheck_1059_: u8 = 0;
    let mut v_isSharedCheck_1060_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_info_1024_ = leanh::lean_ctor_get(v_a_1022_, 0);
                v_subexprPos_1025_ = leanh::lean_ctor_get(v_a_1022_, 1);
                v_diffStatus_x3f_1026_ = leanh::lean_ctor_get(v_a_1022_, 2);
                v_isSharedCheck_1060_ = (!leanh::lean_is_exclusive(v_a_1022_)) as u8;
                if v_isSharedCheck_1060_ == 0 {
                    v___x_1028_ = v_a_1022_;
                    v_isShared_1029_ = v_isSharedCheck_1060_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diffStatus_x3f_1026_);
                    leanh::lean_inc(v_subexprPos_1025_);
                    leanh::lean_inc(v_info_1024_);
                    leanh::lean_dec(v_a_1022_);
                    v___x_1028_ = leanh::lean_box(0);
                    v_isShared_1029_ = v_isSharedCheck_1060_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1030_ =
                    l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3_;
                v___x_1031_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(
                    v___x_1030_,
                    v_info_1024_,
                    v_a_1023_,
                );
                leanh::lean_dec_ref(v_info_1024_);
                v_fst_1032_ = leanh::lean_ctor_get(v___x_1031_, 0);
                v_snd_1033_ = leanh::lean_ctor_get(v___x_1031_, 1);
                v_isSharedCheck_1059_ = (!leanh::lean_is_exclusive(v___x_1031_)) as u8;
                if v_isSharedCheck_1059_ == 0 {
                    v___x_1035_ = v___x_1031_;
                    v_isShared_1036_ = v_isSharedCheck_1059_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1033_);
                    leanh::lean_inc(v_fst_1032_);
                    leanh::lean_dec(v___x_1031_);
                    v___x_1035_ = leanh::lean_box(0);
                    v_isShared_1036_ = v_isSharedCheck_1059_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1037_ = l_Lean_SubExpr_Pos_toString(v_subexprPos_1025_);
                leanh::lean_dec(v_subexprPos_1025_);
                v___x_1038_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1038_, 0, v___x_1037_);
                if leanh::lean_obj_tag(v_diffStatus_x3f_1026_) == 0 {
                    v___x_1048_ = leanh::lean_box(0);
                    v_fst_1040_ = v___x_1048_;
                    state = 3;
                    continue;
                } else {
                    v_val_1049_ = leanh::lean_ctor_get(v_diffStatus_x3f_1026_, 0);
                    v_isSharedCheck_1058_ =
                        (!leanh::lean_is_exclusive(v_diffStatus_x3f_1026_)) as u8;
                    if v_isSharedCheck_1058_ == 0 {
                        v___x_1051_ = v_diffStatus_x3f_1026_;
                        v_isShared_1052_ = v_isSharedCheck_1058_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1049_);
                        leanh::lean_dec(v_diffStatus_x3f_1026_);
                        v___x_1051_ = leanh::lean_box(0);
                        v_isShared_1052_ = v_isSharedCheck_1058_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1029_ == 0 {
                    leanh::lean_ctor_set(v___x_1028_, 2, v_fst_1040_);
                    leanh::lean_ctor_set(v___x_1028_, 1, v___x_1038_);
                    leanh::lean_ctor_set(v___x_1028_, 0, v_fst_1032_);
                    v___x_1042_ = v___x_1028_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1047_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_fst_1032_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1047_, 1, v___x_1038_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1047_, 2, v_fst_1040_);
                    v___x_1042_ = v_reuseFailAlloc_1047_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1043_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33_(v___x_1042_);
                leanh::lean_dec_ref(v___x_1042_);
                if v_isShared_1036_ == 0 {
                    leanh::lean_ctor_set(v___x_1035_, 0, v___x_1043_);
                    v___x_1045_ = v___x_1035_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1046_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1043_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_snd_1033_);
                    v___x_1045_ = v_reuseFailAlloc_1046_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1045_;
            }
            6 => {
                v___x_1053_ = (leanh::lean_unbox(v_val_1049_) as u8);
                leanh::lean_dec(v_val_1049_);
                v___x_1054_ = l_Lean_Widget_instToJsonDiffTag_toJson(v___x_1053_);
                if v_isShared_1052_ == 0 {
                    leanh::lean_ctor_set(v___x_1051_, 0, v___x_1054_);
                    v___x_1056_ = v___x_1051_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1057_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
                    v___x_1056_ = v_reuseFailAlloc_1057_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_fst_1040_ = v___x_1056_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___redArg(
    mut v_x_1061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_x_1061_);
    return v_x_1061_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___redArg___boxed(
    mut v_x_1062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1063_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___redArg(v_x_1062_);
    leanh::lean_dec_ref(v_x_1062_);
    return v_res_1063_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0(
    mut v_00_u03b1_1064_: *mut leanh::LeanObject,
    mut v_x_1065_: *mut leanh::LeanObject,
    mut v___y_1066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_x_1065_);
    return v_x_1065_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___boxed(
    mut v_00_u03b1_1067_: *mut leanh::LeanObject,
    mut v_x_1068_: *mut leanh::LeanObject,
    mut v___y_1069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1070_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0(v_00_u03b1_1067_, v_x_1068_, v___y_1069_);
    leanh::lean_dec_ref(v___y_1069_);
    leanh::lean_dec_ref(v_x_1068_);
    return v_res_1070_;
}
pub unsafe fn l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_(
    mut v_j_1071_: *mut leanh::LeanObject,
    mut v_a_1072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1077_: u8 = 0;
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1081_: u8 = 0;
    let mut v_a_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subexprPos_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diffStatus_x3f_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1088_: u8 = 0;
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1094_: u8 = 0;
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1098_: u8 = 0;
    let mut v_a_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1104_: u8 = 0;
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1108_: u8 = 0;
    let mut v_a_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1114_: u8 = 0;
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1118_: u8 = 0;
    let mut v_a_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1122_: u8 = 0;
    let mut v_____do__lift_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1135_: u8 = 0;
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1140_: u8 = 0;
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1144_: u8 = 0;
    let mut v_a_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1149_: u8 = 0;
    let mut v_isSharedCheck_1150_: u8 = 0;
    let mut v_isSharedCheck_1151_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1073_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_(v_j_1071_);
                if leanh::lean_obj_tag(v___x_1073_) == 0 {
                    v_a_1074_ = leanh::lean_ctor_get(v___x_1073_, 0);
                    v_isSharedCheck_1081_ = (!leanh::lean_is_exclusive(v___x_1073_)) as u8;
                    if v_isSharedCheck_1081_ == 0 {
                        v___x_1076_ = v___x_1073_;
                        v_isShared_1077_ = v_isSharedCheck_1081_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1074_);
                        leanh::lean_dec(v___x_1073_);
                        v___x_1076_ = leanh::lean_box(0);
                        v_isShared_1077_ = v_isSharedCheck_1081_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1082_ = leanh::lean_ctor_get(v___x_1073_, 0);
                    leanh::lean_inc(v_a_1082_);
                    leanh::lean_dec_ref_known(v___x_1073_, 1);
                    v_info_1083_ = leanh::lean_ctor_get(v_a_1082_, 0);
                    v_subexprPos_1084_ = leanh::lean_ctor_get(v_a_1082_, 1);
                    v_diffStatus_x3f_1085_ = leanh::lean_ctor_get(v_a_1082_, 2);
                    v_isSharedCheck_1151_ = (!leanh::lean_is_exclusive(v_a_1082_)) as u8;
                    if v_isSharedCheck_1151_ == 0 {
                        v___x_1087_ = v_a_1082_;
                        v_isShared_1088_ = v_isSharedCheck_1151_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_diffStatus_x3f_1085_);
                        leanh::lean_inc(v_subexprPos_1084_);
                        leanh::lean_inc(v_info_1083_);
                        leanh::lean_dec(v_a_1082_);
                        v___x_1087_ = leanh::lean_box(0);
                        v_isShared_1088_ = v_isSharedCheck_1151_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1077_ == 0 {
                    v___x_1079_ = v___x_1076_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1080_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
                    v___x_1079_ = v_reuseFailAlloc_1080_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1079_;
            }
            3 => {
                v___x_1089_ =
                    l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_2038268869____hygCtx___hyg_3_;
                v___x_1090_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(
                    v___x_1089_,
                    v_info_1083_,
                    v_a_1072_,
                );
                if leanh::lean_obj_tag(v___x_1090_) == 0 {
                    leanh::lean_del_object(v___x_1087_);
                    leanh::lean_dec(v_diffStatus_x3f_1085_);
                    leanh::lean_dec(v_subexprPos_1084_);
                    v_a_1091_ = leanh::lean_ctor_get(v___x_1090_, 0);
                    v_isSharedCheck_1098_ = (!leanh::lean_is_exclusive(v___x_1090_)) as u8;
                    if v_isSharedCheck_1098_ == 0 {
                        v___x_1093_ = v___x_1090_;
                        v_isShared_1094_ = v_isSharedCheck_1098_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1091_);
                        leanh::lean_dec(v___x_1090_);
                        v___x_1093_ = leanh::lean_box(0);
                        v_isShared_1094_ = v_isSharedCheck_1098_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_1099_ = leanh::lean_ctor_get(v___x_1090_, 0);
                    leanh::lean_inc(v_a_1099_);
                    leanh::lean_dec_ref_known(v___x_1090_, 1);
                    v___x_1100_ = l_Lean_Json_getStr_x3f(v_subexprPos_1084_);
                    if leanh::lean_obj_tag(v___x_1100_) == 0 {
                        leanh::lean_dec(v_a_1099_);
                        leanh::lean_del_object(v___x_1087_);
                        leanh::lean_dec(v_diffStatus_x3f_1085_);
                        v_a_1101_ = leanh::lean_ctor_get(v___x_1100_, 0);
                        v_isSharedCheck_1108_ =
                            (!leanh::lean_is_exclusive(v___x_1100_)) as u8;
                        if v_isSharedCheck_1108_ == 0 {
                            v___x_1103_ = v___x_1100_;
                            v_isShared_1104_ = v_isSharedCheck_1108_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1101_);
                            leanh::lean_dec(v___x_1100_);
                            v___x_1103_ = leanh::lean_box(0);
                            v_isShared_1104_ = v_isSharedCheck_1108_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_1109_ = leanh::lean_ctor_get(v___x_1100_, 0);
                        leanh::lean_inc(v_a_1109_);
                        leanh::lean_dec_ref_known(v___x_1100_, 1);
                        v___x_1110_ = l_Lean_SubExpr_Pos_fromString_x3f(v_a_1109_);
                        if leanh::lean_obj_tag(v___x_1110_) == 0 {
                            leanh::lean_dec(v_a_1099_);
                            leanh::lean_del_object(v___x_1087_);
                            leanh::lean_dec(v_diffStatus_x3f_1085_);
                            v_a_1111_ = leanh::lean_ctor_get(v___x_1110_, 0);
                            v_isSharedCheck_1118_ =
                                (!leanh::lean_is_exclusive(v___x_1110_)) as u8;
                            if v_isSharedCheck_1118_ == 0 {
                                v___x_1113_ = v___x_1110_;
                                v_isShared_1114_ = v_isSharedCheck_1118_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1111_);
                                leanh::lean_dec(v___x_1110_);
                                v___x_1113_ = leanh::lean_box(0);
                                v_isShared_1114_ = v_isSharedCheck_1118_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v_a_1119_ = leanh::lean_ctor_get(v___x_1110_, 0);
                            v_isSharedCheck_1150_ =
                                (!leanh::lean_is_exclusive(v___x_1110_)) as u8;
                            if v_isSharedCheck_1150_ == 0 {
                                v___x_1121_ = v___x_1110_;
                                v_isShared_1122_ = v_isSharedCheck_1150_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1119_);
                                leanh::lean_dec(v___x_1110_);
                                v___x_1121_ = leanh::lean_box(0);
                                v_isShared_1122_ = v_isSharedCheck_1150_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                }
            }
            4 => {
                if v_isShared_1094_ == 0 {
                    v___x_1096_ = v___x_1093_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1097_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
                    v___x_1096_ = v_reuseFailAlloc_1097_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1096_;
            }
            6 => {
                if v_isShared_1104_ == 0 {
                    v___x_1106_ = v___x_1103_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1107_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
                    v___x_1106_ = v_reuseFailAlloc_1107_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1106_;
            }
            8 => {
                if v_isShared_1114_ == 0 {
                    v___x_1116_ = v___x_1113_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1117_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
                    v___x_1116_ = v_reuseFailAlloc_1117_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1116_;
            }
            10 => {
                if leanh::lean_obj_tag(v_diffStatus_x3f_1085_) == 0 {
                    v___x_1131_ = leanh::lean_box(0);
                    v_____do__lift_1124_ = v___x_1131_;
                    state = 11;
                    continue;
                } else {
                    v_val_1132_ = leanh::lean_ctor_get(v_diffStatus_x3f_1085_, 0);
                    v_isSharedCheck_1149_ =
                        (!leanh::lean_is_exclusive(v_diffStatus_x3f_1085_)) as u8;
                    if v_isSharedCheck_1149_ == 0 {
                        v___x_1134_ = v_diffStatus_x3f_1085_;
                        v_isShared_1135_ = v_isSharedCheck_1149_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1132_);
                        leanh::lean_dec(v_diffStatus_x3f_1085_);
                        v___x_1134_ = leanh::lean_box(0);
                        v_isShared_1135_ = v_isSharedCheck_1149_;
                        state = 14;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_1088_ == 0 {
                    leanh::lean_ctor_set(v___x_1087_, 2, v_____do__lift_1124_);
                    leanh::lean_ctor_set(v___x_1087_, 1, v_a_1119_);
                    leanh::lean_ctor_set(v___x_1087_, 0, v_a_1099_);
                    v___x_1126_ = v___x_1087_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1130_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1099_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_a_1119_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1130_, 2, v_____do__lift_1124_);
                    v___x_1126_ = v_reuseFailAlloc_1130_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_1122_ == 0 {
                    leanh::lean_ctor_set(v___x_1121_, 0, v___x_1126_);
                    v___x_1128_ = v___x_1121_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1129_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
                    v___x_1128_ = v_reuseFailAlloc_1129_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1128_;
            }
            14 => {
                v___x_1136_ = l_Lean_Widget_instFromJsonDiffTag_fromJson(v_val_1132_);
                if leanh::lean_obj_tag(v___x_1136_) == 0 {
                    leanh::lean_del_object(v___x_1134_);
                    leanh::lean_del_object(v___x_1121_);
                    leanh::lean_dec(v_a_1119_);
                    leanh::lean_dec(v_a_1099_);
                    leanh::lean_del_object(v___x_1087_);
                    v_a_1137_ = leanh::lean_ctor_get(v___x_1136_, 0);
                    v_isSharedCheck_1144_ = (!leanh::lean_is_exclusive(v___x_1136_)) as u8;
                    if v_isSharedCheck_1144_ == 0 {
                        v___x_1139_ = v___x_1136_;
                        v_isShared_1140_ = v_isSharedCheck_1144_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1137_);
                        leanh::lean_dec(v___x_1136_);
                        v___x_1139_ = leanh::lean_box(0);
                        v_isShared_1140_ = v_isSharedCheck_1144_;
                        state = 15;
                        continue;
                    }
                } else {
                    v_a_1145_ = leanh::lean_ctor_get(v___x_1136_, 0);
                    leanh::lean_inc(v_a_1145_);
                    leanh::lean_dec_ref_known(v___x_1136_, 1);
                    if v_isShared_1135_ == 0 {
                        leanh::lean_ctor_set(v___x_1134_, 0, v_a_1145_);
                        v___x_1147_ = v___x_1134_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_1148_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1145_);
                        v___x_1147_ = v_reuseFailAlloc_1148_;
                        state = 17;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_1140_ == 0 {
                    v___x_1142_ = v___x_1139_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1143_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
                    v___x_1142_ = v_reuseFailAlloc_1143_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1142_;
            }
            17 => {
                v_____do__lift_1124_ = v___x_1147_;
                state = 11;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1____boxed(
    mut v_j_1152_: *mut leanh::LeanObject,
    mut v_a_1153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1154_ = l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_(v_j_1152_, v_a_1153_);
    leanh::lean_dec_ref(v_a_1153_);
    return v_res_1154_;
}
pub unsafe fn l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0(
    mut v_x_1161_: *mut leanh::LeanObject,
    mut v_y_1162_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1163_: u8 = 0;
    v___x_1163_ = lean_nat_dec_lt(v_x_1161_, v_y_1162_);
    if v___x_1163_ == 0 {
        let mut v___x_1164_: u8 = 0;
        v___x_1164_ = lean_nat_dec_eq(v_x_1161_, v_y_1162_);
        if v___x_1164_ == 0 {
            let mut v___x_1165_: u8 = 0;
            v___x_1165_ = 2;
            return v___x_1165_;
        } else {
            let mut v___x_1166_: u8 = 0;
            v___x_1166_ = 1;
            return v___x_1166_;
        }
    } else {
        let mut v___x_1167_: u8 = 0;
        v___x_1167_ = 0;
        return v___x_1167_;
    }
}
pub unsafe fn l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0___boxed(
    mut v_x_1168_: *mut leanh::LeanObject,
    mut v_y_1169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1170_: u8 = 0;
    let mut v_r_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1170_ = l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0(v_x_1168_, v_y_1169_);
    leanh::lean_dec(v_y_1169_);
    leanh::lean_dec(v_x_1168_);
    v_r_1171_ = leanh::lean_box((v_res_1170_) as usize);
    return v_r_1171_;
}
pub unsafe fn l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__1(
    mut v___f_1172_: *mut leanh::LeanObject,
    mut v_pm_1173_: *mut leanh::LeanObject,
    mut v_inst_1174_: *mut leanh::LeanObject,
    mut v_merger_1175_: *mut leanh::LeanObject,
    mut v_info_1176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_subexprPos_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_subexprPos_1177_ = leanh::lean_ctor_get(v_info_1176_, 1);
    leanh::lean_inc(v_subexprPos_1177_);
    v___x_1178_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(
        v___f_1172_,
        v_pm_1173_,
        v_subexprPos_1177_,
    );
    if leanh::lean_obj_tag(v___x_1178_) == 0 {
        let mut v_toApplicative_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_merger_1175_);
        v_toApplicative_1179_ = leanh::lean_ctor_get(v_inst_1174_, 0);
        leanh::lean_inc_ref(v_toApplicative_1179_);
        leanh::lean_dec_ref(v_inst_1174_);
        v_toPure_1180_ = leanh::lean_ctor_get(v_toApplicative_1179_, 1);
        leanh::lean_inc(v_toPure_1180_);
        leanh::lean_dec_ref(v_toApplicative_1179_);
        v___x_1181_ =
            leanh::lean_apply_2(v_toPure_1180_, leanh::lean_box(0), v_info_1176_);
        return v___x_1181_;
    } else {
        let mut v_val_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_1174_);
        v_val_1182_ = leanh::lean_ctor_get(v___x_1178_, 0);
        leanh::lean_inc(v_val_1182_);
        leanh::lean_dec_ref_known(v___x_1178_, 1);
        v___x_1183_ = leanh::lean_apply_2(v_merger_1175_, v_info_1176_, v_val_1182_);
        return v___x_1183_;
    }
}
pub unsafe fn l_Lean_Widget_CodeWithInfos_mergePosMap___redArg(
    mut v_inst_1185_: *mut leanh::LeanObject,
    mut v_merger_1186_: *mut leanh::LeanObject,
    mut v_pm_1187_: *mut leanh::LeanObject,
    mut v_tt_1188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_pm_1187_) == 0 {
        let mut v___f_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_1189_ = l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___closed__0;
        leanh::lean_inc_ref(v_inst_1185_);
        v___f_1190_ = leanh::lean_alloc_closure(
            l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_1190_, 0, v___f_1189_);
        leanh::lean_closure_set(v___f_1190_, 1, v_pm_1187_);
        leanh::lean_closure_set(v___f_1190_, 2, v_inst_1185_);
        leanh::lean_closure_set(v___f_1190_, 3, v_merger_1186_);
        v___x_1191_ = l_Lean_Widget_TaggedText_mapM___redArg(v_inst_1185_, v___f_1190_, v_tt_1188_);
        return v___x_1191_;
    } else {
        let mut v_toApplicative_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_merger_1186_);
        v_toApplicative_1192_ = leanh::lean_ctor_get(v_inst_1185_, 0);
        leanh::lean_inc_ref(v_toApplicative_1192_);
        leanh::lean_dec_ref(v_inst_1185_);
        v_toPure_1193_ = leanh::lean_ctor_get(v_toApplicative_1192_, 1);
        leanh::lean_inc(v_toPure_1193_);
        leanh::lean_dec_ref(v_toApplicative_1192_);
        v___x_1194_ =
            leanh::lean_apply_2(v_toPure_1193_, leanh::lean_box(0), v_tt_1188_);
        return v___x_1194_;
    }
}
pub unsafe fn l_Lean_Widget_CodeWithInfos_mergePosMap(
    mut v_m_1195_: *mut leanh::LeanObject,
    mut v_00_u03b1_1196_: *mut leanh::LeanObject,
    mut v_inst_1197_: *mut leanh::LeanObject,
    mut v_merger_1198_: *mut leanh::LeanObject,
    mut v_pm_1199_: *mut leanh::LeanObject,
    mut v_tt_1200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1201_ = l_Lean_Widget_CodeWithInfos_mergePosMap___redArg(
        v_inst_1197_,
        v_merger_1198_,
        v_pm_1199_,
        v_tt_1200_,
    );
    return v___x_1201_;
}
pub unsafe fn l_Lean_Widget_CodeWithInfos_pretty(
    mut v_tt_1202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1203_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_1202_);
    return v___x_1203_;
}
pub unsafe fn l_Lean_Widget_SubexprInfo_withDiffTag(
    mut v_tag_1204_: u8,
    mut v_c_1205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_info_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subexprPos_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1210_: u8 = 0;
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1216_: u8 = 0;
    let mut v_unused_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_info_1206_ = leanh::lean_ctor_get(v_c_1205_, 0);
                v_subexprPos_1207_ = leanh::lean_ctor_get(v_c_1205_, 1);
                v_isSharedCheck_1216_ = (!leanh::lean_is_exclusive(v_c_1205_)) as u8;
                if v_isSharedCheck_1216_ == 0 {
                    v_unused_1217_ = leanh::lean_ctor_get(v_c_1205_, 2);
                    leanh::lean_dec(v_unused_1217_);
                    v___x_1209_ = v_c_1205_;
                    v_isShared_1210_ = v_isSharedCheck_1216_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_subexprPos_1207_);
                    leanh::lean_inc(v_info_1206_);
                    leanh::lean_dec(v_c_1205_);
                    v___x_1209_ = leanh::lean_box(0);
                    v_isShared_1210_ = v_isSharedCheck_1216_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1211_ = leanh::lean_box((v_tag_1204_) as usize);
                v___x_1212_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1212_, 0, v___x_1211_);
                if v_isShared_1210_ == 0 {
                    leanh::lean_ctor_set(v___x_1209_, 2, v___x_1212_);
                    v___x_1214_ = v___x_1209_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1215_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_info_1206_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_subexprPos_1207_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1215_, 2, v___x_1212_);
                    v___x_1214_ = v_reuseFailAlloc_1215_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1214_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_SubexprInfo_withDiffTag___boxed(
    mut v_tag_1218_: *mut leanh::LeanObject,
    mut v_c_1219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tag_boxed_1220_: u8 = 0;
    let mut v_res_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_tag_boxed_1220_ = (leanh::lean_unbox(v_tag_1218_) as u8);
    v_res_1221_ = l_Lean_Widget_SubexprInfo_withDiffTag(v_tag_boxed_1220_, v_c_1219_);
    return v_res_1221_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg(
    mut v_t_1222_: *mut leanh::LeanObject,
    mut v_k_1223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: u8 = 0;
    let mut v___x_1229_: u8 = 0;
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_1222_) == 0 {
                    v_k_1224_ = leanh::lean_ctor_get(v_t_1222_, 1);
                    v_v_1225_ = leanh::lean_ctor_get(v_t_1222_, 2);
                    v_l_1226_ = leanh::lean_ctor_get(v_t_1222_, 3);
                    v_r_1227_ = leanh::lean_ctor_get(v_t_1222_, 4);
                    v___x_1228_ = lean_nat_dec_lt(v_k_1223_, v_k_1224_);
                    if v___x_1228_ == 0 {
                        v___x_1229_ = lean_nat_dec_eq(v_k_1223_, v_k_1224_);
                        if v___x_1229_ == 0 {
                            v_t_1222_ = v_r_1227_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_inc(v_v_1225_);
                            v___x_1231_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1231_, 0, v_v_1225_);
                            return v___x_1231_;
                        }
                    } else {
                        v_t_1222_ = v_l_1226_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_1233_ = leanh::lean_box(0);
                    return v___x_1233_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg___boxed(
    mut v_t_1234_: *mut leanh::LeanObject,
    mut v_k_1235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1236_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg(v_t_1234_, v_k_1235_);
    leanh::lean_dec(v_k_1235_);
    leanh::lean_dec(v_t_1234_);
    return v_res_1236_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg(
    mut v_f_1237_: *mut leanh::LeanObject,
    mut v_sz_1238_: usize,
    mut v_i_1239_: usize,
    mut v_bs_1240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1242_: u8 = 0;
    let mut v_v_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: usize = 0;
    let mut v___x_1248_: usize = 0;
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1242_ = lean_usize_dec_lt(v_i_1239_, v_sz_1238_);
                if v___x_1242_ == 0 {
                    leanh::lean_dec_ref(v_f_1237_);
                    return v_bs_1240_;
                } else {
                    v_v_1243_ = lean_array_uget_borrowed(v_bs_1240_, v_i_1239_);
                    leanh::lean_inc(v_v_1243_);
                    leanh::lean_inc_ref(v_f_1237_);
                    v___x_1244_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(v_f_1237_, v_v_1243_);
                    v___x_1245_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1246_ = lean_array_uset(v_bs_1240_, v_i_1239_, v___x_1245_);
                    v___x_1247_ = 1usize;
                    v___x_1248_ = lean_usize_add(v_i_1239_, v___x_1247_);
                    v___x_1249_ = lean_array_uset(v_bs_x27_1246_, v_i_1239_, v___x_1244_);
                    v_i_1239_ = v___x_1248_;
                    v_bs_1240_ = v___x_1249_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(
    mut v_f_1251_: *mut leanh::LeanObject,
    mut v_x_1252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1257_: u8 = 0;
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1261_: u8 = 0;
    let mut v_a_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1265_: u8 = 0;
    let mut v_sz_1266_: usize = 0;
    let mut v___x_1267_: usize = 0;
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1272_: u8 = 0;
    let mut v_a_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1252_) {
                0 => {
                    leanh::lean_dec_ref(v_f_1251_);
                    v_a_1254_ = leanh::lean_ctor_get(v_x_1252_, 0);
                    v_isSharedCheck_1261_ = (!leanh::lean_is_exclusive(v_x_1252_)) as u8;
                    if v_isSharedCheck_1261_ == 0 {
                        v___x_1256_ = v_x_1252_;
                        v_isShared_1257_ = v_isSharedCheck_1261_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1254_);
                        leanh::lean_dec(v_x_1252_);
                        v___x_1256_ = leanh::lean_box(0);
                        v_isShared_1257_ = v_isSharedCheck_1261_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_1262_ = leanh::lean_ctor_get(v_x_1252_, 0);
                    v_isSharedCheck_1272_ = (!leanh::lean_is_exclusive(v_x_1252_)) as u8;
                    if v_isSharedCheck_1272_ == 0 {
                        v___x_1264_ = v_x_1252_;
                        v_isShared_1265_ = v_isSharedCheck_1272_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1262_);
                        leanh::lean_dec(v_x_1252_);
                        v___x_1264_ = leanh::lean_box(0);
                        v_isShared_1265_ = v_isSharedCheck_1272_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_a_1273_ = leanh::lean_ctor_get(v_x_1252_, 0);
                    leanh::lean_inc(v_a_1273_);
                    v_a_1274_ = leanh::lean_ctor_get(v_x_1252_, 1);
                    leanh::lean_inc_ref(v_a_1274_);
                    leanh::lean_dec_ref_known(v_x_1252_, 2);
                    v___x_1275_ = leanh::lean_apply_3(
                        v_f_1251_,
                        v_a_1273_,
                        v_a_1274_,
                        leanh::lean_box(0),
                    );
                    return v___x_1275_;
                }
            },
            1 => {
                if v_isShared_1257_ == 0 {
                    v___x_1259_ = v___x_1256_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1260_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
                    v___x_1259_ = v_reuseFailAlloc_1260_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1259_;
            }
            3 => {
                v_sz_1266_ = lean_array_size(v_a_1262_);
                v___x_1267_ = 0usize;
                v___x_1268_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg(v_f_1251_, v_sz_1266_, v___x_1267_, v_a_1262_);
                if v_isShared_1265_ == 0 {
                    leanh::lean_ctor_set(v___x_1264_, 0, v___x_1268_);
                    v___x_1270_ = v___x_1264_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1271_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1268_);
                    v___x_1270_ = v_reuseFailAlloc_1271_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1270_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg___boxed(
    mut v_f_1276_: *mut leanh::LeanObject,
    mut v_x_1277_: *mut leanh::LeanObject,
    mut v___y_1278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1279_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(v_f_1276_, v_x_1277_);
    return v_res_1279_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg___boxed(
    mut v_f_1280_: *mut leanh::LeanObject,
    mut v_sz_1281_: *mut leanh::LeanObject,
    mut v_i_1282_: *mut leanh::LeanObject,
    mut v_bs_1283_: *mut leanh::LeanObject,
    mut v___y_1284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1285_: usize = 0;
    let mut v_i_boxed_1286_: usize = 0;
    let mut v_res_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1285_ = leanh::lean_unbox_usize(v_sz_1281_);
    leanh::lean_dec(v_sz_1281_);
    v_i_boxed_1286_ = leanh::lean_unbox_usize(v_i_1282_);
    leanh::lean_dec(v_i_1282_);
    v_res_1287_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg(v_f_1280_, v_sz_boxed_1285_, v_i_boxed_1286_, v_bs_1283_);
    return v_res_1287_;
}
pub unsafe fn _init_l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1288_ = l_Lean_PersistentArray_empty(leanh::lean_box(0));
    return v___x_1288_;
}
pub unsafe fn l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0(
    mut v_infos_1289_: *mut leanh::LeanObject,
    mut v_ctx_1290_: *mut leanh::LeanObject,
    mut v_x_1291_: *mut leanh::LeanObject,
    mut v_subTt_1292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1297_: u8 = 0;
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1310_: u8 = 0;
    let mut v_unused_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1294_ = leanh::lean_ctor_get(v_x_1291_, 0);
                v_isSharedCheck_1310_ = (!leanh::lean_is_exclusive(v_x_1291_)) as u8;
                if v_isSharedCheck_1310_ == 0 {
                    v_unused_1311_ = leanh::lean_ctor_get(v_x_1291_, 1);
                    leanh::lean_dec(v_unused_1311_);
                    v___x_1296_ = v_x_1291_;
                    v_isShared_1297_ = v_isSharedCheck_1310_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_1294_);
                    leanh::lean_dec(v_x_1291_);
                    v___x_1296_ = leanh::lean_box(0);
                    v_isShared_1297_ = v_isSharedCheck_1310_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1298_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg(v_infos_1289_, v_fst_1294_);
                if leanh::lean_obj_tag(v___x_1298_) == 0 {
                    leanh::lean_del_object(v___x_1296_);
                    leanh::lean_dec(v_fst_1294_);
                    v___x_1299_ =
                        l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(
                            v_ctx_1290_,
                            v_infos_1289_,
                            v_subTt_1292_,
                        );
                    return v___x_1299_;
                } else {
                    v_val_1300_ = leanh::lean_ctor_get(v___x_1298_, 0);
                    leanh::lean_inc(v_val_1300_);
                    leanh::lean_dec_ref_known(v___x_1298_, 1);
                    v___x_1301_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0_once), _init_l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0);
                    leanh::lean_inc_ref(v_ctx_1290_);
                    v___x_1302_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1302_, 0, v_ctx_1290_);
                    leanh::lean_ctor_set(v___x_1302_, 1, v_val_1300_);
                    leanh::lean_ctor_set(v___x_1302_, 2, v___x_1301_);
                    v___x_1303_ = l_Lean_Server_WithRpcRef_mk___redArg(v___x_1302_);
                    v___x_1304_ =
                        l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(
                            v_ctx_1290_,
                            v_infos_1289_,
                            v_subTt_1292_,
                        );
                    v___x_1305_ = leanh::lean_box(0);
                    v___x_1306_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1306_, 0, v___x_1303_);
                    leanh::lean_ctor_set(v___x_1306_, 1, v_fst_1294_);
                    leanh::lean_ctor_set(v___x_1306_, 2, v___x_1305_);
                    if v_isShared_1297_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1296_, 2);
                        leanh::lean_ctor_set(v___x_1296_, 1, v___x_1304_);
                        leanh::lean_ctor_set(v___x_1296_, 0, v___x_1306_);
                        v___x_1308_ = v___x_1296_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1309_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1306_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1309_, 1, v___x_1304_);
                        v___x_1308_ = v_reuseFailAlloc_1309_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___boxed(
    mut v_infos_1312_: *mut leanh::LeanObject,
    mut v_ctx_1313_: *mut leanh::LeanObject,
    mut v_x_1314_: *mut leanh::LeanObject,
    mut v_subTt_1315_: *mut leanh::LeanObject,
    mut v___y_1316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1317_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0(
        v_infos_1312_,
        v_ctx_1313_,
        v_x_1314_,
        v_subTt_1315_,
    );
    return v_res_1317_;
}
pub unsafe fn l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(
    mut v_ctx_1318_: *mut leanh::LeanObject,
    mut v_infos_1319_: *mut leanh::LeanObject,
    mut v_tt_1320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1322_ = leanh::lean_alloc_closure(
        l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_1322_, 0, v_infos_1319_);
    leanh::lean_closure_set(v___f_1322_, 1, v_ctx_1318_);
    v___x_1323_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(v___f_1322_, v_tt_1320_);
    return v___x_1323_;
}
pub unsafe fn l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___boxed(
    mut v_ctx_1324_: *mut leanh::LeanObject,
    mut v_infos_1325_: *mut leanh::LeanObject,
    mut v_tt_1326_: *mut leanh::LeanObject,
    mut v_a_1327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1328_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(
        v_ctx_1324_,
        v_infos_1325_,
        v_tt_1326_,
    );
    return v_res_1328_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0(
    mut v_00_u03b4_1329_: *mut leanh::LeanObject,
    mut v_t_1330_: *mut leanh::LeanObject,
    mut v_k_1331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1332_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg(v_t_1330_, v_k_1331_);
    return v___x_1332_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___boxed(
    mut v_00_u03b4_1333_: *mut leanh::LeanObject,
    mut v_t_1334_: *mut leanh::LeanObject,
    mut v_k_1335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1336_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0(v_00_u03b4_1333_, v_t_1334_, v_k_1335_);
    leanh::lean_dec(v_k_1335_);
    leanh::lean_dec(v_t_1334_);
    return v_res_1336_;
}
pub unsafe fn l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1(
    mut v_00_u03b1_1337_: *mut leanh::LeanObject,
    mut v_00_u03b2_1338_: *mut leanh::LeanObject,
    mut v_f_1339_: *mut leanh::LeanObject,
    mut v_x_1340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1342_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(v_f_1339_, v_x_1340_);
    return v___x_1342_;
}
pub unsafe fn l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___boxed(
    mut v_00_u03b1_1343_: *mut leanh::LeanObject,
    mut v_00_u03b2_1344_: *mut leanh::LeanObject,
    mut v_f_1345_: *mut leanh::LeanObject,
    mut v_x_1346_: *mut leanh::LeanObject,
    mut v___y_1347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1348_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1(v_00_u03b1_1343_, v_00_u03b2_1344_, v_f_1345_, v_x_1346_);
    return v_res_1348_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1(
    mut v_00_u03b1_1349_: *mut leanh::LeanObject,
    mut v_00_u03b2_1350_: *mut leanh::LeanObject,
    mut v_f_1351_: *mut leanh::LeanObject,
    mut v_sz_1352_: usize,
    mut v_i_1353_: usize,
    mut v_bs_1354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg(v_f_1351_, v_sz_1352_, v_i_1353_, v_bs_1354_);
    return v___x_1356_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___boxed(
    mut v_00_u03b1_1357_: *mut leanh::LeanObject,
    mut v_00_u03b2_1358_: *mut leanh::LeanObject,
    mut v_f_1359_: *mut leanh::LeanObject,
    mut v_sz_1360_: *mut leanh::LeanObject,
    mut v_i_1361_: *mut leanh::LeanObject,
    mut v_bs_1362_: *mut leanh::LeanObject,
    mut v___y_1363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1364_: usize = 0;
    let mut v_i_boxed_1365_: usize = 0;
    let mut v_res_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1364_ = leanh::lean_unbox_usize(v_sz_1360_);
    leanh::lean_dec(v_sz_1360_);
    v_i_boxed_1365_ = leanh::lean_unbox_usize(v_i_1361_);
    leanh::lean_dec(v_i_1361_);
    v_res_1366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1(v_00_u03b1_1357_, v_00_u03b2_1358_, v_f_1359_, v_sz_boxed_1364_, v_i_boxed_1365_, v_bs_1362_);
    return v_res_1366_;
}
pub unsafe fn l_Lean_Widget_tagCodeInfos(
    mut v_ctx_1367_: *mut leanh::LeanObject,
    mut v_infos_1368_: *mut leanh::LeanObject,
    mut v_tt_1369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1371_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(
        v_ctx_1367_,
        v_infos_1368_,
        v_tt_1369_,
    );
    return v___x_1371_;
}
pub unsafe fn l_Lean_Widget_tagCodeInfos___boxed(
    mut v_ctx_1372_: *mut leanh::LeanObject,
    mut v_infos_1373_: *mut leanh::LeanObject,
    mut v_tt_1374_: *mut leanh::LeanObject,
    mut v_a_1375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1376_ = l_Lean_Widget_tagCodeInfos(v_ctx_1372_, v_infos_1373_, v_tt_1374_);
    return v_res_1376_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0(
    mut v_opts_1377_: *mut leanh::LeanObject,
    mut v_opt_1378_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1379_ = leanh::lean_ctor_get(v_opt_1378_, 0);
    v_defValue_1380_ = leanh::lean_ctor_get(v_opt_1378_, 1);
    v_map_1381_ = leanh::lean_ctor_get(v_opts_1377_, 0);
    v___x_1382_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1381_,
            v_name_1379_,
        );
    if leanh::lean_obj_tag(v___x_1382_) == 0 {
        let mut v___x_1383_: u8 = 0;
        v___x_1383_ = (leanh::lean_unbox(v_defValue_1380_) as u8);
        return v___x_1383_;
    } else {
        let mut v_val_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1384_ = leanh::lean_ctor_get(v___x_1382_, 0);
        leanh::lean_inc(v_val_1384_);
        leanh::lean_dec_ref_known(v___x_1382_, 1);
        if leanh::lean_obj_tag(v_val_1384_) == 1 {
            let mut v_v_1385_: u8 = 0;
            v_v_1385_ = leanh::lean_ctor_get_uint8(v_val_1384_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_1384_, 0);
            return v_v_1385_;
        } else {
            let mut v___x_1386_: u8 = 0;
            leanh::lean_dec(v_val_1384_);
            v___x_1386_ = (leanh::lean_unbox(v_defValue_1380_) as u8);
            return v___x_1386_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0___boxed(
    mut v_opts_1387_: *mut leanh::LeanObject,
    mut v_opt_1388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1389_: u8 = 0;
    let mut v_r_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1389_ =
        l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0(v_opts_1387_, v_opt_1388_);
    leanh::lean_dec_ref(v_opt_1388_);
    leanh::lean_dec_ref(v_opts_1387_);
    v_r_1390_ = leanh::lean_box((v_res_1389_) as usize);
    return v_r_1390_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg(
    mut v_e_1391_: *mut leanh::LeanObject,
    mut v___y_1392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1394_: u8 = 0;
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1408_: u8 = 0;
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1414_: u8 = 0;
    let mut v_unused_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1394_ = l_Lean_Expr_hasMVar(v_e_1391_);
                if v___x_1394_ == 0 {
                    v___x_1395_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1395_, 0, v_e_1391_);
                    return v___x_1395_;
                } else {
                    v___x_1396_ = lean_st_ref_get(v___y_1392_);
                    v_mctx_1397_ = leanh::lean_ctor_get(v___x_1396_, 0);
                    leanh::lean_inc_ref(v_mctx_1397_);
                    leanh::lean_dec(v___x_1396_);
                    v___x_1398_ = l_Lean_instantiateMVarsCore(v_mctx_1397_, v_e_1391_);
                    v_fst_1399_ = leanh::lean_ctor_get(v___x_1398_, 0);
                    leanh::lean_inc(v_fst_1399_);
                    v_snd_1400_ = leanh::lean_ctor_get(v___x_1398_, 1);
                    leanh::lean_inc(v_snd_1400_);
                    leanh::lean_dec_ref(v___x_1398_);
                    v___x_1401_ = lean_st_ref_take(v___y_1392_);
                    v_cache_1402_ = leanh::lean_ctor_get(v___x_1401_, 1);
                    v_zetaDeltaFVarIds_1403_ = leanh::lean_ctor_get(v___x_1401_, 2);
                    v_postponed_1404_ = leanh::lean_ctor_get(v___x_1401_, 3);
                    v_diag_1405_ = leanh::lean_ctor_get(v___x_1401_, 4);
                    v_isSharedCheck_1414_ = (!leanh::lean_is_exclusive(v___x_1401_)) as u8;
                    if v_isSharedCheck_1414_ == 0 {
                        v_unused_1415_ = leanh::lean_ctor_get(v___x_1401_, 0);
                        leanh::lean_dec(v_unused_1415_);
                        v___x_1407_ = v___x_1401_;
                        v_isShared_1408_ = v_isSharedCheck_1414_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_1405_);
                        leanh::lean_inc(v_postponed_1404_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_1403_);
                        leanh::lean_inc(v_cache_1402_);
                        leanh::lean_dec(v___x_1401_);
                        v___x_1407_ = leanh::lean_box(0);
                        v_isShared_1408_ = v_isSharedCheck_1414_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1408_ == 0 {
                    leanh::lean_ctor_set(v___x_1407_, 0, v_snd_1400_);
                    v___x_1410_ = v___x_1407_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1413_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_snd_1400_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_cache_1402_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1413_,
                        2,
                        v_zetaDeltaFVarIds_1403_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1413_, 3, v_postponed_1404_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1413_, 4, v_diag_1405_);
                    v___x_1410_ = v_reuseFailAlloc_1413_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1411_ = lean_st_ref_set(v___y_1392_, v___x_1410_);
                v___x_1412_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1412_, 0, v_fst_1399_);
                return v___x_1412_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg___boxed(
    mut v_e_1416_: *mut leanh::LeanObject,
    mut v___y_1417_: *mut leanh::LeanObject,
    mut v___y_1418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1419_ = l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg(
        v_e_1416_,
        v___y_1417_,
    );
    leanh::lean_dec(v___y_1417_);
    return v_res_1419_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1(
    mut v_e_1420_: *mut leanh::LeanObject,
    mut v___y_1421_: *mut leanh::LeanObject,
    mut v___y_1422_: *mut leanh::LeanObject,
    mut v___y_1423_: *mut leanh::LeanObject,
    mut v___y_1424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1426_ = l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg(
        v_e_1420_,
        v___y_1422_,
    );
    return v___x_1426_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___boxed(
    mut v_e_1427_: *mut leanh::LeanObject,
    mut v___y_1428_: *mut leanh::LeanObject,
    mut v___y_1429_: *mut leanh::LeanObject,
    mut v___y_1430_: *mut leanh::LeanObject,
    mut v___y_1431_: *mut leanh::LeanObject,
    mut v___y_1432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1433_ = l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1(
        v_e_1427_,
        v___y_1428_,
        v___y_1429_,
        v___y_1430_,
        v___y_1431_,
    );
    leanh::lean_dec(v___y_1431_);
    leanh::lean_dec_ref(v___y_1430_);
    leanh::lean_dec(v___y_1429_);
    leanh::lean_dec_ref(v___y_1428_);
    return v_res_1433_;
}
pub unsafe fn l_Lean_Widget_ppExprTagged(
    mut v_e_1436_: *mut leanh::LeanObject,
    mut v_delab_1437_: *mut leanh::LeanObject,
    mut v_a_1438_: *mut leanh::LeanObject,
    mut v_a_1439_: *mut leanh::LeanObject,
    mut v_a_1440_: *mut leanh::LeanObject,
    mut v_a_1441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_e_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: u8 = 0;
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1458_: u8 = 0;
    let mut v_fmt_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infos_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1479_: u8 = 0;
    let mut v_a_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1483_: u8 = 0;
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1487_: u8 = 0;
    let mut v___x_1488_: u8 = 0;
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1448_ = leanh::lean_ctor_get(v_a_1440_, 2);
                v_currNamespace_1449_ = leanh::lean_ctor_get(v_a_1440_, 6);
                v_openDecls_1450_ = leanh::lean_ctor_get(v_a_1440_, 7);
                v___x_1451_ = l_Lean_pp_raw;
                v___x_1452_ = l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0(
                    v_options_1448_,
                    v___x_1451_,
                );
                if v___x_1452_ == 0 {
                    v___x_1453_ = leanh::lean_box(1);
                    v___x_1454_ = l_Lean_PrettyPrinter_ppExprWithInfos(
                        v_e_1436_,
                        v___x_1453_,
                        v_delab_1437_,
                        v_a_1438_,
                        v_a_1439_,
                        v_a_1440_,
                        v_a_1441_,
                    );
                    if leanh::lean_obj_tag(v___x_1454_) == 0 {
                        v_a_1455_ = leanh::lean_ctor_get(v___x_1454_, 0);
                        v_isSharedCheck_1479_ =
                            (!leanh::lean_is_exclusive(v___x_1454_)) as u8;
                        if v_isSharedCheck_1479_ == 0 {
                            v___x_1457_ = v___x_1454_;
                            v_isShared_1458_ = v_isSharedCheck_1479_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1455_);
                            leanh::lean_dec(v___x_1454_);
                            v___x_1457_ = leanh::lean_box(0);
                            v_isShared_1458_ = v_isSharedCheck_1479_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1480_ = leanh::lean_ctor_get(v___x_1454_, 0);
                        v_isSharedCheck_1487_ =
                            (!leanh::lean_is_exclusive(v___x_1454_)) as u8;
                        if v_isSharedCheck_1487_ == 0 {
                            v___x_1482_ = v___x_1454_;
                            v_isShared_1483_ = v_isSharedCheck_1487_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1480_);
                            leanh::lean_dec(v___x_1454_);
                            v___x_1482_ = leanh::lean_box(0);
                            v_isShared_1483_ = v_isSharedCheck_1487_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_delab_1437_);
                    v___x_1488_ = l_Lean_getPPInstantiateMVars(v_options_1448_);
                    if v___x_1488_ == 0 {
                        v_e_1444_ = v_e_1436_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1489_ = l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg(v_e_1436_, v_a_1439_);
                        v_a_1490_ = leanh::lean_ctor_get(v___x_1489_, 0);
                        leanh::lean_inc(v_a_1490_);
                        leanh::lean_dec_ref(v___x_1489_);
                        v_e_1444_ = v_a_1490_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1445_ = lean_expr_dbg_to_string(v_e_1444_);
                leanh::lean_dec_ref(v_e_1444_);
                v___x_1446_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1446_, 0, v___x_1445_);
                v___x_1447_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1447_, 0, v___x_1446_);
                return v___x_1447_;
            }
            2 => {
                v_fmt_1459_ = leanh::lean_ctor_get(v_a_1455_, 0);
                leanh::lean_inc(v_fmt_1459_);
                v_infos_1460_ = leanh::lean_ctor_get(v_a_1455_, 1);
                leanh::lean_inc(v_infos_1460_);
                leanh::lean_dec(v_a_1455_);
                v___x_1461_ = lean_st_ref_get(v_a_1441_);
                v___x_1462_ = lean_st_ref_get(v_a_1439_);
                v___x_1463_ = lean_st_ref_get(v_a_1441_);
                v_env_1464_ = leanh::lean_ctor_get(v___x_1461_, 0);
                leanh::lean_inc_ref(v_env_1464_);
                leanh::lean_dec(v___x_1461_);
                v_mctx_1465_ = leanh::lean_ctor_get(v___x_1462_, 0);
                leanh::lean_inc_ref(v_mctx_1465_);
                leanh::lean_dec(v___x_1462_);
                v_ngen_1466_ = leanh::lean_ctor_get(v___x_1463_, 2);
                leanh::lean_inc_ref(v_ngen_1466_);
                leanh::lean_dec(v___x_1463_);
                v___x_1467_ = leanh::lean_unsigned_to_nat(0);
                v___x_1468_ = l_Std_Format_defWidth;
                v___x_1469_ =
                    l_Lean_Widget_TaggedText_prettyTagged(v_fmt_1459_, v___x_1467_, v___x_1468_);
                v___x_1470_ = leanh::lean_box(0);
                v___x_1471_ = l_Lean_instInhabitedFileMap_default;
                leanh::lean_inc(v_openDecls_1450_);
                leanh::lean_inc(v_currNamespace_1449_);
                leanh::lean_inc_ref(v_options_1448_);
                v___x_1472_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                leanh::lean_ctor_set(v___x_1472_, 0, v_env_1464_);
                leanh::lean_ctor_set(v___x_1472_, 1, v___x_1470_);
                leanh::lean_ctor_set(v___x_1472_, 2, v___x_1471_);
                leanh::lean_ctor_set(v___x_1472_, 3, v_mctx_1465_);
                leanh::lean_ctor_set(v___x_1472_, 4, v_options_1448_);
                leanh::lean_ctor_set(v___x_1472_, 5, v_currNamespace_1449_);
                leanh::lean_ctor_set(v___x_1472_, 6, v_openDecls_1450_);
                leanh::lean_ctor_set(v___x_1472_, 7, v_ngen_1466_);
                v___x_1473_ = l_Lean_Widget_ppExprTagged___closed__0;
                v___x_1474_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1474_, 0, v___x_1472_);
                leanh::lean_ctor_set(v___x_1474_, 1, v___x_1470_);
                leanh::lean_ctor_set(v___x_1474_, 2, v___x_1473_);
                v___x_1475_ =
                    l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(
                        v___x_1474_,
                        v_infos_1460_,
                        v___x_1469_,
                    );
                if v_isShared_1458_ == 0 {
                    leanh::lean_ctor_set(v___x_1457_, 0, v___x_1475_);
                    v___x_1477_ = v___x_1457_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1478_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1475_);
                    v___x_1477_ = v_reuseFailAlloc_1478_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1477_;
            }
            4 => {
                if v_isShared_1483_ == 0 {
                    v___x_1485_ = v___x_1482_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1486_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
                    v___x_1485_ = v_reuseFailAlloc_1486_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1485_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_ppExprTagged___boxed(
    mut v_e_1491_: *mut leanh::LeanObject,
    mut v_delab_1492_: *mut leanh::LeanObject,
    mut v_a_1493_: *mut leanh::LeanObject,
    mut v_a_1494_: *mut leanh::LeanObject,
    mut v_a_1495_: *mut leanh::LeanObject,
    mut v_a_1496_: *mut leanh::LeanObject,
    mut v_a_1497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1498_ = l_Lean_Widget_ppExprTagged(
        v_e_1491_,
        v_delab_1492_,
        v_a_1493_,
        v_a_1494_,
        v_a_1495_,
        v_a_1496_,
    );
    leanh::lean_dec(v_a_1496_);
    leanh::lean_dec_ref(v_a_1495_);
    leanh::lean_dec(v_a_1494_);
    leanh::lean_dec_ref(v_a_1493_);
    return v_res_1498_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Widget_InteractiveCode(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Widget_TaggedText(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Widget_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Widget_InteractiveCode(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Widget_InteractiveCode(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Widget_TaggedText(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Widget_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Widget_InteractiveCode(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Widget_InteractiveCode(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Widget_InteractiveCode(builtin);
}