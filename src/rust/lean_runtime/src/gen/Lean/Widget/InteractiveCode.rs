// Lean compiler output
// Module: Lean.Widget.InteractiveCode
// Imports: Lean.Widget.TaggedText Lean.Widget.Basic
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_to_list, lean_nat_dec_eq, lean_nat_dec_lt, lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_dbg_to_string;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__0_value:
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
    m_data: [119, 97, 115, 67, 104, 97, 110, 103, 101, 100, 0],
};
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__2_value:
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
    m_data: [119, 105, 108, 108, 67, 104, 97, 110, 103, 101, 0],
};
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__3_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__4_value:
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
    m_data: [119, 97, 115, 68, 101, 108, 101, 116, 101, 100, 0],
};
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__5_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__6_value:
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
    m_data: [119, 105, 108, 108, 68, 101, 108, 101, 116, 101, 0],
};
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__7_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__8_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__9_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__10_value:
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
    m_data: [119, 105, 108, 108, 73, 110, 115, 101, 114, 116, 0],
};
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag_toJson___closed__11_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instToJsonDiffTag_toJson___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag_toJson___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instToJsonDiffTag___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Widget_instToJsonDiffTag_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Widget_instToJsonDiffTag___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_instToJsonDiffTag: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instToJsonDiffTag___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__0_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__2_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__4_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__6_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__7_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__8_value:
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
static mut l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__9_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((5 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonDiffTag___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Widget_instFromJsonDiffTag_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Widget_instFromJsonDiffTag___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_instFromJsonDiffTag: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instFromJsonDiffTag___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [105, 110, 102, 111, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 117, 98, 101, 120, 112, 114, 80, 111, 115, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 105, 102, 102, 83, 116, 97, 116, 117, 115, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_instToJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableSubexprInfo___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableSubexprInfo_enc_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableSubexprInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableSubexprInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableSubexprInfo___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableSubexprInfo___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableSubexprInfo___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableSubexprInfo___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableSubexprInfo___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableSubexprInfo___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instRpcEncodableSubexprInfo___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableSubexprInfo___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_instRpcEncodableSubexprInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableSubexprInfo___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___closed__0_value:
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
    m_fun: l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Widget_ppExprTagged___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Widget_ppExprTagged___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_ppExprTagged___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Widget_DiffTag_ctorIdx(mut v_x_750_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_750_ {
        0 => {
            let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_751_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_751_;
        }
        1 => {
            let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_752_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_752_;
        }
        2 => {
            let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_753_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_753_;
        }
        3 => {
            let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_754_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_754_;
        }
        4 => {
            let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_755_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_755_;
        }
        _ => {
            let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_756_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_756_;
        }
    }
}
pub unsafe fn l_Lean_Widget_DiffTag_ctorIdx___boxed(
    mut v_x_757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_758_: u8 = 0;
    let mut v_res_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_758_ = (crate::leanh::lean_unbox(v_x_757_) as u8);
    v_res_759_ = l_Lean_Widget_DiffTag_ctorIdx(v_x_boxed_758_);
    return v_res_759_;
}
pub unsafe fn l_Lean_Widget_DiffTag_toCtorIdx(mut v_x_760_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_761_ = l_Lean_Widget_DiffTag_ctorIdx(v_x_760_);
    return v___x_761_;
}
pub unsafe fn l_Lean_Widget_DiffTag_toCtorIdx___boxed(
    mut v_x_762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_763_: u8 = 0;
    let mut v_res_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_763_ = (crate::leanh::lean_unbox(v_x_762_) as u8);
    v_res_764_ = l_Lean_Widget_DiffTag_toCtorIdx(v_x_4__boxed_763_);
    return v_res_764_;
}
pub unsafe fn l_Lean_Widget_DiffTag_ctorElim___redArg(
    mut v_k_765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_765_);
    return v_k_765_;
}
pub unsafe fn l_Lean_Widget_DiffTag_ctorElim___redArg___boxed(
    mut v_k_766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_767_ = l_Lean_Widget_DiffTag_ctorElim___redArg(v_k_766_);
    crate::leanh::lean_dec(v_k_766_);
    return v_res_767_;
}
pub unsafe fn l_Lean_Widget_DiffTag_ctorElim(
    mut v_motive_768_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_769_: *mut crate::leanh::LeanObject,
    mut v_t_770_: u8,
    mut v_h_771_: *mut crate::leanh::LeanObject,
    mut v_k_772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_772_);
    return v_k_772_;
}
pub unsafe fn l_Lean_Widget_DiffTag_ctorElim___boxed(
    mut v_motive_773_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_774_: *mut crate::leanh::LeanObject,
    mut v_t_775_: *mut crate::leanh::LeanObject,
    mut v_h_776_: *mut crate::leanh::LeanObject,
    mut v_k_777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_778_: u8 = 0;
    let mut v_res_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_778_ = (crate::leanh::lean_unbox(v_t_775_) as u8);
    v_res_779_ = l_Lean_Widget_DiffTag_ctorElim(
        v_motive_773_,
        v_ctorIdx_774_,
        v_t_boxed_778_,
        v_h_776_,
        v_k_777_,
    );
    crate::leanh::lean_dec(v_k_777_);
    crate::leanh::lean_dec(v_ctorIdx_774_);
    return v_res_779_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasChanged_elim___redArg(
    mut v_wasChanged_780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_wasChanged_780_);
    return v_wasChanged_780_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasChanged_elim___redArg___boxed(
    mut v_wasChanged_781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_782_ = l_Lean_Widget_DiffTag_wasChanged_elim___redArg(v_wasChanged_781_);
    crate::leanh::lean_dec(v_wasChanged_781_);
    return v_res_782_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasChanged_elim(
    mut v_motive_783_: *mut crate::leanh::LeanObject,
    mut v_t_784_: u8,
    mut v_h_785_: *mut crate::leanh::LeanObject,
    mut v_wasChanged_786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_wasChanged_786_);
    return v_wasChanged_786_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasChanged_elim___boxed(
    mut v_motive_787_: *mut crate::leanh::LeanObject,
    mut v_t_788_: *mut crate::leanh::LeanObject,
    mut v_h_789_: *mut crate::leanh::LeanObject,
    mut v_wasChanged_790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_791_: u8 = 0;
    let mut v_res_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_791_ = (crate::leanh::lean_unbox(v_t_788_) as u8);
    v_res_792_ = l_Lean_Widget_DiffTag_wasChanged_elim(
        v_motive_787_,
        v_t_boxed_791_,
        v_h_789_,
        v_wasChanged_790_,
    );
    crate::leanh::lean_dec(v_wasChanged_790_);
    return v_res_792_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willChange_elim___redArg(
    mut v_willChange_793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_willChange_793_);
    return v_willChange_793_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willChange_elim___redArg___boxed(
    mut v_willChange_794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_795_ = l_Lean_Widget_DiffTag_willChange_elim___redArg(v_willChange_794_);
    crate::leanh::lean_dec(v_willChange_794_);
    return v_res_795_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willChange_elim(
    mut v_motive_796_: *mut crate::leanh::LeanObject,
    mut v_t_797_: u8,
    mut v_h_798_: *mut crate::leanh::LeanObject,
    mut v_willChange_799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_willChange_799_);
    return v_willChange_799_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willChange_elim___boxed(
    mut v_motive_800_: *mut crate::leanh::LeanObject,
    mut v_t_801_: *mut crate::leanh::LeanObject,
    mut v_h_802_: *mut crate::leanh::LeanObject,
    mut v_willChange_803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_804_: u8 = 0;
    let mut v_res_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_804_ = (crate::leanh::lean_unbox(v_t_801_) as u8);
    v_res_805_ = l_Lean_Widget_DiffTag_willChange_elim(
        v_motive_800_,
        v_t_boxed_804_,
        v_h_802_,
        v_willChange_803_,
    );
    crate::leanh::lean_dec(v_willChange_803_);
    return v_res_805_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasDeleted_elim___redArg(
    mut v_wasDeleted_806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_wasDeleted_806_);
    return v_wasDeleted_806_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasDeleted_elim___redArg___boxed(
    mut v_wasDeleted_807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_808_ = l_Lean_Widget_DiffTag_wasDeleted_elim___redArg(v_wasDeleted_807_);
    crate::leanh::lean_dec(v_wasDeleted_807_);
    return v_res_808_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasDeleted_elim(
    mut v_motive_809_: *mut crate::leanh::LeanObject,
    mut v_t_810_: u8,
    mut v_h_811_: *mut crate::leanh::LeanObject,
    mut v_wasDeleted_812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_wasDeleted_812_);
    return v_wasDeleted_812_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasDeleted_elim___boxed(
    mut v_motive_813_: *mut crate::leanh::LeanObject,
    mut v_t_814_: *mut crate::leanh::LeanObject,
    mut v_h_815_: *mut crate::leanh::LeanObject,
    mut v_wasDeleted_816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_817_: u8 = 0;
    let mut v_res_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_817_ = (crate::leanh::lean_unbox(v_t_814_) as u8);
    v_res_818_ = l_Lean_Widget_DiffTag_wasDeleted_elim(
        v_motive_813_,
        v_t_boxed_817_,
        v_h_815_,
        v_wasDeleted_816_,
    );
    crate::leanh::lean_dec(v_wasDeleted_816_);
    return v_res_818_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willDelete_elim___redArg(
    mut v_willDelete_819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_willDelete_819_);
    return v_willDelete_819_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willDelete_elim___redArg___boxed(
    mut v_willDelete_820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_821_ = l_Lean_Widget_DiffTag_willDelete_elim___redArg(v_willDelete_820_);
    crate::leanh::lean_dec(v_willDelete_820_);
    return v_res_821_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willDelete_elim(
    mut v_motive_822_: *mut crate::leanh::LeanObject,
    mut v_t_823_: u8,
    mut v_h_824_: *mut crate::leanh::LeanObject,
    mut v_willDelete_825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_willDelete_825_);
    return v_willDelete_825_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willDelete_elim___boxed(
    mut v_motive_826_: *mut crate::leanh::LeanObject,
    mut v_t_827_: *mut crate::leanh::LeanObject,
    mut v_h_828_: *mut crate::leanh::LeanObject,
    mut v_willDelete_829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_830_: u8 = 0;
    let mut v_res_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_830_ = (crate::leanh::lean_unbox(v_t_827_) as u8);
    v_res_831_ = l_Lean_Widget_DiffTag_willDelete_elim(
        v_motive_826_,
        v_t_boxed_830_,
        v_h_828_,
        v_willDelete_829_,
    );
    crate::leanh::lean_dec(v_willDelete_829_);
    return v_res_831_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasInserted_elim___redArg(
    mut v_wasInserted_832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_wasInserted_832_);
    return v_wasInserted_832_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasInserted_elim___redArg___boxed(
    mut v_wasInserted_833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_834_ = l_Lean_Widget_DiffTag_wasInserted_elim___redArg(v_wasInserted_833_);
    crate::leanh::lean_dec(v_wasInserted_833_);
    return v_res_834_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasInserted_elim(
    mut v_motive_835_: *mut crate::leanh::LeanObject,
    mut v_t_836_: u8,
    mut v_h_837_: *mut crate::leanh::LeanObject,
    mut v_wasInserted_838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_wasInserted_838_);
    return v_wasInserted_838_;
}
pub unsafe fn l_Lean_Widget_DiffTag_wasInserted_elim___boxed(
    mut v_motive_839_: *mut crate::leanh::LeanObject,
    mut v_t_840_: *mut crate::leanh::LeanObject,
    mut v_h_841_: *mut crate::leanh::LeanObject,
    mut v_wasInserted_842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_843_: u8 = 0;
    let mut v_res_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_843_ = (crate::leanh::lean_unbox(v_t_840_) as u8);
    v_res_844_ = l_Lean_Widget_DiffTag_wasInserted_elim(
        v_motive_839_,
        v_t_boxed_843_,
        v_h_841_,
        v_wasInserted_842_,
    );
    crate::leanh::lean_dec(v_wasInserted_842_);
    return v_res_844_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willInsert_elim___redArg(
    mut v_willInsert_845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_willInsert_845_);
    return v_willInsert_845_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willInsert_elim___redArg___boxed(
    mut v_willInsert_846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_847_ = l_Lean_Widget_DiffTag_willInsert_elim___redArg(v_willInsert_846_);
    crate::leanh::lean_dec(v_willInsert_846_);
    return v_res_847_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willInsert_elim(
    mut v_motive_848_: *mut crate::leanh::LeanObject,
    mut v_t_849_: u8,
    mut v_h_850_: *mut crate::leanh::LeanObject,
    mut v_willInsert_851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_willInsert_851_);
    return v_willInsert_851_;
}
pub unsafe fn l_Lean_Widget_DiffTag_willInsert_elim___boxed(
    mut v_motive_852_: *mut crate::leanh::LeanObject,
    mut v_t_853_: *mut crate::leanh::LeanObject,
    mut v_h_854_: *mut crate::leanh::LeanObject,
    mut v_willInsert_855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_856_: u8 = 0;
    let mut v_res_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_856_ = (crate::leanh::lean_unbox(v_t_853_) as u8);
    v_res_857_ = l_Lean_Widget_DiffTag_willInsert_elim(
        v_motive_852_,
        v_t_boxed_856_,
        v_h_854_,
        v_willInsert_855_,
    );
    crate::leanh::lean_dec(v_willInsert_855_);
    return v_res_857_;
}
pub unsafe fn l_Lean_Widget_instToJsonDiffTag_toJson(
    mut v_x_876_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_876_ {
        0 => {
            let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_877_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__1;
            return v___x_877_;
        }
        1 => {
            let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_878_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__3;
            return v___x_878_;
        }
        2 => {
            let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_879_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__5;
            return v___x_879_;
        }
        3 => {
            let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_880_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__7;
            return v___x_880_;
        }
        4 => {
            let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_881_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__9;
            return v___x_881_;
        }
        _ => {
            let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_882_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__11;
            return v___x_882_;
        }
    }
}
pub unsafe fn l_Lean_Widget_instToJsonDiffTag_toJson___boxed(
    mut v_x_883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_130__boxed_884_: u8 = 0;
    let mut v_res_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_130__boxed_884_ = (crate::leanh::lean_unbox(v_x_883_) as u8);
    v_res_885_ = l_Lean_Widget_instToJsonDiffTag_toJson(v_x_130__boxed_884_);
    return v_res_885_;
}
pub unsafe fn l_Lean_Widget_instFromJsonDiffTag_fromJson(
    mut v_json_912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_913_ = l_Lean_Json_getTag_x3f(v_json_912_);
    if crate::leanh::lean_obj_tag(v___x_913_) == 0 {
        let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_914_ = l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__1;
        return v___x_914_;
    } else {
        let mut v_val_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_917_: u8 = 0;
        v_val_915_ = crate::leanh::lean_ctor_get(v___x_913_, 0);
        crate::leanh::lean_inc(v_val_915_);
        crate::leanh::lean_dec_ref_known(v___x_913_, 1);
        v___x_916_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__10;
        v___x_917_ = lean_string_dec_eq(v_val_915_, v___x_916_);
        if v___x_917_ == 0 {
            let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_919_: u8 = 0;
            v___x_918_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__0;
            v___x_919_ = lean_string_dec_eq(v_val_915_, v___x_918_);
            if v___x_919_ == 0 {
                let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_921_: u8 = 0;
                v___x_920_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__2;
                v___x_921_ = lean_string_dec_eq(v_val_915_, v___x_920_);
                if v___x_921_ == 0 {
                    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_923_: u8 = 0;
                    v___x_922_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__4;
                    v___x_923_ = lean_string_dec_eq(v_val_915_, v___x_922_);
                    if v___x_923_ == 0 {
                        let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_925_: u8 = 0;
                        v___x_924_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__6;
                        v___x_925_ = lean_string_dec_eq(v_val_915_, v___x_924_);
                        if v___x_925_ == 0 {
                            let mut v___x_926_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_927_: u8 = 0;
                            v___x_926_ = l_Lean_Widget_instToJsonDiffTag_toJson___closed__8;
                            v___x_927_ = lean_string_dec_eq(v_val_915_, v___x_926_);
                            crate::leanh::lean_dec(v_val_915_);
                            if v___x_927_ == 0 {
                                let mut v___x_928_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                v___x_928_ = l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__3;
                                return v___x_928_;
                            } else {
                                let mut v___x_929_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                v___x_929_ = l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__4;
                                return v___x_929_;
                            }
                        } else {
                            let mut v___x_930_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v_val_915_);
                            v___x_930_ = l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__5;
                            return v___x_930_;
                        }
                    } else {
                        let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v_val_915_);
                        v___x_931_ = l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__6;
                        return v___x_931_;
                    }
                } else {
                    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_val_915_);
                    v___x_932_ = l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__7;
                    return v___x_932_;
                }
            } else {
                let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_val_915_);
                v___x_933_ = l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__8;
                return v___x_933_;
            }
        } else {
            let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_val_915_);
            v___x_934_ = l_Lean_Widget_instFromJsonDiffTag_fromJson___closed__9;
            return v___x_934_;
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0(
    mut v_j_937_: *mut crate::leanh::LeanObject,
    mut v_k_938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_939_ = l_Lean_Json_getObjValD(v_j_937_, v_k_938_);
    v___x_940_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_940_, 0, v___x_939_);
    return v___x_940_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0___boxed(
    mut v_j_941_: *mut crate::leanh::LeanObject,
    mut v_k_942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_943_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0(v_j_941_, v_k_942_);
    crate::leanh::lean_dec_ref(v_k_942_);
    return v_res_943_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1(
    mut v_x_946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_946_) == 0 {
        let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_947_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1___closed__0;
        return v___x_947_;
    } else {
        let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_948_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_948_, 0, v_x_946_);
        v___x_949_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_949_, 0, v___x_948_);
        return v___x_949_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1(
    mut v_j_950_: *mut crate::leanh::LeanObject,
    mut v_k_951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_952_ = l_Lean_Json_getObjValD(v_j_950_, v_k_951_);
    v___x_953_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1_spec__1(v___x_952_);
    return v___x_953_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1___boxed(
    mut v_j_954_: *mut crate::leanh::LeanObject,
    mut v_k_955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_956_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1(v_j_954_, v_k_955_);
    crate::leanh::lean_dec_ref(v_k_955_);
    return v_res_956_;
}
pub unsafe fn l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_(
    mut v_json_960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_972_: u8 = 0;
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_977_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_961_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_;
                crate::leanh::lean_inc_n(v_json_960_, 2);
                v___x_962_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0(v_json_960_, v___x_961_);
                v_a_963_ = crate::leanh::lean_ctor_get(v___x_962_, 0);
                crate::leanh::lean_inc(v_a_963_);
                crate::leanh::lean_dec_ref(v___x_962_);
                v___x_964_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_;
                v___x_965_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__0(v_json_960_, v___x_964_);
                v_a_966_ = crate::leanh::lean_ctor_get(v___x_965_, 0);
                crate::leanh::lean_inc(v_a_966_);
                crate::leanh::lean_dec_ref(v___x_965_);
                v___x_967_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_;
                v___x_968_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15__spec__1(v_json_960_, v___x_967_);
                v_a_969_ = crate::leanh::lean_ctor_get(v___x_968_, 0);
                v_isSharedCheck_977_ = (!crate::leanh::lean_is_exclusive(v___x_968_)) as u8;
                if v_isSharedCheck_977_ == 0 {
                    v___x_971_ = v___x_968_;
                    v_isShared_972_ = v_isSharedCheck_977_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_969_);
                    crate::leanh::lean_dec(v___x_968_);
                    v___x_971_ = crate::leanh::lean_box(0);
                    v_isShared_972_ = v_isSharedCheck_977_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_973_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_973_, 0, v_a_963_);
                crate::leanh::lean_ctor_set(v___x_973_, 1, v_a_966_);
                crate::leanh::lean_ctor_set(v___x_973_, 2, v_a_969_);
                if v_isShared_972_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_971_, 0, v___x_973_);
                    v___x_975_ = v___x_971_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_976_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
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
    mut v_k_980_: *mut crate::leanh::LeanObject,
    mut v_x_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_981_) == 0 {
        let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_980_);
        v___x_982_ = crate::leanh::lean_box(0);
        return v___x_982_;
    } else {
        let mut v_val_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_983_ = crate::leanh::lean_ctor_get(v_x_981_, 0);
        crate::leanh::lean_inc(v_val_983_);
        v___x_984_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_984_, 0, v_k_980_);
        crate::leanh::lean_ctor_set(v___x_984_, 1, v_val_983_);
        v___x_985_ = crate::leanh::lean_box(0);
        v___x_986_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_986_, 0, v___x_984_);
        crate::leanh::lean_ctor_set(v___x_986_, 1, v___x_985_);
        return v___x_986_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__spec__0___boxed(
    mut v_k_987_: *mut crate::leanh::LeanObject,
    mut v_x_988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_989_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__spec__0(v_k_987_, v_x_988_);
    crate::leanh::lean_dec(v_x_988_);
    return v_res_989_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__spec__1(
    mut v_a_990_: *mut crate::leanh::LeanObject,
    mut v_a_991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_990_) == 0 {
                    v___x_992_ = lean_array_to_list(v_a_991_);
                    return v___x_992_;
                } else {
                    v_head_993_ = crate::leanh::lean_ctor_get(v_a_990_, 0);
                    crate::leanh::lean_inc(v_head_993_);
                    v_tail_994_ = crate::leanh::lean_ctor_get(v_a_990_, 1);
                    crate::leanh::lean_inc(v_tail_994_);
                    crate::leanh::lean_dec_ref_known(v_a_990_, 2);
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
    mut v_x_999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_info_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subexprPos_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diffStatus_x3f_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_info_1000_ = crate::leanh::lean_ctor_get(v_x_999_, 0);
    v_subexprPos_1001_ = crate::leanh::lean_ctor_get(v_x_999_, 1);
    v_diffStatus_x3f_1002_ = crate::leanh::lean_ctor_get(v_x_999_, 2);
    v___x_1003_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_;
    crate::leanh::lean_inc(v_info_1000_);
    v___x_1004_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1004_, 0, v___x_1003_);
    crate::leanh::lean_ctor_set(v___x_1004_, 1, v_info_1000_);
    v___x_1005_ = crate::leanh::lean_box(0);
    v___x_1006_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1006_, 0, v___x_1004_);
    crate::leanh::lean_ctor_set(v___x_1006_, 1, v___x_1005_);
    v___x_1007_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_;
    crate::leanh::lean_inc(v_subexprPos_1001_);
    v___x_1008_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1008_, 0, v___x_1007_);
    crate::leanh::lean_ctor_set(v___x_1008_, 1, v_subexprPos_1001_);
    v___x_1009_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1009_, 0, v___x_1008_);
    crate::leanh::lean_ctor_set(v___x_1009_, 1, v___x_1005_);
    v___x_1010_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_;
    v___x_1011_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__spec__0(v___x_1010_, v_diffStatus_x3f_1002_);
    v___x_1012_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1012_, 0, v___x_1011_);
    crate::leanh::lean_ctor_set(v___x_1012_, 1, v___x_1005_);
    v___x_1013_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1013_, 0, v___x_1009_);
    crate::leanh::lean_ctor_set(v___x_1013_, 1, v___x_1012_);
    v___x_1014_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1014_, 0, v___x_1006_);
    crate::leanh::lean_ctor_set(v___x_1014_, 1, v___x_1013_);
    v___x_1015_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33_;
    v___x_1016_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33__spec__1(v___x_1014_, v___x_1015_);
    v___x_1017_ = l_Lean_Json_mkObj(v___x_1016_);
    crate::leanh::lean_dec(v___x_1016_);
    return v___x_1017_;
}
pub unsafe fn l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33____boxed(
    mut v_x_1018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1019_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33_(v_x_1018_);
    crate::leanh::lean_dec_ref(v_x_1018_);
    return v_res_1019_;
}
pub unsafe fn l_Lean_Widget_instRpcEncodableSubexprInfo_enc_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_(
    mut v_a_1022_: *mut crate::leanh::LeanObject,
    mut v_a_1023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_info_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subexprPos_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diffStatus_x3f_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1029_: u8 = 0;
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1036_: u8 = 0;
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1052_: u8 = 0;
    let mut v___x_1053_: u8 = 0;
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1058_: u8 = 0;
    let mut v_isSharedCheck_1059_: u8 = 0;
    let mut v_isSharedCheck_1060_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_info_1024_ = crate::leanh::lean_ctor_get(v_a_1022_, 0);
                v_subexprPos_1025_ = crate::leanh::lean_ctor_get(v_a_1022_, 1);
                v_diffStatus_x3f_1026_ = crate::leanh::lean_ctor_get(v_a_1022_, 2);
                v_isSharedCheck_1060_ = (!crate::leanh::lean_is_exclusive(v_a_1022_)) as u8;
                if v_isSharedCheck_1060_ == 0 {
                    v___x_1028_ = v_a_1022_;
                    v_isShared_1029_ = v_isSharedCheck_1060_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diffStatus_x3f_1026_);
                    crate::leanh::lean_inc(v_subexprPos_1025_);
                    crate::leanh::lean_inc(v_info_1024_);
                    crate::leanh::lean_dec(v_a_1022_);
                    v___x_1028_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_dec_ref(v_info_1024_);
                v_fst_1032_ = crate::leanh::lean_ctor_get(v___x_1031_, 0);
                v_snd_1033_ = crate::leanh::lean_ctor_get(v___x_1031_, 1);
                v_isSharedCheck_1059_ = (!crate::leanh::lean_is_exclusive(v___x_1031_)) as u8;
                if v_isSharedCheck_1059_ == 0 {
                    v___x_1035_ = v___x_1031_;
                    v_isShared_1036_ = v_isSharedCheck_1059_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1033_);
                    crate::leanh::lean_inc(v_fst_1032_);
                    crate::leanh::lean_dec(v___x_1031_);
                    v___x_1035_ = crate::leanh::lean_box(0);
                    v_isShared_1036_ = v_isSharedCheck_1059_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1037_ = l_Lean_SubExpr_Pos_toString(v_subexprPos_1025_);
                crate::leanh::lean_dec(v_subexprPos_1025_);
                v___x_1038_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1038_, 0, v___x_1037_);
                if crate::leanh::lean_obj_tag(v_diffStatus_x3f_1026_) == 0 {
                    v___x_1048_ = crate::leanh::lean_box(0);
                    v_fst_1040_ = v___x_1048_;
                    state = 3;
                    continue;
                } else {
                    v_val_1049_ = crate::leanh::lean_ctor_get(v_diffStatus_x3f_1026_, 0);
                    v_isSharedCheck_1058_ =
                        (!crate::leanh::lean_is_exclusive(v_diffStatus_x3f_1026_)) as u8;
                    if v_isSharedCheck_1058_ == 0 {
                        v___x_1051_ = v_diffStatus_x3f_1026_;
                        v_isShared_1052_ = v_isSharedCheck_1058_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1049_);
                        crate::leanh::lean_dec(v_diffStatus_x3f_1026_);
                        v___x_1051_ = crate::leanh::lean_box(0);
                        v_isShared_1052_ = v_isSharedCheck_1058_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1029_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1028_, 2, v_fst_1040_);
                    crate::leanh::lean_ctor_set(v___x_1028_, 1, v___x_1038_);
                    crate::leanh::lean_ctor_set(v___x_1028_, 0, v_fst_1032_);
                    v___x_1042_ = v___x_1028_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1047_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_fst_1032_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1047_, 1, v___x_1038_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1047_, 2, v_fst_1040_);
                    v___x_1042_ = v_reuseFailAlloc_1047_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1043_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_33_(v___x_1042_);
                crate::leanh::lean_dec_ref(v___x_1042_);
                if v_isShared_1036_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1035_, 0, v___x_1043_);
                    v___x_1045_ = v___x_1035_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1046_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_snd_1033_);
                    v___x_1045_ = v_reuseFailAlloc_1046_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1045_;
            }
            6 => {
                v___x_1053_ = (crate::leanh::lean_unbox(v_val_1049_) as u8);
                crate::leanh::lean_dec(v_val_1049_);
                v___x_1054_ = l_Lean_Widget_instToJsonDiffTag_toJson(v___x_1053_);
                if v_isShared_1052_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1051_, 0, v___x_1054_);
                    v___x_1056_ = v___x_1051_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1057_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
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
    mut v_x_1061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_x_1061_);
    return v_x_1061_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___redArg___boxed(
    mut v_x_1062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1063_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___redArg(v_x_1062_);
    crate::leanh::lean_dec_ref(v_x_1062_);
    return v_res_1063_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0(
    mut v_00_u03b1_1064_: *mut crate::leanh::LeanObject,
    mut v_x_1065_: *mut crate::leanh::LeanObject,
    mut v___y_1066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_x_1065_);
    return v_x_1065_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0___boxed(
    mut v_00_u03b1_1067_: *mut crate::leanh::LeanObject,
    mut v_x_1068_: *mut crate::leanh::LeanObject,
    mut v___y_1069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1070_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1__spec__0(v_00_u03b1_1067_, v_x_1068_, v___y_1069_);
    crate::leanh::lean_dec_ref(v___y_1069_);
    crate::leanh::lean_dec_ref(v_x_1068_);
    return v_res_1070_;
}
pub unsafe fn l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_(
    mut v_j_1071_: *mut crate::leanh::LeanObject,
    mut v_a_1072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1077_: u8 = 0;
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1081_: u8 = 0;
    let mut v_a_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subexprPos_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diffStatus_x3f_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1088_: u8 = 0;
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1094_: u8 = 0;
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1098_: u8 = 0;
    let mut v_a_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1104_: u8 = 0;
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1108_: u8 = 0;
    let mut v_a_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1114_: u8 = 0;
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1118_: u8 = 0;
    let mut v_a_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1122_: u8 = 0;
    let mut v_____do__lift_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1135_: u8 = 0;
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1140_: u8 = 0;
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1144_: u8 = 0;
    let mut v_a_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1149_: u8 = 0;
    let mut v_isSharedCheck_1150_: u8 = 0;
    let mut v_isSharedCheck_1151_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1073_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveCode_2818889736____hygCtx___hyg_15_(v_j_1071_);
                if crate::leanh::lean_obj_tag(v___x_1073_) == 0 {
                    v_a_1074_ = crate::leanh::lean_ctor_get(v___x_1073_, 0);
                    v_isSharedCheck_1081_ = (!crate::leanh::lean_is_exclusive(v___x_1073_)) as u8;
                    if v_isSharedCheck_1081_ == 0 {
                        v___x_1076_ = v___x_1073_;
                        v_isShared_1077_ = v_isSharedCheck_1081_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1074_);
                        crate::leanh::lean_dec(v___x_1073_);
                        v___x_1076_ = crate::leanh::lean_box(0);
                        v_isShared_1077_ = v_isSharedCheck_1081_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1082_ = crate::leanh::lean_ctor_get(v___x_1073_, 0);
                    crate::leanh::lean_inc(v_a_1082_);
                    crate::leanh::lean_dec_ref_known(v___x_1073_, 1);
                    v_info_1083_ = crate::leanh::lean_ctor_get(v_a_1082_, 0);
                    v_subexprPos_1084_ = crate::leanh::lean_ctor_get(v_a_1082_, 1);
                    v_diffStatus_x3f_1085_ = crate::leanh::lean_ctor_get(v_a_1082_, 2);
                    v_isSharedCheck_1151_ = (!crate::leanh::lean_is_exclusive(v_a_1082_)) as u8;
                    if v_isSharedCheck_1151_ == 0 {
                        v___x_1087_ = v_a_1082_;
                        v_isShared_1088_ = v_isSharedCheck_1151_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diffStatus_x3f_1085_);
                        crate::leanh::lean_inc(v_subexprPos_1084_);
                        crate::leanh::lean_inc(v_info_1083_);
                        crate::leanh::lean_dec(v_a_1082_);
                        v___x_1087_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1080_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
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
                if crate::leanh::lean_obj_tag(v___x_1090_) == 0 {
                    crate::leanh::lean_del_object(v___x_1087_);
                    crate::leanh::lean_dec(v_diffStatus_x3f_1085_);
                    crate::leanh::lean_dec(v_subexprPos_1084_);
                    v_a_1091_ = crate::leanh::lean_ctor_get(v___x_1090_, 0);
                    v_isSharedCheck_1098_ = (!crate::leanh::lean_is_exclusive(v___x_1090_)) as u8;
                    if v_isSharedCheck_1098_ == 0 {
                        v___x_1093_ = v___x_1090_;
                        v_isShared_1094_ = v_isSharedCheck_1098_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1091_);
                        crate::leanh::lean_dec(v___x_1090_);
                        v___x_1093_ = crate::leanh::lean_box(0);
                        v_isShared_1094_ = v_isSharedCheck_1098_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_1099_ = crate::leanh::lean_ctor_get(v___x_1090_, 0);
                    crate::leanh::lean_inc(v_a_1099_);
                    crate::leanh::lean_dec_ref_known(v___x_1090_, 1);
                    v___x_1100_ = l_Lean_Json_getStr_x3f(v_subexprPos_1084_);
                    if crate::leanh::lean_obj_tag(v___x_1100_) == 0 {
                        crate::leanh::lean_dec(v_a_1099_);
                        crate::leanh::lean_del_object(v___x_1087_);
                        crate::leanh::lean_dec(v_diffStatus_x3f_1085_);
                        v_a_1101_ = crate::leanh::lean_ctor_get(v___x_1100_, 0);
                        v_isSharedCheck_1108_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1100_)) as u8;
                        if v_isSharedCheck_1108_ == 0 {
                            v___x_1103_ = v___x_1100_;
                            v_isShared_1104_ = v_isSharedCheck_1108_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1101_);
                            crate::leanh::lean_dec(v___x_1100_);
                            v___x_1103_ = crate::leanh::lean_box(0);
                            v_isShared_1104_ = v_isSharedCheck_1108_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_1109_ = crate::leanh::lean_ctor_get(v___x_1100_, 0);
                        crate::leanh::lean_inc(v_a_1109_);
                        crate::leanh::lean_dec_ref_known(v___x_1100_, 1);
                        v___x_1110_ = l_Lean_SubExpr_Pos_fromString_x3f(v_a_1109_);
                        if crate::leanh::lean_obj_tag(v___x_1110_) == 0 {
                            crate::leanh::lean_dec(v_a_1099_);
                            crate::leanh::lean_del_object(v___x_1087_);
                            crate::leanh::lean_dec(v_diffStatus_x3f_1085_);
                            v_a_1111_ = crate::leanh::lean_ctor_get(v___x_1110_, 0);
                            v_isSharedCheck_1118_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1110_)) as u8;
                            if v_isSharedCheck_1118_ == 0 {
                                v___x_1113_ = v___x_1110_;
                                v_isShared_1114_ = v_isSharedCheck_1118_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1111_);
                                crate::leanh::lean_dec(v___x_1110_);
                                v___x_1113_ = crate::leanh::lean_box(0);
                                v_isShared_1114_ = v_isSharedCheck_1118_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v_a_1119_ = crate::leanh::lean_ctor_get(v___x_1110_, 0);
                            v_isSharedCheck_1150_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1110_)) as u8;
                            if v_isSharedCheck_1150_ == 0 {
                                v___x_1121_ = v___x_1110_;
                                v_isShared_1122_ = v_isSharedCheck_1150_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1119_);
                                crate::leanh::lean_dec(v___x_1110_);
                                v___x_1121_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1097_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
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
                    v_reuseFailAlloc_1107_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
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
                    v_reuseFailAlloc_1117_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
                    v___x_1116_ = v_reuseFailAlloc_1117_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1116_;
            }
            10 => {
                if crate::leanh::lean_obj_tag(v_diffStatus_x3f_1085_) == 0 {
                    v___x_1131_ = crate::leanh::lean_box(0);
                    v_____do__lift_1124_ = v___x_1131_;
                    state = 11;
                    continue;
                } else {
                    v_val_1132_ = crate::leanh::lean_ctor_get(v_diffStatus_x3f_1085_, 0);
                    v_isSharedCheck_1149_ =
                        (!crate::leanh::lean_is_exclusive(v_diffStatus_x3f_1085_)) as u8;
                    if v_isSharedCheck_1149_ == 0 {
                        v___x_1134_ = v_diffStatus_x3f_1085_;
                        v_isShared_1135_ = v_isSharedCheck_1149_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1132_);
                        crate::leanh::lean_dec(v_diffStatus_x3f_1085_);
                        v___x_1134_ = crate::leanh::lean_box(0);
                        v_isShared_1135_ = v_isSharedCheck_1149_;
                        state = 14;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_1088_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1087_, 2, v_____do__lift_1124_);
                    crate::leanh::lean_ctor_set(v___x_1087_, 1, v_a_1119_);
                    crate::leanh::lean_ctor_set(v___x_1087_, 0, v_a_1099_);
                    v___x_1126_ = v___x_1087_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1130_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1099_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_a_1119_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1130_, 2, v_____do__lift_1124_);
                    v___x_1126_ = v_reuseFailAlloc_1130_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_1122_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1121_, 0, v___x_1126_);
                    v___x_1128_ = v___x_1121_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1129_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
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
                if crate::leanh::lean_obj_tag(v___x_1136_) == 0 {
                    crate::leanh::lean_del_object(v___x_1134_);
                    crate::leanh::lean_del_object(v___x_1121_);
                    crate::leanh::lean_dec(v_a_1119_);
                    crate::leanh::lean_dec(v_a_1099_);
                    crate::leanh::lean_del_object(v___x_1087_);
                    v_a_1137_ = crate::leanh::lean_ctor_get(v___x_1136_, 0);
                    v_isSharedCheck_1144_ = (!crate::leanh::lean_is_exclusive(v___x_1136_)) as u8;
                    if v_isSharedCheck_1144_ == 0 {
                        v___x_1139_ = v___x_1136_;
                        v_isShared_1140_ = v_isSharedCheck_1144_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1137_);
                        crate::leanh::lean_dec(v___x_1136_);
                        v___x_1139_ = crate::leanh::lean_box(0);
                        v_isShared_1140_ = v_isSharedCheck_1144_;
                        state = 15;
                        continue;
                    }
                } else {
                    v_a_1145_ = crate::leanh::lean_ctor_get(v___x_1136_, 0);
                    crate::leanh::lean_inc(v_a_1145_);
                    crate::leanh::lean_dec_ref_known(v___x_1136_, 1);
                    if v_isShared_1135_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1134_, 0, v_a_1145_);
                        v___x_1147_ = v___x_1134_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_1148_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1145_);
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
                    v_reuseFailAlloc_1143_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
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
    mut v_j_1152_: *mut crate::leanh::LeanObject,
    mut v_a_1153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1154_ = l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_(v_j_1152_, v_a_1153_);
    crate::leanh::lean_dec_ref(v_a_1153_);
    return v_res_1154_;
}
pub unsafe fn l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0(
    mut v_x_1161_: *mut crate::leanh::LeanObject,
    mut v_y_1162_: *mut crate::leanh::LeanObject,
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
    mut v_x_1168_: *mut crate::leanh::LeanObject,
    mut v_y_1169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1170_: u8 = 0;
    let mut v_r_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1170_ = l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0(v_x_1168_, v_y_1169_);
    crate::leanh::lean_dec(v_y_1169_);
    crate::leanh::lean_dec(v_x_1168_);
    v_r_1171_ = crate::leanh::lean_box((v_res_1170_) as usize);
    return v_r_1171_;
}
pub unsafe fn l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__1(
    mut v___f_1172_: *mut crate::leanh::LeanObject,
    mut v_pm_1173_: *mut crate::leanh::LeanObject,
    mut v_inst_1174_: *mut crate::leanh::LeanObject,
    mut v_merger_1175_: *mut crate::leanh::LeanObject,
    mut v_info_1176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_subexprPos_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_subexprPos_1177_ = crate::leanh::lean_ctor_get(v_info_1176_, 1);
    crate::leanh::lean_inc(v_subexprPos_1177_);
    v___x_1178_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(
        v___f_1172_,
        v_pm_1173_,
        v_subexprPos_1177_,
    );
    if crate::leanh::lean_obj_tag(v___x_1178_) == 0 {
        let mut v_toApplicative_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_merger_1175_);
        v_toApplicative_1179_ = crate::leanh::lean_ctor_get(v_inst_1174_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1179_);
        crate::leanh::lean_dec_ref(v_inst_1174_);
        v_toPure_1180_ = crate::leanh::lean_ctor_get(v_toApplicative_1179_, 1);
        crate::leanh::lean_inc(v_toPure_1180_);
        crate::leanh::lean_dec_ref(v_toApplicative_1179_);
        v___x_1181_ =
            crate::leanh::lean_apply_2(v_toPure_1180_, crate::leanh::lean_box(0), v_info_1176_);
        return v___x_1181_;
    } else {
        let mut v_val_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_1174_);
        v_val_1182_ = crate::leanh::lean_ctor_get(v___x_1178_, 0);
        crate::leanh::lean_inc(v_val_1182_);
        crate::leanh::lean_dec_ref_known(v___x_1178_, 1);
        v___x_1183_ = crate::leanh::lean_apply_2(v_merger_1175_, v_info_1176_, v_val_1182_);
        return v___x_1183_;
    }
}
pub unsafe fn l_Lean_Widget_CodeWithInfos_mergePosMap___redArg(
    mut v_inst_1185_: *mut crate::leanh::LeanObject,
    mut v_merger_1186_: *mut crate::leanh::LeanObject,
    mut v_pm_1187_: *mut crate::leanh::LeanObject,
    mut v_tt_1188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_pm_1187_) == 0 {
        let mut v___f_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_1189_ = l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___closed__0;
        crate::leanh::lean_inc_ref(v_inst_1185_);
        v___f_1190_ = crate::leanh::lean_alloc_closure(
            l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_1190_, 0, v___f_1189_);
        crate::leanh::lean_closure_set(v___f_1190_, 1, v_pm_1187_);
        crate::leanh::lean_closure_set(v___f_1190_, 2, v_inst_1185_);
        crate::leanh::lean_closure_set(v___f_1190_, 3, v_merger_1186_);
        v___x_1191_ = l_Lean_Widget_TaggedText_mapM___redArg(v_inst_1185_, v___f_1190_, v_tt_1188_);
        return v___x_1191_;
    } else {
        let mut v_toApplicative_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_merger_1186_);
        v_toApplicative_1192_ = crate::leanh::lean_ctor_get(v_inst_1185_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1192_);
        crate::leanh::lean_dec_ref(v_inst_1185_);
        v_toPure_1193_ = crate::leanh::lean_ctor_get(v_toApplicative_1192_, 1);
        crate::leanh::lean_inc(v_toPure_1193_);
        crate::leanh::lean_dec_ref(v_toApplicative_1192_);
        v___x_1194_ =
            crate::leanh::lean_apply_2(v_toPure_1193_, crate::leanh::lean_box(0), v_tt_1188_);
        return v___x_1194_;
    }
}
pub unsafe fn l_Lean_Widget_CodeWithInfos_mergePosMap(
    mut v_m_1195_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1196_: *mut crate::leanh::LeanObject,
    mut v_inst_1197_: *mut crate::leanh::LeanObject,
    mut v_merger_1198_: *mut crate::leanh::LeanObject,
    mut v_pm_1199_: *mut crate::leanh::LeanObject,
    mut v_tt_1200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1201_ = l_Lean_Widget_CodeWithInfos_mergePosMap___redArg(
        v_inst_1197_,
        v_merger_1198_,
        v_pm_1199_,
        v_tt_1200_,
    );
    return v___x_1201_;
}
pub unsafe fn l_Lean_Widget_CodeWithInfos_pretty(
    mut v_tt_1202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1203_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_tt_1202_);
    return v___x_1203_;
}
pub unsafe fn l_Lean_Widget_SubexprInfo_withDiffTag(
    mut v_tag_1204_: u8,
    mut v_c_1205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_info_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subexprPos_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1210_: u8 = 0;
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1216_: u8 = 0;
    let mut v_unused_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_info_1206_ = crate::leanh::lean_ctor_get(v_c_1205_, 0);
                v_subexprPos_1207_ = crate::leanh::lean_ctor_get(v_c_1205_, 1);
                v_isSharedCheck_1216_ = (!crate::leanh::lean_is_exclusive(v_c_1205_)) as u8;
                if v_isSharedCheck_1216_ == 0 {
                    v_unused_1217_ = crate::leanh::lean_ctor_get(v_c_1205_, 2);
                    crate::leanh::lean_dec(v_unused_1217_);
                    v___x_1209_ = v_c_1205_;
                    v_isShared_1210_ = v_isSharedCheck_1216_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_subexprPos_1207_);
                    crate::leanh::lean_inc(v_info_1206_);
                    crate::leanh::lean_dec(v_c_1205_);
                    v___x_1209_ = crate::leanh::lean_box(0);
                    v_isShared_1210_ = v_isSharedCheck_1216_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1211_ = crate::leanh::lean_box((v_tag_1204_) as usize);
                v___x_1212_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1212_, 0, v___x_1211_);
                if v_isShared_1210_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1209_, 2, v___x_1212_);
                    v___x_1214_ = v___x_1209_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1215_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_info_1206_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_subexprPos_1207_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1215_, 2, v___x_1212_);
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
    mut v_tag_1218_: *mut crate::leanh::LeanObject,
    mut v_c_1219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tag_boxed_1220_: u8 = 0;
    let mut v_res_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tag_boxed_1220_ = (crate::leanh::lean_unbox(v_tag_1218_) as u8);
    v_res_1221_ = l_Lean_Widget_SubexprInfo_withDiffTag(v_tag_boxed_1220_, v_c_1219_);
    return v_res_1221_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg(
    mut v_t_1222_: *mut crate::leanh::LeanObject,
    mut v_k_1223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: u8 = 0;
    let mut v___x_1229_: u8 = 0;
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1222_) == 0 {
                    v_k_1224_ = crate::leanh::lean_ctor_get(v_t_1222_, 1);
                    v_v_1225_ = crate::leanh::lean_ctor_get(v_t_1222_, 2);
                    v_l_1226_ = crate::leanh::lean_ctor_get(v_t_1222_, 3);
                    v_r_1227_ = crate::leanh::lean_ctor_get(v_t_1222_, 4);
                    v___x_1228_ = lean_nat_dec_lt(v_k_1223_, v_k_1224_);
                    if v___x_1228_ == 0 {
                        v___x_1229_ = lean_nat_dec_eq(v_k_1223_, v_k_1224_);
                        if v___x_1229_ == 0 {
                            v_t_1222_ = v_r_1227_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_v_1225_);
                            v___x_1231_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1231_, 0, v_v_1225_);
                            return v___x_1231_;
                        }
                    } else {
                        v_t_1222_ = v_l_1226_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_1233_ = crate::leanh::lean_box(0);
                    return v___x_1233_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg___boxed(
    mut v_t_1234_: *mut crate::leanh::LeanObject,
    mut v_k_1235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1236_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg(v_t_1234_, v_k_1235_);
    crate::leanh::lean_dec(v_k_1235_);
    crate::leanh::lean_dec(v_t_1234_);
    return v_res_1236_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg(
    mut v_f_1237_: *mut crate::leanh::LeanObject,
    mut v_sz_1238_: usize,
    mut v_i_1239_: usize,
    mut v_bs_1240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1242_: u8 = 0;
    let mut v_v_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: usize = 0;
    let mut v___x_1248_: usize = 0;
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1242_ = lean_usize_dec_lt(v_i_1239_, v_sz_1238_);
                if v___x_1242_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_1237_);
                    return v_bs_1240_;
                } else {
                    v_v_1243_ = lean_array_uget_borrowed(v_bs_1240_, v_i_1239_);
                    crate::leanh::lean_inc(v_v_1243_);
                    crate::leanh::lean_inc_ref(v_f_1237_);
                    v___x_1244_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(v_f_1237_, v_v_1243_);
                    v___x_1245_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_f_1251_: *mut crate::leanh::LeanObject,
    mut v_x_1252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1257_: u8 = 0;
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1261_: u8 = 0;
    let mut v_a_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1265_: u8 = 0;
    let mut v_sz_1266_: usize = 0;
    let mut v___x_1267_: usize = 0;
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1272_: u8 = 0;
    let mut v_a_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1252_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_f_1251_);
                    v_a_1254_ = crate::leanh::lean_ctor_get(v_x_1252_, 0);
                    v_isSharedCheck_1261_ = (!crate::leanh::lean_is_exclusive(v_x_1252_)) as u8;
                    if v_isSharedCheck_1261_ == 0 {
                        v___x_1256_ = v_x_1252_;
                        v_isShared_1257_ = v_isSharedCheck_1261_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1254_);
                        crate::leanh::lean_dec(v_x_1252_);
                        v___x_1256_ = crate::leanh::lean_box(0);
                        v_isShared_1257_ = v_isSharedCheck_1261_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_1262_ = crate::leanh::lean_ctor_get(v_x_1252_, 0);
                    v_isSharedCheck_1272_ = (!crate::leanh::lean_is_exclusive(v_x_1252_)) as u8;
                    if v_isSharedCheck_1272_ == 0 {
                        v___x_1264_ = v_x_1252_;
                        v_isShared_1265_ = v_isSharedCheck_1272_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1262_);
                        crate::leanh::lean_dec(v_x_1252_);
                        v___x_1264_ = crate::leanh::lean_box(0);
                        v_isShared_1265_ = v_isSharedCheck_1272_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_a_1273_ = crate::leanh::lean_ctor_get(v_x_1252_, 0);
                    crate::leanh::lean_inc(v_a_1273_);
                    v_a_1274_ = crate::leanh::lean_ctor_get(v_x_1252_, 1);
                    crate::leanh::lean_inc_ref(v_a_1274_);
                    crate::leanh::lean_dec_ref_known(v_x_1252_, 2);
                    v___x_1275_ = crate::leanh::lean_apply_3(
                        v_f_1251_,
                        v_a_1273_,
                        v_a_1274_,
                        crate::leanh::lean_box(0),
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
                    v_reuseFailAlloc_1260_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
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
                    crate::leanh::lean_ctor_set(v___x_1264_, 0, v___x_1268_);
                    v___x_1270_ = v___x_1264_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1271_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1268_);
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
    mut v_f_1276_: *mut crate::leanh::LeanObject,
    mut v_x_1277_: *mut crate::leanh::LeanObject,
    mut v___y_1278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1279_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(v_f_1276_, v_x_1277_);
    return v_res_1279_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg___boxed(
    mut v_f_1280_: *mut crate::leanh::LeanObject,
    mut v_sz_1281_: *mut crate::leanh::LeanObject,
    mut v_i_1282_: *mut crate::leanh::LeanObject,
    mut v_bs_1283_: *mut crate::leanh::LeanObject,
    mut v___y_1284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1285_: usize = 0;
    let mut v_i_boxed_1286_: usize = 0;
    let mut v_res_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1285_ = crate::leanh::lean_unbox_usize(v_sz_1281_);
    crate::leanh::lean_dec(v_sz_1281_);
    v_i_boxed_1286_ = crate::leanh::lean_unbox_usize(v_i_1282_);
    crate::leanh::lean_dec(v_i_1282_);
    v_res_1287_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg(v_f_1280_, v_sz_boxed_1285_, v_i_boxed_1286_, v_bs_1283_);
    return v_res_1287_;
}
pub unsafe fn _init_l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1288_ = l_Lean_PersistentArray_empty(crate::leanh::lean_box(0));
    return v___x_1288_;
}
pub unsafe fn l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0(
    mut v_infos_1289_: *mut crate::leanh::LeanObject,
    mut v_ctx_1290_: *mut crate::leanh::LeanObject,
    mut v_x_1291_: *mut crate::leanh::LeanObject,
    mut v_subTt_1292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1297_: u8 = 0;
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1310_: u8 = 0;
    let mut v_unused_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1294_ = crate::leanh::lean_ctor_get(v_x_1291_, 0);
                v_isSharedCheck_1310_ = (!crate::leanh::lean_is_exclusive(v_x_1291_)) as u8;
                if v_isSharedCheck_1310_ == 0 {
                    v_unused_1311_ = crate::leanh::lean_ctor_get(v_x_1291_, 1);
                    crate::leanh::lean_dec(v_unused_1311_);
                    v___x_1296_ = v_x_1291_;
                    v_isShared_1297_ = v_isSharedCheck_1310_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_1294_);
                    crate::leanh::lean_dec(v_x_1291_);
                    v___x_1296_ = crate::leanh::lean_box(0);
                    v_isShared_1297_ = v_isSharedCheck_1310_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1298_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg(v_infos_1289_, v_fst_1294_);
                if crate::leanh::lean_obj_tag(v___x_1298_) == 0 {
                    crate::leanh::lean_del_object(v___x_1296_);
                    crate::leanh::lean_dec(v_fst_1294_);
                    v___x_1299_ =
                        l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(
                            v_ctx_1290_,
                            v_infos_1289_,
                            v_subTt_1292_,
                        );
                    return v___x_1299_;
                } else {
                    v_val_1300_ = crate::leanh::lean_ctor_get(v___x_1298_, 0);
                    crate::leanh::lean_inc(v_val_1300_);
                    crate::leanh::lean_dec_ref_known(v___x_1298_, 1);
                    v___x_1301_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0_once), _init_l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___closed__0);
                    crate::leanh::lean_inc_ref(v_ctx_1290_);
                    v___x_1302_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1302_, 0, v_ctx_1290_);
                    crate::leanh::lean_ctor_set(v___x_1302_, 1, v_val_1300_);
                    crate::leanh::lean_ctor_set(v___x_1302_, 2, v___x_1301_);
                    v___x_1303_ = l_Lean_Server_WithRpcRef_mk___redArg(v___x_1302_);
                    v___x_1304_ =
                        l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(
                            v_ctx_1290_,
                            v_infos_1289_,
                            v_subTt_1292_,
                        );
                    v___x_1305_ = crate::leanh::lean_box(0);
                    v___x_1306_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1306_, 0, v___x_1303_);
                    crate::leanh::lean_ctor_set(v___x_1306_, 1, v_fst_1294_);
                    crate::leanh::lean_ctor_set(v___x_1306_, 2, v___x_1305_);
                    if v_isShared_1297_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1296_, 2);
                        crate::leanh::lean_ctor_set(v___x_1296_, 1, v___x_1304_);
                        crate::leanh::lean_ctor_set(v___x_1296_, 0, v___x_1306_);
                        v___x_1308_ = v___x_1296_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1309_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1306_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1309_, 1, v___x_1304_);
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
    mut v_infos_1312_: *mut crate::leanh::LeanObject,
    mut v_ctx_1313_: *mut crate::leanh::LeanObject,
    mut v_x_1314_: *mut crate::leanh::LeanObject,
    mut v_subTt_1315_: *mut crate::leanh::LeanObject,
    mut v___y_1316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1317_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0(
        v_infos_1312_,
        v_ctx_1313_,
        v_x_1314_,
        v_subTt_1315_,
    );
    return v_res_1317_;
}
pub unsafe fn l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(
    mut v_ctx_1318_: *mut crate::leanh::LeanObject,
    mut v_infos_1319_: *mut crate::leanh::LeanObject,
    mut v_tt_1320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1322_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1322_, 0, v_infos_1319_);
    crate::leanh::lean_closure_set(v___f_1322_, 1, v_ctx_1318_);
    v___x_1323_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(v___f_1322_, v_tt_1320_);
    return v___x_1323_;
}
pub unsafe fn l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go___boxed(
    mut v_ctx_1324_: *mut crate::leanh::LeanObject,
    mut v_infos_1325_: *mut crate::leanh::LeanObject,
    mut v_tt_1326_: *mut crate::leanh::LeanObject,
    mut v_a_1327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1328_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(
        v_ctx_1324_,
        v_infos_1325_,
        v_tt_1326_,
    );
    return v_res_1328_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0(
    mut v_00_u03b4_1329_: *mut crate::leanh::LeanObject,
    mut v_t_1330_: *mut crate::leanh::LeanObject,
    mut v_k_1331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1332_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___redArg(v_t_1330_, v_k_1331_);
    return v___x_1332_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0___boxed(
    mut v_00_u03b4_1333_: *mut crate::leanh::LeanObject,
    mut v_t_1334_: *mut crate::leanh::LeanObject,
    mut v_k_1335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1336_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__0(v_00_u03b4_1333_, v_t_1334_, v_k_1335_);
    crate::leanh::lean_dec(v_k_1335_);
    crate::leanh::lean_dec(v_t_1334_);
    return v_res_1336_;
}
pub unsafe fn l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1(
    mut v_00_u03b1_1337_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1338_: *mut crate::leanh::LeanObject,
    mut v_f_1339_: *mut crate::leanh::LeanObject,
    mut v_x_1340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1342_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___redArg(v_f_1339_, v_x_1340_);
    return v___x_1342_;
}
pub unsafe fn l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1___boxed(
    mut v_00_u03b1_1343_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1344_: *mut crate::leanh::LeanObject,
    mut v_f_1345_: *mut crate::leanh::LeanObject,
    mut v_x_1346_: *mut crate::leanh::LeanObject,
    mut v___y_1347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1348_ = l_Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1(v_00_u03b1_1343_, v_00_u03b2_1344_, v_f_1345_, v_x_1346_);
    return v_res_1348_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1(
    mut v_00_u03b1_1349_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1350_: *mut crate::leanh::LeanObject,
    mut v_f_1351_: *mut crate::leanh::LeanObject,
    mut v_sz_1352_: usize,
    mut v_i_1353_: usize,
    mut v_bs_1354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___redArg(v_f_1351_, v_sz_1352_, v_i_1353_, v_bs_1354_);
    return v___x_1356_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1___boxed(
    mut v_00_u03b1_1357_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1358_: *mut crate::leanh::LeanObject,
    mut v_f_1359_: *mut crate::leanh::LeanObject,
    mut v_sz_1360_: *mut crate::leanh::LeanObject,
    mut v_i_1361_: *mut crate::leanh::LeanObject,
    mut v_bs_1362_: *mut crate::leanh::LeanObject,
    mut v___y_1363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1364_: usize = 0;
    let mut v_i_boxed_1365_: usize = 0;
    let mut v_res_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1364_ = crate::leanh::lean_unbox_usize(v_sz_1360_);
    crate::leanh::lean_dec(v_sz_1360_);
    v_i_boxed_1365_ = crate::leanh::lean_unbox_usize(v_i_1361_);
    crate::leanh::lean_dec(v_i_1361_);
    v_res_1366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_rewriteM___at___00__private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go_spec__1_spec__1(v_00_u03b1_1357_, v_00_u03b2_1358_, v_f_1359_, v_sz_boxed_1364_, v_i_boxed_1365_, v_bs_1362_);
    return v_res_1366_;
}
pub unsafe fn l_Lean_Widget_tagCodeInfos(
    mut v_ctx_1367_: *mut crate::leanh::LeanObject,
    mut v_infos_1368_: *mut crate::leanh::LeanObject,
    mut v_tt_1369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1371_ = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(
        v_ctx_1367_,
        v_infos_1368_,
        v_tt_1369_,
    );
    return v___x_1371_;
}
pub unsafe fn l_Lean_Widget_tagCodeInfos___boxed(
    mut v_ctx_1372_: *mut crate::leanh::LeanObject,
    mut v_infos_1373_: *mut crate::leanh::LeanObject,
    mut v_tt_1374_: *mut crate::leanh::LeanObject,
    mut v_a_1375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1376_ = l_Lean_Widget_tagCodeInfos(v_ctx_1372_, v_infos_1373_, v_tt_1374_);
    return v_res_1376_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0(
    mut v_opts_1377_: *mut crate::leanh::LeanObject,
    mut v_opt_1378_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1379_ = crate::leanh::lean_ctor_get(v_opt_1378_, 0);
    v_defValue_1380_ = crate::leanh::lean_ctor_get(v_opt_1378_, 1);
    v_map_1381_ = crate::leanh::lean_ctor_get(v_opts_1377_, 0);
    v___x_1382_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1381_,
            v_name_1379_,
        );
    if crate::leanh::lean_obj_tag(v___x_1382_) == 0 {
        let mut v___x_1383_: u8 = 0;
        v___x_1383_ = (crate::leanh::lean_unbox(v_defValue_1380_) as u8);
        return v___x_1383_;
    } else {
        let mut v_val_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1384_ = crate::leanh::lean_ctor_get(v___x_1382_, 0);
        crate::leanh::lean_inc(v_val_1384_);
        crate::leanh::lean_dec_ref_known(v___x_1382_, 1);
        if crate::leanh::lean_obj_tag(v_val_1384_) == 1 {
            let mut v_v_1385_: u8 = 0;
            v_v_1385_ = crate::leanh::lean_ctor_get_uint8(v_val_1384_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_1384_, 0);
            return v_v_1385_;
        } else {
            let mut v___x_1386_: u8 = 0;
            crate::leanh::lean_dec(v_val_1384_);
            v___x_1386_ = (crate::leanh::lean_unbox(v_defValue_1380_) as u8);
            return v___x_1386_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0___boxed(
    mut v_opts_1387_: *mut crate::leanh::LeanObject,
    mut v_opt_1388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1389_: u8 = 0;
    let mut v_r_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1389_ =
        l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0(v_opts_1387_, v_opt_1388_);
    crate::leanh::lean_dec_ref(v_opt_1388_);
    crate::leanh::lean_dec_ref(v_opts_1387_);
    v_r_1390_ = crate::leanh::lean_box((v_res_1389_) as usize);
    return v_r_1390_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg(
    mut v_e_1391_: *mut crate::leanh::LeanObject,
    mut v___y_1392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1394_: u8 = 0;
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1408_: u8 = 0;
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1414_: u8 = 0;
    let mut v_unused_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1394_ = l_Lean_Expr_hasMVar(v_e_1391_);
                if v___x_1394_ == 0 {
                    v___x_1395_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1395_, 0, v_e_1391_);
                    return v___x_1395_;
                } else {
                    v___x_1396_ = lean_st_ref_get(v___y_1392_);
                    v_mctx_1397_ = crate::leanh::lean_ctor_get(v___x_1396_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_1397_);
                    crate::leanh::lean_dec(v___x_1396_);
                    v___x_1398_ = l_Lean_instantiateMVarsCore(v_mctx_1397_, v_e_1391_);
                    v_fst_1399_ = crate::leanh::lean_ctor_get(v___x_1398_, 0);
                    crate::leanh::lean_inc(v_fst_1399_);
                    v_snd_1400_ = crate::leanh::lean_ctor_get(v___x_1398_, 1);
                    crate::leanh::lean_inc(v_snd_1400_);
                    crate::leanh::lean_dec_ref(v___x_1398_);
                    v___x_1401_ = lean_st_ref_take(v___y_1392_);
                    v_cache_1402_ = crate::leanh::lean_ctor_get(v___x_1401_, 1);
                    v_zetaDeltaFVarIds_1403_ = crate::leanh::lean_ctor_get(v___x_1401_, 2);
                    v_postponed_1404_ = crate::leanh::lean_ctor_get(v___x_1401_, 3);
                    v_diag_1405_ = crate::leanh::lean_ctor_get(v___x_1401_, 4);
                    v_isSharedCheck_1414_ = (!crate::leanh::lean_is_exclusive(v___x_1401_)) as u8;
                    if v_isSharedCheck_1414_ == 0 {
                        v_unused_1415_ = crate::leanh::lean_ctor_get(v___x_1401_, 0);
                        crate::leanh::lean_dec(v_unused_1415_);
                        v___x_1407_ = v___x_1401_;
                        v_isShared_1408_ = v_isSharedCheck_1414_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_1405_);
                        crate::leanh::lean_inc(v_postponed_1404_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_1403_);
                        crate::leanh::lean_inc(v_cache_1402_);
                        crate::leanh::lean_dec(v___x_1401_);
                        v___x_1407_ = crate::leanh::lean_box(0);
                        v_isShared_1408_ = v_isSharedCheck_1414_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1408_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1407_, 0, v_snd_1400_);
                    v___x_1410_ = v___x_1407_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1413_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_snd_1400_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_cache_1402_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1413_,
                        2,
                        v_zetaDeltaFVarIds_1403_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1413_, 3, v_postponed_1404_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1413_, 4, v_diag_1405_);
                    v___x_1410_ = v_reuseFailAlloc_1413_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1411_ = lean_st_ref_set(v___y_1392_, v___x_1410_);
                v___x_1412_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1412_, 0, v_fst_1399_);
                return v___x_1412_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg___boxed(
    mut v_e_1416_: *mut crate::leanh::LeanObject,
    mut v___y_1417_: *mut crate::leanh::LeanObject,
    mut v___y_1418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1419_ = l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg(
        v_e_1416_,
        v___y_1417_,
    );
    crate::leanh::lean_dec(v___y_1417_);
    return v_res_1419_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1(
    mut v_e_1420_: *mut crate::leanh::LeanObject,
    mut v___y_1421_: *mut crate::leanh::LeanObject,
    mut v___y_1422_: *mut crate::leanh::LeanObject,
    mut v___y_1423_: *mut crate::leanh::LeanObject,
    mut v___y_1424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1426_ = l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg(
        v_e_1420_,
        v___y_1422_,
    );
    return v___x_1426_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___boxed(
    mut v_e_1427_: *mut crate::leanh::LeanObject,
    mut v___y_1428_: *mut crate::leanh::LeanObject,
    mut v___y_1429_: *mut crate::leanh::LeanObject,
    mut v___y_1430_: *mut crate::leanh::LeanObject,
    mut v___y_1431_: *mut crate::leanh::LeanObject,
    mut v___y_1432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1433_ = l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1(
        v_e_1427_,
        v___y_1428_,
        v___y_1429_,
        v___y_1430_,
        v___y_1431_,
    );
    crate::leanh::lean_dec(v___y_1431_);
    crate::leanh::lean_dec_ref(v___y_1430_);
    crate::leanh::lean_dec(v___y_1429_);
    crate::leanh::lean_dec_ref(v___y_1428_);
    return v_res_1433_;
}
pub unsafe fn l_Lean_Widget_ppExprTagged(
    mut v_e_1436_: *mut crate::leanh::LeanObject,
    mut v_delab_1437_: *mut crate::leanh::LeanObject,
    mut v_a_1438_: *mut crate::leanh::LeanObject,
    mut v_a_1439_: *mut crate::leanh::LeanObject,
    mut v_a_1440_: *mut crate::leanh::LeanObject,
    mut v_a_1441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_e_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: u8 = 0;
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1458_: u8 = 0;
    let mut v_fmt_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infos_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1479_: u8 = 0;
    let mut v_a_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1483_: u8 = 0;
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1487_: u8 = 0;
    let mut v___x_1488_: u8 = 0;
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1448_ = crate::leanh::lean_ctor_get(v_a_1440_, 2);
                v_currNamespace_1449_ = crate::leanh::lean_ctor_get(v_a_1440_, 6);
                v_openDecls_1450_ = crate::leanh::lean_ctor_get(v_a_1440_, 7);
                v___x_1451_ = l_Lean_pp_raw;
                v___x_1452_ = l_Lean_Option_get___at___00Lean_Widget_ppExprTagged_spec__0(
                    v_options_1448_,
                    v___x_1451_,
                );
                if v___x_1452_ == 0 {
                    v___x_1453_ = crate::leanh::lean_box(1);
                    v___x_1454_ = l_Lean_PrettyPrinter_ppExprWithInfos(
                        v_e_1436_,
                        v___x_1453_,
                        v_delab_1437_,
                        v_a_1438_,
                        v_a_1439_,
                        v_a_1440_,
                        v_a_1441_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1454_) == 0 {
                        v_a_1455_ = crate::leanh::lean_ctor_get(v___x_1454_, 0);
                        v_isSharedCheck_1479_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1454_)) as u8;
                        if v_isSharedCheck_1479_ == 0 {
                            v___x_1457_ = v___x_1454_;
                            v_isShared_1458_ = v_isSharedCheck_1479_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1455_);
                            crate::leanh::lean_dec(v___x_1454_);
                            v___x_1457_ = crate::leanh::lean_box(0);
                            v_isShared_1458_ = v_isSharedCheck_1479_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1480_ = crate::leanh::lean_ctor_get(v___x_1454_, 0);
                        v_isSharedCheck_1487_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1454_)) as u8;
                        if v_isSharedCheck_1487_ == 0 {
                            v___x_1482_ = v___x_1454_;
                            v_isShared_1483_ = v_isSharedCheck_1487_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1480_);
                            crate::leanh::lean_dec(v___x_1454_);
                            v___x_1482_ = crate::leanh::lean_box(0);
                            v_isShared_1483_ = v_isSharedCheck_1487_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_delab_1437_);
                    v___x_1488_ = l_Lean_getPPInstantiateMVars(v_options_1448_);
                    if v___x_1488_ == 0 {
                        v_e_1444_ = v_e_1436_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1489_ = l_Lean_instantiateMVars___at___00Lean_Widget_ppExprTagged_spec__1___redArg(v_e_1436_, v_a_1439_);
                        v_a_1490_ = crate::leanh::lean_ctor_get(v___x_1489_, 0);
                        crate::leanh::lean_inc(v_a_1490_);
                        crate::leanh::lean_dec_ref(v___x_1489_);
                        v_e_1444_ = v_a_1490_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1445_ = lean_expr_dbg_to_string(v_e_1444_);
                crate::leanh::lean_dec_ref(v_e_1444_);
                v___x_1446_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1446_, 0, v___x_1445_);
                v___x_1447_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1447_, 0, v___x_1446_);
                return v___x_1447_;
            }
            2 => {
                v_fmt_1459_ = crate::leanh::lean_ctor_get(v_a_1455_, 0);
                crate::leanh::lean_inc(v_fmt_1459_);
                v_infos_1460_ = crate::leanh::lean_ctor_get(v_a_1455_, 1);
                crate::leanh::lean_inc(v_infos_1460_);
                crate::leanh::lean_dec(v_a_1455_);
                v___x_1461_ = lean_st_ref_get(v_a_1441_);
                v___x_1462_ = lean_st_ref_get(v_a_1439_);
                v___x_1463_ = lean_st_ref_get(v_a_1441_);
                v_env_1464_ = crate::leanh::lean_ctor_get(v___x_1461_, 0);
                crate::leanh::lean_inc_ref(v_env_1464_);
                crate::leanh::lean_dec(v___x_1461_);
                v_mctx_1465_ = crate::leanh::lean_ctor_get(v___x_1462_, 0);
                crate::leanh::lean_inc_ref(v_mctx_1465_);
                crate::leanh::lean_dec(v___x_1462_);
                v_ngen_1466_ = crate::leanh::lean_ctor_get(v___x_1463_, 2);
                crate::leanh::lean_inc_ref(v_ngen_1466_);
                crate::leanh::lean_dec(v___x_1463_);
                v___x_1467_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1468_ = l_Std_Format_defWidth;
                v___x_1469_ =
                    l_Lean_Widget_TaggedText_prettyTagged(v_fmt_1459_, v___x_1467_, v___x_1468_);
                v___x_1470_ = crate::leanh::lean_box(0);
                v___x_1471_ = l_Lean_instInhabitedFileMap_default;
                crate::leanh::lean_inc(v_openDecls_1450_);
                crate::leanh::lean_inc(v_currNamespace_1449_);
                crate::leanh::lean_inc_ref(v_options_1448_);
                v___x_1472_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1472_, 0, v_env_1464_);
                crate::leanh::lean_ctor_set(v___x_1472_, 1, v___x_1470_);
                crate::leanh::lean_ctor_set(v___x_1472_, 2, v___x_1471_);
                crate::leanh::lean_ctor_set(v___x_1472_, 3, v_mctx_1465_);
                crate::leanh::lean_ctor_set(v___x_1472_, 4, v_options_1448_);
                crate::leanh::lean_ctor_set(v___x_1472_, 5, v_currNamespace_1449_);
                crate::leanh::lean_ctor_set(v___x_1472_, 6, v_openDecls_1450_);
                crate::leanh::lean_ctor_set(v___x_1472_, 7, v_ngen_1466_);
                v___x_1473_ = l_Lean_Widget_ppExprTagged___closed__0;
                v___x_1474_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1474_, 0, v___x_1472_);
                crate::leanh::lean_ctor_set(v___x_1474_, 1, v___x_1470_);
                crate::leanh::lean_ctor_set(v___x_1474_, 2, v___x_1473_);
                v___x_1475_ =
                    l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_tagCodeInfos_go(
                        v___x_1474_,
                        v_infos_1460_,
                        v___x_1469_,
                    );
                if v_isShared_1458_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1457_, 0, v___x_1475_);
                    v___x_1477_ = v___x_1457_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1478_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1475_);
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
                    v_reuseFailAlloc_1486_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
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
    mut v_e_1491_: *mut crate::leanh::LeanObject,
    mut v_delab_1492_: *mut crate::leanh::LeanObject,
    mut v_a_1493_: *mut crate::leanh::LeanObject,
    mut v_a_1494_: *mut crate::leanh::LeanObject,
    mut v_a_1495_: *mut crate::leanh::LeanObject,
    mut v_a_1496_: *mut crate::leanh::LeanObject,
    mut v_a_1497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1498_ = l_Lean_Widget_ppExprTagged(
        v_e_1491_,
        v_delab_1492_,
        v_a_1493_,
        v_a_1494_,
        v_a_1495_,
        v_a_1496_,
    );
    crate::leanh::lean_dec(v_a_1496_);
    crate::leanh::lean_dec_ref(v_a_1495_);
    crate::leanh::lean_dec(v_a_1494_);
    crate::leanh::lean_dec_ref(v_a_1493_);
    return v_res_1498_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Widget_InteractiveCode(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Widget_TaggedText(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Widget_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Widget_InteractiveCode(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Widget_InteractiveCode(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Widget_TaggedText(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Widget_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Widget_InteractiveCode(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Widget_InteractiveCode(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Widget_InteractiveCode(builtin);
}
