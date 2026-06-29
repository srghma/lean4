// Lean compiler output
// Module: Lean.Data.Lsp.InitShutdown
// Imports: Lean.Data.Lsp.Capabilities Lean.Data.Lsp.Workspace
use crate::r#gen::Init::Control::Basic::l_instForInOfForIn_x27___redArg___lam__1;
use crate::r#gen::Init::Control::Except::{
    l_Except_bind, l_Except_instMonad___lam__0, l_Except_instMonad___lam__1,
    l_Except_instMonad___lam__2___boxed, l_Except_instMonad___lam__3, l_Except_map, l_Except_pure,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map,
    l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0,
    l_List_foldl___at___00Array_appendList_spec__0___redArg,
};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getBool_x3f, l_Lean_Json_getInt_x3f, l_Lean_Json_getObjValD,
    l_Lean_Json_getStr_x3f, l_Lean_Json_mkObj, l_Lean_JsonNumber_fromInt,
};
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::{
    l_Array_fromJson_x3f, l_Lean_Json_getObjValAs_x3f___redArg,
};
use crate::r#gen::Lean::Data::Lsp::Capabilities::{
    initialize_Lean_Data_Lsp_Capabilities, l_Lean_Lsp_instFromJsonClientCapabilities_fromJson,
    l_Lean_Lsp_instFromJsonServerCapabilities_fromJson,
    l_Lean_Lsp_instToJsonClientCapabilities_toJson, l_Lean_Lsp_instToJsonServerCapabilities_toJson,
    runtime_initialize_Lean_Data_Lsp_Capabilities,
};
use crate::r#gen::Lean::Data::Lsp::Workspace::{
    initialize_Lean_Data_Lsp_Workspace, l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson,
    l_Lean_Lsp_instToJsonWorkspaceFolder_toJson, runtime_initialize_Lean_Data_Lsp_Workspace,
};
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Basic::l_Std_DHashMap_Internal_AssocList_foldlM___redArg;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg;
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::ffi::lean_array_fset;
use crate::ffi::lean_string_append;
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_div, lean_nat_mul, lean_string_dec_eq, lean_string_hash, lean_usize_dec_eq,
};
pub static l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2_value: crate::leanh::LeanArrayObject<
    0,
> = crate::leanh::LeanArrayObject {
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
static mut l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonClientInfo___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonClientInfo_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonClientInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonClientInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonClientInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonClientInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__2_value:
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
    m_data: [67, 108, 105, 101, 110, 116, 73, 110, 102, 111, 0],
};
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__2_value)
            as *mut crate::leanh::LeanObject,
        3907392747204505285 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        5949480926448383572 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__12_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__13_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__12_value)
            as *mut crate::leanh::LeanObject,
        5707914067652744443 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonClientInfo___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonClientInfo_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonClientInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonClientInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTrace___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    14,
> = crate::leanh::LeanStringObject {
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
        117, 110, 107, 110, 111, 119, 110, 32, 116, 114, 97, 99, 101, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonTrace___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTrace___lam__0___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonTrace___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTrace___lam__0___closed__2_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [111, 102, 102, 0],
};
static mut l_Lean_Lsp_instFromJsonTrace___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTrace___lam__0___closed__3_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [109, 101, 115, 115, 97, 103, 101, 115, 0],
};
static mut l_Lean_Lsp_instFromJsonTrace___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTrace___lam__0___closed__4_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [118, 101, 114, 98, 111, 115, 101, 0],
};
static mut l_Lean_Lsp_instFromJsonTrace___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTrace___lam__0___closed__5_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
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
static mut l_Lean_Lsp_instFromJsonTrace___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTrace___lam__0___closed__6_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
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
static mut l_Lean_Lsp_instFromJsonTrace___lam__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTrace___lam__0___closed__7_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
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
static mut l_Lean_Lsp_instFromJsonTrace___lam__0___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonTrace___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonTrace___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonTrace___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonTrace: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_Trace_hasToJson___lam__0___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Lsp_Trace_hasToJson___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_Trace_hasToJson___lam__0___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Lsp_Trace_hasToJson___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_Trace_hasToJson___lam__0___closed__2_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Lsp_Trace_hasToJson___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_Trace_hasToJson___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_Trace_hasToJson___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_Trace_hasToJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_Trace_hasToJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_Trace_hasToJson: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_Trace_hasToJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__8_value:
    crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonHashSet___redArg___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonHashSet___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonHashSet___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__0_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instForInOfForIn_x27___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__4_value:
    crate::leanh::LeanStringObject<51> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 51,
    m_capacity: 51,
    m_length: 50,
    m_data: [
        69, 120, 112, 101, 99, 116, 101, 100, 32, 97, 114, 114, 97, 121, 32, 119, 104, 101, 110,
        32, 99, 111, 110, 118, 101, 114, 116, 105, 110, 103, 32, 74, 83, 79, 78, 32, 116, 111, 32,
        83, 116, 100, 46, 72, 97, 115, 104, 83, 101, 116, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___closed__0_value:
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
    m_fun: l_Except_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___closed__1_value:
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
    m_fun: l_Except_instMonad___lam__1 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___closed__2_value:
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
    m_fun: l_Except_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___closed__3_value:
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
    m_fun: l_Except_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___closed__4_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Except_map as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___closed__5_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___closed__6_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Except_pure as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___closed__7_value: crate::leanh::LeanCtorObject<
    5,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___closed__8_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Except_bind as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___closed__9_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__3_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [108, 111, 103, 68, 105, 114, 0],
};
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__1_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [76, 111, 103, 67, 111, 110, 102, 105, 103, 0],
};
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13822333033241362512 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__5_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [108, 111, 103, 68, 105, 114, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__6_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__5_value)
            as *mut crate::leanh::LeanObject,
        12006921733506407479 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__10_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
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
        97, 108, 108, 111, 119, 101, 100, 77, 101, 116, 104, 111, 100, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__11_value:
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
        97, 108, 108, 111, 119, 101, 100, 77, 101, 116, 104, 111, 100, 115, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__12_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__11_value)
            as *mut crate::leanh::LeanObject,
        2002671136272417502 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__16_value:
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
        100, 105, 115, 97, 108, 108, 111, 119, 101, 100, 77, 101, 116, 104, 111, 100, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__17_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        100, 105, 115, 97, 108, 108, 111, 119, 101, 100, 77, 101, 116, 104, 111, 100, 115, 63, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__18_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__17_value)
            as *mut crate::leanh::LeanObject,
        16624093685862140986 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__18_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLogConfig___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonLogConfig_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonLogConfig___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonLogConfig: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonLogConfig___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonLogConfig_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonLogConfig___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLogConfig___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonLogConfig: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLogConfig___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__0_value:
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
    m_data: [104, 97, 115, 87, 105, 100, 103, 101, 116, 115, 0],
};
static mut l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [108, 111, 103, 67, 102, 103, 0],
};
static mut l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonInitializationOptions___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonInitializationOptions_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonInitializationOptions___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializationOptions___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonInitializationOptions: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializationOptions___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__0_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        73, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 79, 112, 116, 105, 111,
        110, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7316217595702879692 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__4_value:
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
    m_data: [104, 97, 115, 87, 105, 100, 103, 101, 116, 115, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__4_value)
            as *mut crate::leanh::LeanObject,
        2865615965707119338 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__9_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [108, 111, 103, 67, 102, 103, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__10_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__9_value)
            as *mut crate::leanh::LeanObject,
        1435684361439067299 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonInitializationOptions___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonInitializationOptions_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonInitializationOptions___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonInitializationOptions: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__0_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [112, 114, 111, 99, 101, 115, 115, 73, 100, 0],
};
static mut l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__1_value:
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
    m_data: [99, 108, 105, 101, 110, 116, 73, 110, 102, 111, 0],
};
static mut l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__2_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [114, 111, 111, 116, 85, 114, 105, 0],
};
static mut l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__3_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 79, 112, 116, 105, 111,
        110, 115, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [99, 97, 112, 97, 98, 105, 108, 105, 116, 105, 101, 115, 0],
};
static mut l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__5_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 114, 97, 99, 101, 0],
};
static mut l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__6_value:
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
        119, 111, 114, 107, 115, 112, 97, 99, 101, 70, 111, 108, 100, 101, 114, 115, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonInitializeParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonInitializeParams_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonInitializeParams___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonInitializeParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializeParams___closed__0_value:
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
    m_fun: l_Lean_Json_getInt_x3f as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonInitializeParams___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializeParams___closed__1_value:
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
    m_fun: l_Lean_Json_getStr_x3f as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonInitializeParams___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializeParams___closed__2_value:
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
    m_fun: l_Lean_Lsp_instFromJsonClientCapabilities_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonInitializeParams___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializeParams___closed__3_value:
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
    m_fun: l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonInitializeParams___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializeParams___closed__4_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonInitializeParams___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializeParams___closed__5_value:
    crate::leanh::LeanClosureObject<7> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonInitializeParams___lam__0 as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 7,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonInitializeParams___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonInitializeParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializedParams___lam__0___closed__0_value:
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
static mut l_Lean_Lsp_instFromJsonInitializedParams___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializedParams___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializedParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonInitializedParams___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonInitializedParams___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializedParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonInitializedParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializedParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonInitializedParams___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonInitializedParams___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonInitializedParams___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializedParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonInitializedParams: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializedParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonServerInfo___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonServerInfo_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonServerInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonServerInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__0_value:
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
    m_data: [83, 101, 114, 118, 101, 114, 73, 110, 102, 111, 0],
};
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        213377184366943763 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonServerInfo___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonServerInfo_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonServerInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonServerInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonInitializeResult_toJson___closed__0_value:
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
    m_data: [115, 101, 114, 118, 101, 114, 73, 110, 102, 111, 0],
};
static mut l_Lean_Lsp_instToJsonInitializeResult_toJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeResult_toJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonInitializeResult___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonInitializeResult_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonInitializeResult___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeResult___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonInitializeResult: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeResult___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__0_value:
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
        73, 110, 105, 116, 105, 97, 108, 105, 122, 101, 82, 101, 115, 117, 108, 116, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1_value)
            as *mut crate::leanh::LeanObject,
        6773744487318448338 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__0_value)
            as *mut crate::leanh::LeanObject,
        4948849926862197272 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4_value)
            as *mut crate::leanh::LeanObject,
        18164368300990074274 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__8_value:
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
    m_data: [115, 101, 114, 118, 101, 114, 73, 110, 102, 111, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__9_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__8_value)
            as *mut crate::leanh::LeanObject,
        1486792206322009551 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonInitializeResult___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonInitializeResult_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonInitializeResult___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeResult___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonInitializeResult: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeResult___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__0(
    mut v_k_1613_: *mut crate::leanh::LeanObject,
    mut v_x_1614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1619_: u8 = 0;
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1626_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1614_) == 0 {
                    crate::leanh::lean_dec_ref(v_k_1613_);
                    v___x_1615_ = crate::leanh::lean_box(0);
                    return v___x_1615_;
                } else {
                    v_val_1616_ = crate::leanh::lean_ctor_get(v_x_1614_, 0);
                    v_isSharedCheck_1626_ = (!crate::leanh::lean_is_exclusive(v_x_1614_)) as u8;
                    if v_isSharedCheck_1626_ == 0 {
                        v___x_1618_ = v_x_1614_;
                        v_isShared_1619_ = v_isSharedCheck_1626_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1616_);
                        crate::leanh::lean_dec(v_x_1614_);
                        v___x_1618_ = crate::leanh::lean_box(0);
                        v_isShared_1619_ = v_isSharedCheck_1626_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1619_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1618_, 3);
                    v___x_1621_ = v___x_1618_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1625_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_val_1616_);
                    v___x_1621_ = v_reuseFailAlloc_1625_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1622_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1622_, 0, v_k_1613_);
                crate::leanh::lean_ctor_set(v___x_1622_, 1, v___x_1621_);
                v___x_1623_ = crate::leanh::lean_box(0);
                v___x_1624_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1624_, 0, v___x_1622_);
                crate::leanh::lean_ctor_set(v___x_1624_, 1, v___x_1623_);
                return v___x_1624_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(
    mut v_a_1627_: *mut crate::leanh::LeanObject,
    mut v_a_1628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1627_) == 0 {
                    v___x_1629_ = lean_array_to_list(v_a_1628_);
                    return v___x_1629_;
                } else {
                    v_head_1630_ = crate::leanh::lean_ctor_get(v_a_1627_, 0);
                    crate::leanh::lean_inc(v_head_1630_);
                    v_tail_1631_ = crate::leanh::lean_ctor_get(v_a_1627_, 1);
                    crate::leanh::lean_inc(v_tail_1631_);
                    crate::leanh::lean_dec_ref_known(v_a_1627_, 2);
                    v___x_1632_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_1628_,
                        v_head_1630_,
                    );
                    v_a_1627_ = v_tail_1631_;
                    v_a_1628_ = v___x_1632_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonClientInfo_toJson(
    mut v_x_1638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_x3f_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1643_: u8 = 0;
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1658_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_1639_ = crate::leanh::lean_ctor_get(v_x_1638_, 0);
                v_version_x3f_1640_ = crate::leanh::lean_ctor_get(v_x_1638_, 1);
                v_isSharedCheck_1658_ = (!crate::leanh::lean_is_exclusive(v_x_1638_)) as u8;
                if v_isSharedCheck_1658_ == 0 {
                    v___x_1642_ = v_x_1638_;
                    v_isShared_1643_ = v_isSharedCheck_1658_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_version_x3f_1640_);
                    crate::leanh::lean_inc(v_name_1639_);
                    crate::leanh::lean_dec(v_x_1638_);
                    v___x_1642_ = crate::leanh::lean_box(0);
                    v_isShared_1643_ = v_isSharedCheck_1658_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1644_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0;
                v___x_1645_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1645_, 0, v_name_1639_);
                if v_isShared_1643_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1642_, 1, v___x_1645_);
                    crate::leanh::lean_ctor_set(v___x_1642_, 0, v___x_1644_);
                    v___x_1647_ = v___x_1642_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1657_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1657_, 1, v___x_1645_);
                    v___x_1647_ = v_reuseFailAlloc_1657_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1648_ = crate::leanh::lean_box(0);
                v___x_1649_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1649_, 0, v___x_1647_);
                crate::leanh::lean_ctor_set(v___x_1649_, 1, v___x_1648_);
                v___x_1650_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1;
                v___x_1651_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__0(
                    v___x_1650_,
                    v_version_x3f_1640_,
                );
                v___x_1652_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1652_, 0, v___x_1651_);
                crate::leanh::lean_ctor_set(v___x_1652_, 1, v___x_1648_);
                v___x_1653_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1653_, 0, v___x_1649_);
                crate::leanh::lean_ctor_set(v___x_1653_, 1, v___x_1652_);
                v___x_1654_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2;
                v___x_1655_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_1653_, v___x_1654_);
                v___x_1656_ = l_Lean_Json_mkObj(v___x_1655_);
                crate::leanh::lean_dec(v___x_1655_);
                return v___x_1656_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__0(
    mut v_j_1661_: *mut crate::leanh::LeanObject,
    mut v_k_1662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1663_ = l_Lean_Json_getObjValD(v_j_1661_, v_k_1662_);
    v___x_1664_ = l_Lean_Json_getStr_x3f(v___x_1663_);
    return v___x_1664_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__0___boxed(
    mut v_j_1665_: *mut crate::leanh::LeanObject,
    mut v_k_1666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1667_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__0(
            v_j_1665_, v_k_1666_,
        );
    crate::leanh::lean_dec_ref(v_k_1666_);
    return v_res_1667_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1(
    mut v_x_1670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1676_: u8 = 0;
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1680_: u8 = 0;
    let mut v_a_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1684_: u8 = 0;
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1689_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1670_) == 0 {
                    v___x_1671_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1___closed__0;
                    return v___x_1671_;
                } else {
                    v___x_1672_ = l_Lean_Json_getStr_x3f(v_x_1670_);
                    if crate::leanh::lean_obj_tag(v___x_1672_) == 0 {
                        v_a_1673_ = crate::leanh::lean_ctor_get(v___x_1672_, 0);
                        v_isSharedCheck_1680_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1672_)) as u8;
                        if v_isSharedCheck_1680_ == 0 {
                            v___x_1675_ = v___x_1672_;
                            v_isShared_1676_ = v_isSharedCheck_1680_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1673_);
                            crate::leanh::lean_dec(v___x_1672_);
                            v___x_1675_ = crate::leanh::lean_box(0);
                            v_isShared_1676_ = v_isSharedCheck_1680_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1681_ = crate::leanh::lean_ctor_get(v___x_1672_, 0);
                        v_isSharedCheck_1689_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1672_)) as u8;
                        if v_isSharedCheck_1689_ == 0 {
                            v___x_1683_ = v___x_1672_;
                            v_isShared_1684_ = v_isSharedCheck_1689_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1681_);
                            crate::leanh::lean_dec(v___x_1672_);
                            v___x_1683_ = crate::leanh::lean_box(0);
                            v_isShared_1684_ = v_isSharedCheck_1689_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1676_ == 0 {
                    v___x_1678_ = v___x_1675_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1679_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
                    v___x_1678_ = v_reuseFailAlloc_1679_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1678_;
            }
            3 => {
                v___x_1685_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1685_, 0, v_a_1681_);
                if v_isShared_1684_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1683_, 0, v___x_1685_);
                    v___x_1687_ = v___x_1683_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1688_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1685_);
                    v___x_1687_ = v_reuseFailAlloc_1688_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1687_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1(
    mut v_j_1690_: *mut crate::leanh::LeanObject,
    mut v_k_1691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1692_ = l_Lean_Json_getObjValD(v_j_1690_, v_k_1691_);
    v___x_1693_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1(v___x_1692_);
    return v___x_1693_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1___boxed(
    mut v_j_1694_: *mut crate::leanh::LeanObject,
    mut v_k_1695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1696_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1(
            v_j_1694_, v_k_1695_,
        );
    crate::leanh::lean_dec_ref(v_k_1695_);
    return v_res_1696_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1704_: u8 = 0;
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1704_ = 1;
    v___x_1705_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3;
    v___x_1706_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1705_, v___x_1704_);
    return v___x_1706_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1708_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5;
    v___x_1709_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__4,
    );
    v___x_1710_ = lean_string_append(v___x_1709_, v___x_1708_);
    return v___x_1710_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1713_: u8 = 0;
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1713_ = 1;
    v___x_1714_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__7;
    v___x_1715_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1714_, v___x_1713_);
    return v___x_1715_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1716_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8_once),
        _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8,
    );
    v___x_1717_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6,
    );
    v___x_1718_ = lean_string_append(v___x_1717_, v___x_1716_);
    return v___x_1718_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1720_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10;
    v___x_1721_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__9_once),
        _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__9,
    );
    v___x_1722_ = lean_string_append(v___x_1721_, v___x_1720_);
    return v___x_1722_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1726_: u8 = 0;
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1726_ = 1;
    v___x_1727_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__13;
    v___x_1728_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1727_, v___x_1726_);
    return v___x_1728_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1729_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14_once),
        _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14,
    );
    v___x_1730_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6,
    );
    v___x_1731_ = lean_string_append(v___x_1730_, v___x_1729_);
    return v___x_1731_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1732_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10;
    v___x_1733_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__15_once),
        _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__15,
    );
    v___x_1734_ = lean_string_append(v___x_1733_, v___x_1732_);
    return v___x_1734_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonClientInfo_fromJson(
    mut v_json_1735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1741_: u8 = 0;
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1747_: u8 = 0;
    let mut v_a_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1751_: u8 = 0;
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1755_: u8 = 0;
    let mut v_a_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1762_: u8 = 0;
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1768_: u8 = 0;
    let mut v_a_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1772_: u8 = 0;
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1776_: u8 = 0;
    let mut v_a_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1780_: u8 = 0;
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1785_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1736_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0;
                crate::leanh::lean_inc(v_json_1735_);
                v___x_1737_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__0(v_json_1735_, v___x_1736_);
                if crate::leanh::lean_obj_tag(v___x_1737_) == 0 {
                    crate::leanh::lean_dec(v_json_1735_);
                    v_a_1738_ = crate::leanh::lean_ctor_get(v___x_1737_, 0);
                    v_isSharedCheck_1747_ = (!crate::leanh::lean_is_exclusive(v___x_1737_)) as u8;
                    if v_isSharedCheck_1747_ == 0 {
                        v___x_1740_ = v___x_1737_;
                        v_isShared_1741_ = v_isSharedCheck_1747_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1738_);
                        crate::leanh::lean_dec(v___x_1737_);
                        v___x_1740_ = crate::leanh::lean_box(0);
                        v_isShared_1741_ = v_isSharedCheck_1747_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_1737_) == 0 {
                        crate::leanh::lean_dec(v_json_1735_);
                        v_a_1748_ = crate::leanh::lean_ctor_get(v___x_1737_, 0);
                        v_isSharedCheck_1755_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1737_)) as u8;
                        if v_isSharedCheck_1755_ == 0 {
                            v___x_1750_ = v___x_1737_;
                            v_isShared_1751_ = v_isSharedCheck_1755_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1748_);
                            crate::leanh::lean_dec(v___x_1737_);
                            v___x_1750_ = crate::leanh::lean_box(0);
                            v_isShared_1751_ = v_isSharedCheck_1755_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1756_ = crate::leanh::lean_ctor_get(v___x_1737_, 0);
                        crate::leanh::lean_inc(v_a_1756_);
                        crate::leanh::lean_dec_ref_known(v___x_1737_, 1);
                        v___x_1757_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1;
                        v___x_1758_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1(v_json_1735_, v___x_1757_);
                        if crate::leanh::lean_obj_tag(v___x_1758_) == 0 {
                            crate::leanh::lean_dec(v_a_1756_);
                            v_a_1759_ = crate::leanh::lean_ctor_get(v___x_1758_, 0);
                            v_isSharedCheck_1768_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1758_)) as u8;
                            if v_isSharedCheck_1768_ == 0 {
                                v___x_1761_ = v___x_1758_;
                                v_isShared_1762_ = v_isSharedCheck_1768_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1759_);
                                crate::leanh::lean_dec(v___x_1758_);
                                v___x_1761_ = crate::leanh::lean_box(0);
                                v_isShared_1762_ = v_isSharedCheck_1768_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_1758_) == 0 {
                                crate::leanh::lean_dec(v_a_1756_);
                                v_a_1769_ = crate::leanh::lean_ctor_get(v___x_1758_, 0);
                                v_isSharedCheck_1776_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1758_)) as u8;
                                if v_isSharedCheck_1776_ == 0 {
                                    v___x_1771_ = v___x_1758_;
                                    v_isShared_1772_ = v_isSharedCheck_1776_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1769_);
                                    crate::leanh::lean_dec(v___x_1758_);
                                    v___x_1771_ = crate::leanh::lean_box(0);
                                    v_isShared_1772_ = v_isSharedCheck_1776_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_1777_ = crate::leanh::lean_ctor_get(v___x_1758_, 0);
                                v_isSharedCheck_1785_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1758_)) as u8;
                                if v_isSharedCheck_1785_ == 0 {
                                    v___x_1779_ = v___x_1758_;
                                    v_isShared_1780_ = v_isSharedCheck_1785_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1777_);
                                    crate::leanh::lean_dec(v___x_1758_);
                                    v___x_1779_ = crate::leanh::lean_box(0);
                                    v_isShared_1780_ = v_isSharedCheck_1785_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1742_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__11_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__11,
                );
                v___x_1743_ = lean_string_append(v___x_1742_, v_a_1738_);
                crate::leanh::lean_dec(v_a_1738_);
                if v_isShared_1741_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1740_, 0, v___x_1743_);
                    v___x_1745_ = v___x_1740_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1746_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
                    v___x_1745_ = v_reuseFailAlloc_1746_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1745_;
            }
            3 => {
                if v_isShared_1751_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1750_, 0);
                    v___x_1753_ = v___x_1750_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1754_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
                    v___x_1753_ = v_reuseFailAlloc_1754_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1753_;
            }
            5 => {
                v___x_1763_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__16
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__16_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__16,
                );
                v___x_1764_ = lean_string_append(v___x_1763_, v_a_1759_);
                crate::leanh::lean_dec(v_a_1759_);
                if v_isShared_1762_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1761_, 0, v___x_1764_);
                    v___x_1766_ = v___x_1761_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1767_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
                    v___x_1766_ = v_reuseFailAlloc_1767_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1766_;
            }
            7 => {
                if v_isShared_1772_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1771_, 0);
                    v___x_1774_ = v___x_1771_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1775_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
                    v___x_1774_ = v_reuseFailAlloc_1775_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1774_;
            }
            9 => {
                v___x_1781_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1781_, 0, v_a_1756_);
                crate::leanh::lean_ctor_set(v___x_1781_, 1, v_a_1777_);
                if v_isShared_1780_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1779_, 0, v___x_1781_);
                    v___x_1783_ = v___x_1779_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1784_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1781_);
                    v___x_1783_ = v_reuseFailAlloc_1784_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1783_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_Trace_ctorIdx(mut v_x_1788_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_1788_ {
        0 => {
            let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1789_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1789_;
        }
        1 => {
            let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1790_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1790_;
        }
        _ => {
            let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1791_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1791_;
        }
    }
}
pub unsafe fn l_Lean_Lsp_Trace_ctorIdx___boxed(
    mut v_x_1792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1793_: u8 = 0;
    let mut v_res_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1793_ = (crate::leanh::lean_unbox(v_x_1792_) as u8);
    v_res_1794_ = l_Lean_Lsp_Trace_ctorIdx(v_x_boxed_1793_);
    return v_res_1794_;
}
pub unsafe fn l_Lean_Lsp_Trace_toCtorIdx(mut v_x_1795_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1796_ = l_Lean_Lsp_Trace_ctorIdx(v_x_1795_);
    return v___x_1796_;
}
pub unsafe fn l_Lean_Lsp_Trace_toCtorIdx___boxed(
    mut v_x_1797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_1798_: u8 = 0;
    let mut v_res_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1798_ = (crate::leanh::lean_unbox(v_x_1797_) as u8);
    v_res_1799_ = l_Lean_Lsp_Trace_toCtorIdx(v_x_4__boxed_1798_);
    return v_res_1799_;
}
pub unsafe fn l_Lean_Lsp_Trace_ctorElim___redArg(
    mut v_k_1800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1800_);
    return v_k_1800_;
}
pub unsafe fn l_Lean_Lsp_Trace_ctorElim___redArg___boxed(
    mut v_k_1801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1802_ = l_Lean_Lsp_Trace_ctorElim___redArg(v_k_1801_);
    crate::leanh::lean_dec(v_k_1801_);
    return v_res_1802_;
}
pub unsafe fn l_Lean_Lsp_Trace_ctorElim(
    mut v_motive_1803_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1804_: *mut crate::leanh::LeanObject,
    mut v_t_1805_: u8,
    mut v_h_1806_: *mut crate::leanh::LeanObject,
    mut v_k_1807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1807_);
    return v_k_1807_;
}
pub unsafe fn l_Lean_Lsp_Trace_ctorElim___boxed(
    mut v_motive_1808_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1809_: *mut crate::leanh::LeanObject,
    mut v_t_1810_: *mut crate::leanh::LeanObject,
    mut v_h_1811_: *mut crate::leanh::LeanObject,
    mut v_k_1812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1813_: u8 = 0;
    let mut v_res_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1813_ = (crate::leanh::lean_unbox(v_t_1810_) as u8);
    v_res_1814_ = l_Lean_Lsp_Trace_ctorElim(
        v_motive_1808_,
        v_ctorIdx_1809_,
        v_t_boxed_1813_,
        v_h_1811_,
        v_k_1812_,
    );
    crate::leanh::lean_dec(v_k_1812_);
    crate::leanh::lean_dec(v_ctorIdx_1809_);
    return v_res_1814_;
}
pub unsafe fn l_Lean_Lsp_Trace_off_elim___redArg(
    mut v_off_1815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_off_1815_);
    return v_off_1815_;
}
pub unsafe fn l_Lean_Lsp_Trace_off_elim___redArg___boxed(
    mut v_off_1816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1817_ = l_Lean_Lsp_Trace_off_elim___redArg(v_off_1816_);
    crate::leanh::lean_dec(v_off_1816_);
    return v_res_1817_;
}
pub unsafe fn l_Lean_Lsp_Trace_off_elim(
    mut v_motive_1818_: *mut crate::leanh::LeanObject,
    mut v_t_1819_: u8,
    mut v_h_1820_: *mut crate::leanh::LeanObject,
    mut v_off_1821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_off_1821_);
    return v_off_1821_;
}
pub unsafe fn l_Lean_Lsp_Trace_off_elim___boxed(
    mut v_motive_1822_: *mut crate::leanh::LeanObject,
    mut v_t_1823_: *mut crate::leanh::LeanObject,
    mut v_h_1824_: *mut crate::leanh::LeanObject,
    mut v_off_1825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1826_: u8 = 0;
    let mut v_res_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1826_ = (crate::leanh::lean_unbox(v_t_1823_) as u8);
    v_res_1827_ =
        l_Lean_Lsp_Trace_off_elim(v_motive_1822_, v_t_boxed_1826_, v_h_1824_, v_off_1825_);
    crate::leanh::lean_dec(v_off_1825_);
    return v_res_1827_;
}
pub unsafe fn l_Lean_Lsp_Trace_messages_elim___redArg(
    mut v_messages_1828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_messages_1828_);
    return v_messages_1828_;
}
pub unsafe fn l_Lean_Lsp_Trace_messages_elim___redArg___boxed(
    mut v_messages_1829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1830_ = l_Lean_Lsp_Trace_messages_elim___redArg(v_messages_1829_);
    crate::leanh::lean_dec(v_messages_1829_);
    return v_res_1830_;
}
pub unsafe fn l_Lean_Lsp_Trace_messages_elim(
    mut v_motive_1831_: *mut crate::leanh::LeanObject,
    mut v_t_1832_: u8,
    mut v_h_1833_: *mut crate::leanh::LeanObject,
    mut v_messages_1834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_messages_1834_);
    return v_messages_1834_;
}
pub unsafe fn l_Lean_Lsp_Trace_messages_elim___boxed(
    mut v_motive_1835_: *mut crate::leanh::LeanObject,
    mut v_t_1836_: *mut crate::leanh::LeanObject,
    mut v_h_1837_: *mut crate::leanh::LeanObject,
    mut v_messages_1838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1839_: u8 = 0;
    let mut v_res_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1839_ = (crate::leanh::lean_unbox(v_t_1836_) as u8);
    v_res_1840_ = l_Lean_Lsp_Trace_messages_elim(
        v_motive_1835_,
        v_t_boxed_1839_,
        v_h_1837_,
        v_messages_1838_,
    );
    crate::leanh::lean_dec(v_messages_1838_);
    return v_res_1840_;
}
pub unsafe fn l_Lean_Lsp_Trace_verbose_elim___redArg(
    mut v_verbose_1841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_verbose_1841_);
    return v_verbose_1841_;
}
pub unsafe fn l_Lean_Lsp_Trace_verbose_elim___redArg___boxed(
    mut v_verbose_1842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1843_ = l_Lean_Lsp_Trace_verbose_elim___redArg(v_verbose_1842_);
    crate::leanh::lean_dec(v_verbose_1842_);
    return v_res_1843_;
}
pub unsafe fn l_Lean_Lsp_Trace_verbose_elim(
    mut v_motive_1844_: *mut crate::leanh::LeanObject,
    mut v_t_1845_: u8,
    mut v_h_1846_: *mut crate::leanh::LeanObject,
    mut v_verbose_1847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_verbose_1847_);
    return v_verbose_1847_;
}
pub unsafe fn l_Lean_Lsp_Trace_verbose_elim___boxed(
    mut v_motive_1848_: *mut crate::leanh::LeanObject,
    mut v_t_1849_: *mut crate::leanh::LeanObject,
    mut v_h_1850_: *mut crate::leanh::LeanObject,
    mut v_verbose_1851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1852_: u8 = 0;
    let mut v_res_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1852_ = (crate::leanh::lean_unbox(v_t_1849_) as u8);
    v_res_1853_ =
        l_Lean_Lsp_Trace_verbose_elim(v_motive_1848_, v_t_boxed_1852_, v_h_1850_, v_verbose_1851_);
    crate::leanh::lean_dec(v_verbose_1851_);
    return v_res_1853_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonTrace___lam__0(
    mut v_j_1869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: u8 = 0;
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: u8 = 0;
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: u8 = 0;
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1872_ = l_Lean_Json_getStr_x3f(v_j_1869_);
                if crate::leanh::lean_obj_tag(v___x_1872_) == 1 {
                    v_a_1873_ = crate::leanh::lean_ctor_get(v___x_1872_, 0);
                    crate::leanh::lean_inc(v_a_1873_);
                    crate::leanh::lean_dec_ref_known(v___x_1872_, 1);
                    v___x_1874_ = l_Lean_Lsp_instFromJsonTrace___lam__0___closed__2;
                    v___x_1875_ = lean_string_dec_eq(v_a_1873_, v___x_1874_);
                    if v___x_1875_ == 0 {
                        v___x_1876_ = l_Lean_Lsp_instFromJsonTrace___lam__0___closed__3;
                        v___x_1877_ = lean_string_dec_eq(v_a_1873_, v___x_1876_);
                        if v___x_1877_ == 0 {
                            v___x_1878_ = l_Lean_Lsp_instFromJsonTrace___lam__0___closed__4;
                            v___x_1879_ = lean_string_dec_eq(v_a_1873_, v___x_1878_);
                            crate::leanh::lean_dec(v_a_1873_);
                            if v___x_1879_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                v___x_1880_ = l_Lean_Lsp_instFromJsonTrace___lam__0___closed__5;
                                return v___x_1880_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1873_);
                            v___x_1881_ = l_Lean_Lsp_instFromJsonTrace___lam__0___closed__6;
                            return v___x_1881_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1873_);
                        v___x_1882_ = l_Lean_Lsp_instFromJsonTrace___lam__0___closed__7;
                        return v___x_1882_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1872_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1871_ = l_Lean_Lsp_instFromJsonTrace___lam__0___closed__1;
                return v___x_1871_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_Trace_hasToJson___lam__0(
    mut v_x_1891_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_1891_ {
        0 => {
            let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1892_ = l_Lean_Lsp_Trace_hasToJson___lam__0___closed__0;
            return v___x_1892_;
        }
        1 => {
            let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1893_ = l_Lean_Lsp_Trace_hasToJson___lam__0___closed__1;
            return v___x_1893_;
        }
        _ => {
            let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1894_ = l_Lean_Lsp_Trace_hasToJson___lam__0___closed__2;
            return v___x_1894_;
        }
    }
}
pub unsafe fn l_Lean_Lsp_Trace_hasToJson___lam__0___boxed(
    mut v_x_1895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_54__boxed_1896_: u8 = 0;
    let mut v_res_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_54__boxed_1896_ = (crate::leanh::lean_unbox(v_x_1895_) as u8);
    v_res_1897_ = l_Lean_Lsp_Trace_hasToJson___lam__0(v_x_54__boxed_1896_);
    return v_res_1897_;
}
pub unsafe fn l_Lean_Lsp_instToJsonHashSet___redArg___lam__0(
    mut v_x1_1900_: *mut crate::leanh::LeanObject,
    mut v_x2_1901_: *mut crate::leanh::LeanObject,
    mut v_x3_1902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1903_ = lean_array_push(v_x1_1900_, v_x2_1901_);
    return v___x_1903_;
}
pub unsafe fn l_Lean_Lsp_instToJsonHashSet___redArg___lam__1(
    mut v_inst_1904_: *mut crate::leanh::LeanObject,
    mut v_x_1905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1906_ = crate::leanh::lean_apply_1(v_inst_1904_, v_x_1905_);
    return v___x_1906_;
}
pub unsafe fn l_Lean_Lsp_instToJsonHashSet___redArg___lam__2(
    mut v___x_1907_: *mut crate::leanh::LeanObject,
    mut v___f_1908_: *mut crate::leanh::LeanObject,
    mut v_acc_1909_: *mut crate::leanh::LeanObject,
    mut v_l_1910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1911_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_1907_,
        v___f_1908_,
        v_acc_1909_,
        v_l_1910_,
    );
    return v___x_1911_;
}
pub unsafe fn l_Lean_Lsp_instToJsonHashSet___redArg___lam__3(
    mut v___f_1931_: *mut crate::leanh::LeanObject,
    mut v___f_1932_: *mut crate::leanh::LeanObject,
    mut v_s_1933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1937_: usize = 0;
    let mut v___x_1938_: usize = 0;
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: u8 = 0;
    let mut v___f_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: u8 = 0;
    let mut v___x_1950_: usize = 0;
    let mut v___x_1951_: usize = 0;
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: usize = 0;
    let mut v___x_1954_: usize = 0;
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1941_ = crate::leanh::lean_ctor_get(v_s_1933_, 0);
                crate::leanh::lean_inc(v_size_1941_);
                v_buckets_1942_ = crate::leanh::lean_ctor_get(v_s_1933_, 1);
                crate::leanh::lean_inc_ref(v_buckets_1942_);
                crate::leanh::lean_dec_ref(v_s_1933_);
                v___x_1943_ = lean_mk_empty_array_with_capacity(v_size_1941_);
                crate::leanh::lean_dec(v_size_1941_);
                v___x_1944_ = l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__9;
                v___x_1945_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1946_ = lean_array_get_size(v_buckets_1942_);
                v___x_1947_ = lean_nat_dec_lt(v___x_1945_, v___x_1946_);
                if v___x_1947_ == 0 {
                    crate::leanh::lean_dec_ref(v_buckets_1942_);
                    crate::leanh::lean_dec_ref(v___f_1932_);
                    v___y_1935_ = v___x_1943_;
                    state = 1;
                    continue;
                } else {
                    v___f_1948_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Lsp_instToJsonHashSet___redArg___lam__2 as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_1948_, 0, v___x_1944_);
                    crate::leanh::lean_closure_set(v___f_1948_, 1, v___f_1932_);
                    v___x_1949_ = lean_nat_dec_le(v___x_1946_, v___x_1946_);
                    if v___x_1949_ == 0 {
                        if v___x_1947_ == 0 {
                            crate::leanh::lean_dec_ref(v___f_1948_);
                            crate::leanh::lean_dec_ref(v_buckets_1942_);
                            v___y_1935_ = v___x_1943_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1950_ = 0usize;
                            v___x_1951_ = lean_usize_of_nat(v___x_1946_);
                            v___x_1952_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_1944_,
                                    v___f_1948_,
                                    v_buckets_1942_,
                                    v___x_1950_,
                                    v___x_1951_,
                                    v___x_1943_,
                                );
                            v___y_1935_ = v___x_1952_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1953_ = 0usize;
                        v___x_1954_ = lean_usize_of_nat(v___x_1946_);
                        v___x_1955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_1944_,
                            v___f_1948_,
                            v_buckets_1942_,
                            v___x_1953_,
                            v___x_1954_,
                            v___x_1943_,
                        );
                        v___y_1935_ = v___x_1955_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1936_ = l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__9;
                v_sz_1937_ = lean_array_size(v___y_1935_);
                v___x_1938_ = 0usize;
                v___x_1939_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1936_,
                    v___f_1931_,
                    v_sz_1937_,
                    v___x_1938_,
                    v___y_1935_,
                );
                v___x_1940_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1940_, 0, v___x_1939_);
                return v___x_1940_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonHashSet___redArg(
    mut v_inst_1957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1958_ = l_Lean_Lsp_instToJsonHashSet___redArg___closed__0;
    v___f_1959_ = crate::leanh::lean_alloc_closure(
        l_Lean_Lsp_instToJsonHashSet___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1959_, 0, v_inst_1957_);
    v___f_1960_ = crate::leanh::lean_alloc_closure(
        l_Lean_Lsp_instToJsonHashSet___redArg___lam__3 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1960_, 0, v___f_1959_);
    crate::leanh::lean_closure_set(v___f_1960_, 1, v___f_1958_);
    return v___f_1960_;
}
pub unsafe fn l_Lean_Lsp_instToJsonHashSet(
    mut v_00_u03b1_1961_: *mut crate::leanh::LeanObject,
    mut v_inst_1962_: *mut crate::leanh::LeanObject,
    mut v_inst_1963_: *mut crate::leanh::LeanObject,
    mut v_inst_1964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1965_ = l_Lean_Lsp_instToJsonHashSet___redArg(v_inst_1964_);
    return v___x_1965_;
}
pub unsafe fn l_Lean_Lsp_instToJsonHashSet___boxed(
    mut v_00_u03b1_1966_: *mut crate::leanh::LeanObject,
    mut v_inst_1967_: *mut crate::leanh::LeanObject,
    mut v_inst_1968_: *mut crate::leanh::LeanObject,
    mut v_inst_1969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1970_ =
        l_Lean_Lsp_instToJsonHashSet(v_00_u03b1_1966_, v_inst_1967_, v_inst_1968_, v_inst_1969_);
    crate::leanh::lean_dec_ref(v_inst_1968_);
    crate::leanh::lean_dec_ref(v_inst_1967_);
    return v_res_1970_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1975_ = crate::leanh::lean_box(0);
    v___x_1976_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1977_ = lean_mk_array(v___x_1976_, v___x_1975_);
    return v___x_1977_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1978_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2_once),
        _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2,
    );
    v___x_1979_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1980_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1980_, 0, v___x_1979_);
    crate::leanh::lean_ctor_set(v___x_1980_, 1, v___x_1978_);
    return v___x_1980_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0(
    mut v___x_1984_: *mut crate::leanh::LeanObject,
    mut v_inst_1985_: *mut crate::leanh::LeanObject,
    mut v_inst_1986_: *mut crate::leanh::LeanObject,
    mut v_inst_1987_: *mut crate::leanh::LeanObject,
    mut v_x_1988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_elems_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1990_: usize = 0;
    let mut v___x_1991_: usize = 0;
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1996_: u8 = 0;
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2000_: u8 = 0;
    let mut v_a_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2004_: u8 = 0;
    let mut v___f_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2011_: u8 = 0;
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1988_) == 4 {
                    v_elems_1989_ = crate::leanh::lean_ctor_get(v_x_1988_, 0);
                    crate::leanh::lean_inc_ref(v_elems_1989_);
                    crate::leanh::lean_dec_ref_known(v_x_1988_, 1);
                    v_sz_1990_ = lean_array_size(v_elems_1989_);
                    v___x_1991_ = 0usize;
                    v___x_1992_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_1984_,
                        v_inst_1985_,
                        v_sz_1990_,
                        v___x_1991_,
                        v_elems_1989_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1992_) == 0 {
                        crate::leanh::lean_dec_ref(v_inst_1987_);
                        crate::leanh::lean_dec_ref(v_inst_1986_);
                        v_a_1993_ = crate::leanh::lean_ctor_get(v___x_1992_, 0);
                        v_isSharedCheck_2000_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1992_)) as u8;
                        if v_isSharedCheck_2000_ == 0 {
                            v___x_1995_ = v___x_1992_;
                            v_isShared_1996_ = v_isSharedCheck_2000_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1993_);
                            crate::leanh::lean_dec(v___x_1992_);
                            v___x_1995_ = crate::leanh::lean_box(0);
                            v_isShared_1996_ = v_isSharedCheck_2000_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2001_ = crate::leanh::lean_ctor_get(v___x_1992_, 0);
                        v_isSharedCheck_2011_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1992_)) as u8;
                        if v_isSharedCheck_2011_ == 0 {
                            v___x_2003_ = v___x_1992_;
                            v_isShared_2004_ = v_isSharedCheck_2011_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2001_);
                            crate::leanh::lean_dec(v___x_1992_);
                            v___x_2003_ = crate::leanh::lean_box(0);
                            v_isShared_2004_ = v_isSharedCheck_2011_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_x_1988_);
                    crate::leanh::lean_dec_ref(v_inst_1987_);
                    crate::leanh::lean_dec_ref(v_inst_1986_);
                    crate::leanh::lean_dec_ref(v_inst_1985_);
                    crate::leanh::lean_dec_ref(v___x_1984_);
                    v___x_2012_ = l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__5;
                    return v___x_2012_;
                }
            }
            1 => {
                if v_isShared_1996_ == 0 {
                    v___x_1998_ = v___x_1995_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1999_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
                    v___x_1998_ = v_reuseFailAlloc_1999_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1998_;
            }
            3 => {
                v___f_2005_ = l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__1;
                v___x_2006_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3,
                );
                v___x_2007_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
                    v___f_2005_,
                    v_inst_1986_,
                    v_inst_1987_,
                    v___x_2006_,
                    v_a_2001_,
                );
                if v_isShared_2004_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2003_, 0, v___x_2007_);
                    v___x_2009_ = v___x_2003_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2010_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2007_);
                    v___x_2009_ = v_reuseFailAlloc_2010_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2009_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instFromJsonHashSet___redArg(
    mut v_inst_2032_: *mut crate::leanh::LeanObject,
    mut v_inst_2033_: *mut crate::leanh::LeanObject,
    mut v_inst_2034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2035_ = l_Lean_Lsp_instFromJsonHashSet___redArg___closed__9;
    v___f_2036_ = crate::leanh::lean_alloc_closure(
        l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2036_, 0, v___x_2035_);
    crate::leanh::lean_closure_set(v___f_2036_, 1, v_inst_2034_);
    crate::leanh::lean_closure_set(v___f_2036_, 2, v_inst_2032_);
    crate::leanh::lean_closure_set(v___f_2036_, 3, v_inst_2033_);
    return v___f_2036_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonHashSet(
    mut v_00_u03b1_2037_: *mut crate::leanh::LeanObject,
    mut v_inst_2038_: *mut crate::leanh::LeanObject,
    mut v_inst_2039_: *mut crate::leanh::LeanObject,
    mut v_inst_2040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2041_ = l_Lean_Lsp_instFromJsonHashSet___redArg(v_inst_2038_, v_inst_2039_, v_inst_2040_);
    return v___x_2041_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0_spec__0(
    mut v_x_2042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2048_: u8 = 0;
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2052_: u8 = 0;
    let mut v_a_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2056_: u8 = 0;
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2061_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2042_) == 0 {
                    v___x_2043_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1___closed__0;
                    return v___x_2043_;
                } else {
                    v___x_2044_ = l_Lean_Json_getStr_x3f(v_x_2042_);
                    if crate::leanh::lean_obj_tag(v___x_2044_) == 0 {
                        v_a_2045_ = crate::leanh::lean_ctor_get(v___x_2044_, 0);
                        v_isSharedCheck_2052_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2044_)) as u8;
                        if v_isSharedCheck_2052_ == 0 {
                            v___x_2047_ = v___x_2044_;
                            v_isShared_2048_ = v_isSharedCheck_2052_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2045_);
                            crate::leanh::lean_dec(v___x_2044_);
                            v___x_2047_ = crate::leanh::lean_box(0);
                            v_isShared_2048_ = v_isSharedCheck_2052_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2053_ = crate::leanh::lean_ctor_get(v___x_2044_, 0);
                        v_isSharedCheck_2061_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2044_)) as u8;
                        if v_isSharedCheck_2061_ == 0 {
                            v___x_2055_ = v___x_2044_;
                            v_isShared_2056_ = v_isSharedCheck_2061_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2053_);
                            crate::leanh::lean_dec(v___x_2044_);
                            v___x_2055_ = crate::leanh::lean_box(0);
                            v_isShared_2056_ = v_isSharedCheck_2061_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2048_ == 0 {
                    v___x_2050_ = v___x_2047_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2051_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
                    v___x_2050_ = v_reuseFailAlloc_2051_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2050_;
            }
            3 => {
                v___x_2057_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2057_, 0, v_a_2053_);
                if v_isShared_2056_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2055_, 0, v___x_2057_);
                    v___x_2059_ = v___x_2055_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2060_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2057_);
                    v___x_2059_ = v_reuseFailAlloc_2060_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2059_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0(
    mut v_j_2062_: *mut crate::leanh::LeanObject,
    mut v_k_2063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2064_ = l_Lean_Json_getObjValD(v_j_2062_, v_k_2063_);
    v___x_2065_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0_spec__0(v___x_2064_);
    return v___x_2065_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0___boxed(
    mut v_j_2066_: *mut crate::leanh::LeanObject,
    mut v_k_2067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2068_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0(
            v_j_2066_, v_k_2067_,
        );
    crate::leanh::lean_dec_ref(v_k_2067_);
    return v_res_2068_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3(
    mut v_sz_2069_: usize,
    mut v_i_2070_: usize,
    mut v_bs_2071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2072_: u8 = 0;
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2079_: u8 = 0;
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2083_: u8 = 0;
    let mut v_a_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: usize = 0;
    let mut v___x_2088_: usize = 0;
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2072_ = lean_usize_dec_lt(v_i_2070_, v_sz_2069_);
                if v___x_2072_ == 0 {
                    v___x_2073_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2073_, 0, v_bs_2071_);
                    return v___x_2073_;
                } else {
                    v_v_2074_ = lean_array_uget_borrowed(v_bs_2071_, v_i_2070_);
                    crate::leanh::lean_inc(v_v_2074_);
                    v___x_2075_ = l_Lean_Json_getStr_x3f(v_v_2074_);
                    if crate::leanh::lean_obj_tag(v___x_2075_) == 0 {
                        crate::leanh::lean_dec_ref(v_bs_2071_);
                        v_a_2076_ = crate::leanh::lean_ctor_get(v___x_2075_, 0);
                        v_isSharedCheck_2083_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2075_)) as u8;
                        if v_isSharedCheck_2083_ == 0 {
                            v___x_2078_ = v___x_2075_;
                            v_isShared_2079_ = v_isSharedCheck_2083_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2076_);
                            crate::leanh::lean_dec(v___x_2075_);
                            v___x_2078_ = crate::leanh::lean_box(0);
                            v_isShared_2079_ = v_isSharedCheck_2083_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2084_ = crate::leanh::lean_ctor_get(v___x_2075_, 0);
                        crate::leanh::lean_inc(v_a_2084_);
                        crate::leanh::lean_dec_ref_known(v___x_2075_, 1);
                        v___x_2085_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_2086_ = lean_array_uset(v_bs_2071_, v_i_2070_, v___x_2085_);
                        v___x_2087_ = 1usize;
                        v___x_2088_ = lean_usize_add(v_i_2070_, v___x_2087_);
                        v___x_2089_ = lean_array_uset(v_bs_x27_2086_, v_i_2070_, v_a_2084_);
                        v_i_2070_ = v___x_2088_;
                        v_bs_2071_ = v___x_2089_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2079_ == 0 {
                    v___x_2081_ = v___x_2078_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2082_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
                    v___x_2081_ = v_reuseFailAlloc_2082_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2081_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3___boxed(
    mut v_sz_2091_: *mut crate::leanh::LeanObject,
    mut v_i_2092_: *mut crate::leanh::LeanObject,
    mut v_bs_2093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2094_: usize = 0;
    let mut v_i_boxed_2095_: usize = 0;
    let mut v_res_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2094_ = crate::leanh::lean_unbox_usize(v_sz_2091_);
    crate::leanh::lean_dec(v_sz_2091_);
    v_i_boxed_2095_ = crate::leanh::lean_unbox_usize(v_i_2092_);
    crate::leanh::lean_dec(v_i_2092_);
    v_res_2096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3(v_sz_boxed_2094_, v_i_boxed_2095_, v_bs_2093_);
    return v_res_2096_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10___redArg(
    mut v_x_2097_: *mut crate::leanh::LeanObject,
    mut v_x_2098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2104_: u8 = 0;
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: u64 = 0;
    let mut v___x_2107_: u64 = 0;
    let mut v___x_2108_: u64 = 0;
    let mut v_fold_2109_: u64 = 0;
    let mut v___x_2110_: u64 = 0;
    let mut v___x_2111_: u64 = 0;
    let mut v___x_2112_: u64 = 0;
    let mut v___x_2113_: usize = 0;
    let mut v___x_2114_: usize = 0;
    let mut v___x_2115_: usize = 0;
    let mut v___x_2116_: usize = 0;
    let mut v___x_2117_: usize = 0;
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2124_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2098_) == 0 {
                    return v_x_2097_;
                } else {
                    v_key_2099_ = crate::leanh::lean_ctor_get(v_x_2098_, 0);
                    v_value_2100_ = crate::leanh::lean_ctor_get(v_x_2098_, 1);
                    v_tail_2101_ = crate::leanh::lean_ctor_get(v_x_2098_, 2);
                    v_isSharedCheck_2124_ = (!crate::leanh::lean_is_exclusive(v_x_2098_)) as u8;
                    if v_isSharedCheck_2124_ == 0 {
                        v___x_2103_ = v_x_2098_;
                        v_isShared_2104_ = v_isSharedCheck_2124_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2101_);
                        crate::leanh::lean_inc(v_value_2100_);
                        crate::leanh::lean_inc(v_key_2099_);
                        crate::leanh::lean_dec(v_x_2098_);
                        v___x_2103_ = crate::leanh::lean_box(0);
                        v_isShared_2104_ = v_isSharedCheck_2124_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2105_ = lean_array_get_size(v_x_2097_);
                v___x_2106_ = lean_string_hash(v_key_2099_);
                v___x_2107_ = 32u64;
                v___x_2108_ = lean_uint64_shift_right(v___x_2106_, v___x_2107_);
                v_fold_2109_ = lean_uint64_xor(v___x_2106_, v___x_2108_);
                v___x_2110_ = 16u64;
                v___x_2111_ = lean_uint64_shift_right(v_fold_2109_, v___x_2110_);
                v___x_2112_ = lean_uint64_xor(v_fold_2109_, v___x_2111_);
                v___x_2113_ = lean_uint64_to_usize(v___x_2112_);
                v___x_2114_ = lean_usize_of_nat(v___x_2105_);
                v___x_2115_ = 1usize;
                v___x_2116_ = lean_usize_sub(v___x_2114_, v___x_2115_);
                v___x_2117_ = lean_usize_land(v___x_2113_, v___x_2116_);
                v___x_2118_ = lean_array_uget_borrowed(v_x_2097_, v___x_2117_);
                crate::leanh::lean_inc(v___x_2118_);
                if v_isShared_2104_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2103_, 2, v___x_2118_);
                    v___x_2120_ = v___x_2103_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2123_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_key_2099_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_value_2100_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2123_, 2, v___x_2118_);
                    v___x_2120_ = v_reuseFailAlloc_2123_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2121_ = lean_array_uset(v_x_2097_, v___x_2117_, v___x_2120_);
                v_x_2097_ = v___x_2121_;
                v_x_2098_ = v_tail_2101_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8___redArg(
    mut v_i_2125_: *mut crate::leanh::LeanObject,
    mut v_source_2126_: *mut crate::leanh::LeanObject,
    mut v_target_2127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: u8 = 0;
    let mut v_es_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2128_ = lean_array_get_size(v_source_2126_);
                v___x_2129_ = lean_nat_dec_lt(v_i_2125_, v___x_2128_);
                if v___x_2129_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_2126_);
                    crate::leanh::lean_dec(v_i_2125_);
                    return v_target_2127_;
                } else {
                    v_es_2130_ = lean_array_fget(v_source_2126_, v_i_2125_);
                    v___x_2131_ = crate::leanh::lean_box(0);
                    v_source_2132_ = lean_array_fset(v_source_2126_, v_i_2125_, v___x_2131_);
                    v_target_2133_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10___redArg(v_target_2127_, v_es_2130_);
                    v___x_2134_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2135_ = lean_nat_add(v_i_2125_, v___x_2134_);
                    crate::leanh::lean_dec(v_i_2125_);
                    v_i_2125_ = v___x_2135_;
                    v_source_2126_ = v_source_2132_;
                    v_target_2127_ = v_target_2133_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7___redArg(
    mut v_data_2137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2138_ = lean_array_get_size(v_data_2137_);
    v___x_2139_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2140_ = lean_nat_mul(v___x_2138_, v___x_2139_);
    v___x_2141_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2142_ = crate::leanh::lean_box(0);
    v___x_2143_ = lean_mk_array(v_nbuckets_2140_, v___x_2142_);
    v___x_2144_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8___redArg(v___x_2141_, v_data_2137_, v___x_2143_);
    return v___x_2144_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(
    mut v_a_2145_: *mut crate::leanh::LeanObject,
    mut v_x_2146_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2147_: u8 = 0;
    let mut v_key_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2146_) == 0 {
                    v___x_2147_ = 0;
                    return v___x_2147_;
                } else {
                    v_key_2148_ = crate::leanh::lean_ctor_get(v_x_2146_, 0);
                    v_tail_2149_ = crate::leanh::lean_ctor_get(v_x_2146_, 2);
                    v___x_2150_ = lean_string_dec_eq(v_key_2148_, v_a_2145_);
                    if v___x_2150_ == 0 {
                        v_x_2146_ = v_tail_2149_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2150_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg___boxed(
    mut v_a_2152_: *mut crate::leanh::LeanObject,
    mut v_x_2153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2154_: u8 = 0;
    let mut v_r_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2154_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_a_2152_, v_x_2153_);
    crate::leanh::lean_dec(v_x_2153_);
    crate::leanh::lean_dec_ref(v_a_2152_);
    v_r_2155_ = crate::leanh::lean_box((v_res_2154_) as usize);
    return v_r_2155_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(
    mut v_m_2156_: *mut crate::leanh::LeanObject,
    mut v_a_2157_: *mut crate::leanh::LeanObject,
    mut v_b_2158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: u64 = 0;
    let mut v___x_2163_: u64 = 0;
    let mut v___x_2164_: u64 = 0;
    let mut v_fold_2165_: u64 = 0;
    let mut v___x_2166_: u64 = 0;
    let mut v___x_2167_: u64 = 0;
    let mut v___x_2168_: u64 = 0;
    let mut v___x_2169_: usize = 0;
    let mut v___x_2170_: usize = 0;
    let mut v___x_2171_: usize = 0;
    let mut v___x_2172_: usize = 0;
    let mut v___x_2173_: usize = 0;
    let mut v_bkt_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: u8 = 0;
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2178_: u8 = 0;
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: u8 = 0;
    let mut v_val_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2196_: u8 = 0;
    let mut v_unused_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2159_ = crate::leanh::lean_ctor_get(v_m_2156_, 0);
                v_buckets_2160_ = crate::leanh::lean_ctor_get(v_m_2156_, 1);
                v___x_2161_ = lean_array_get_size(v_buckets_2160_);
                v___x_2162_ = lean_string_hash(v_a_2157_);
                v___x_2163_ = 32u64;
                v___x_2164_ = lean_uint64_shift_right(v___x_2162_, v___x_2163_);
                v_fold_2165_ = lean_uint64_xor(v___x_2162_, v___x_2164_);
                v___x_2166_ = 16u64;
                v___x_2167_ = lean_uint64_shift_right(v_fold_2165_, v___x_2166_);
                v___x_2168_ = lean_uint64_xor(v_fold_2165_, v___x_2167_);
                v___x_2169_ = lean_uint64_to_usize(v___x_2168_);
                v___x_2170_ = lean_usize_of_nat(v___x_2161_);
                v___x_2171_ = 1usize;
                v___x_2172_ = lean_usize_sub(v___x_2170_, v___x_2171_);
                v___x_2173_ = lean_usize_land(v___x_2169_, v___x_2172_);
                v_bkt_2174_ = lean_array_uget_borrowed(v_buckets_2160_, v___x_2173_);
                v___x_2175_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_a_2157_, v_bkt_2174_);
                if v___x_2175_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_2160_);
                    crate::leanh::lean_inc(v_size_2159_);
                    v_isSharedCheck_2196_ = (!crate::leanh::lean_is_exclusive(v_m_2156_)) as u8;
                    if v_isSharedCheck_2196_ == 0 {
                        v_unused_2197_ = crate::leanh::lean_ctor_get(v_m_2156_, 1);
                        crate::leanh::lean_dec(v_unused_2197_);
                        v_unused_2198_ = crate::leanh::lean_ctor_get(v_m_2156_, 0);
                        crate::leanh::lean_dec(v_unused_2198_);
                        v___x_2177_ = v_m_2156_;
                        v_isShared_2178_ = v_isSharedCheck_2196_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_2156_);
                        v___x_2177_ = crate::leanh::lean_box(0);
                        v_isShared_2178_ = v_isSharedCheck_2196_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_2158_);
                    crate::leanh::lean_dec_ref(v_a_2157_);
                    return v_m_2156_;
                }
            }
            1 => {
                v___x_2179_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_2180_ = lean_nat_add(v_size_2159_, v___x_2179_);
                crate::leanh::lean_dec(v_size_2159_);
                crate::leanh::lean_inc(v_bkt_2174_);
                v___x_2181_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2181_, 0, v_a_2157_);
                crate::leanh::lean_ctor_set(v___x_2181_, 1, v_b_2158_);
                crate::leanh::lean_ctor_set(v___x_2181_, 2, v_bkt_2174_);
                v_buckets_x27_2182_ = lean_array_uset(v_buckets_2160_, v___x_2173_, v___x_2181_);
                v___x_2183_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2184_ = lean_nat_mul(v_size_x27_2180_, v___x_2183_);
                v___x_2185_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2186_ = lean_nat_div(v___x_2184_, v___x_2185_);
                crate::leanh::lean_dec(v___x_2184_);
                v___x_2187_ = lean_array_get_size(v_buckets_x27_2182_);
                v___x_2188_ = lean_nat_dec_le(v___x_2186_, v___x_2187_);
                crate::leanh::lean_dec(v___x_2186_);
                if v___x_2188_ == 0 {
                    v_val_2189_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7___redArg(v_buckets_x27_2182_);
                    if v_isShared_2178_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2177_, 1, v_val_2189_);
                        crate::leanh::lean_ctor_set(v___x_2177_, 0, v_size_x27_2180_);
                        v___x_2191_ = v___x_2177_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2192_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_size_x27_2180_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_val_2189_);
                        v___x_2191_ = v_reuseFailAlloc_2192_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_2178_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2177_, 1, v_buckets_x27_2182_);
                        crate::leanh::lean_ctor_set(v___x_2177_, 0, v_size_x27_2180_);
                        v___x_2194_ = v___x_2177_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2195_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_size_x27_2180_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_buckets_x27_2182_);
                        v___x_2194_ = v_reuseFailAlloc_2195_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2191_;
            }
            3 => {
                return v___x_2194_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6(
    mut v_as_2199_: *mut crate::leanh::LeanObject,
    mut v_sz_2200_: usize,
    mut v_i_2201_: usize,
    mut v_b_2202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2203_: u8 = 0;
    let mut v_a_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: usize = 0;
    let mut v___x_2208_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2203_ = lean_usize_dec_lt(v_i_2201_, v_sz_2200_);
                if v___x_2203_ == 0 {
                    return v_b_2202_;
                } else {
                    v_a_2204_ = lean_array_uget_borrowed(v_as_2199_, v_i_2201_);
                    v___x_2205_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_a_2204_);
                    v_r_2206_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(v_b_2202_, v_a_2204_, v___x_2205_);
                    v___x_2207_ = 1usize;
                    v___x_2208_ = lean_usize_add(v_i_2201_, v___x_2207_);
                    v_i_2201_ = v___x_2208_;
                    v_b_2202_ = v_r_2206_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_as_2210_: *mut crate::leanh::LeanObject,
    mut v_sz_2211_: *mut crate::leanh::LeanObject,
    mut v_i_2212_: *mut crate::leanh::LeanObject,
    mut v_b_2213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2214_: usize = 0;
    let mut v_i_boxed_2215_: usize = 0;
    let mut v_res_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2214_ = crate::leanh::lean_unbox_usize(v_sz_2211_);
    crate::leanh::lean_dec(v_sz_2211_);
    v_i_boxed_2215_ = crate::leanh::lean_unbox_usize(v_i_2212_);
    crate::leanh::lean_dec(v_i_2212_);
    v_res_2216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6(v_as_2210_, v_sz_boxed_2214_, v_i_boxed_2215_, v_b_2213_);
    crate::leanh::lean_dec_ref(v_as_2210_);
    return v_res_2216_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4(
    mut v_m_2217_: *mut crate::leanh::LeanObject,
    mut v_l_2218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_2219_: usize = 0;
    let mut v___x_2220_: usize = 0;
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_2219_ = lean_array_size(v_l_2218_);
    v___x_2220_ = 0usize;
    v___x_2221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6(v_l_2218_, v_sz_2219_, v___x_2220_, v_m_2217_);
    return v___x_2221_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4___boxed(
    mut v_m_2222_: *mut crate::leanh::LeanObject,
    mut v_l_2223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2224_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4(v_m_2222_, v_l_2223_);
    crate::leanh::lean_dec_ref(v_l_2223_);
    return v_res_2224_;
}
pub unsafe fn _init_l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2227_ = crate::leanh::lean_box(0);
    v___x_2228_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2229_ = lean_mk_array(v___x_2228_, v___x_2227_);
    return v___x_2229_;
}
pub unsafe fn _init_l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2230_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1_once), _init_l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1);
    v___x_2231_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2232_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2232_, 0, v___x_2231_);
    crate::leanh::lean_ctor_set(v___x_2232_, 1, v___x_2230_);
    return v___x_2232_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2(
    mut v_x_2235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elems_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2238_: usize = 0;
    let mut v___x_2239_: usize = 0;
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2244_: u8 = 0;
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2248_: u8 = 0;
    let mut v_a_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2252_: u8 = 0;
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2259_: u8 = 0;
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2235_) == 0 {
                    v___x_2236_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__0;
                    return v___x_2236_;
                } else {
                    if crate::leanh::lean_obj_tag(v_x_2235_) == 4 {
                        v_elems_2237_ = crate::leanh::lean_ctor_get(v_x_2235_, 0);
                        crate::leanh::lean_inc_ref(v_elems_2237_);
                        crate::leanh::lean_dec_ref_known(v_x_2235_, 1);
                        v_sz_2238_ = lean_array_size(v_elems_2237_);
                        v___x_2239_ = 0usize;
                        v___x_2240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3(v_sz_2238_, v___x_2239_, v_elems_2237_);
                        if crate::leanh::lean_obj_tag(v___x_2240_) == 0 {
                            v_a_2241_ = crate::leanh::lean_ctor_get(v___x_2240_, 0);
                            v_isSharedCheck_2248_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2240_)) as u8;
                            if v_isSharedCheck_2248_ == 0 {
                                v___x_2243_ = v___x_2240_;
                                v_isShared_2244_ = v_isSharedCheck_2248_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2241_);
                                crate::leanh::lean_dec(v___x_2240_);
                                v___x_2243_ = crate::leanh::lean_box(0);
                                v_isShared_2244_ = v_isSharedCheck_2248_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_2249_ = crate::leanh::lean_ctor_get(v___x_2240_, 0);
                            v_isSharedCheck_2259_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2240_)) as u8;
                            if v_isSharedCheck_2259_ == 0 {
                                v___x_2251_ = v___x_2240_;
                                v_isShared_2252_ = v_isSharedCheck_2259_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2249_);
                                crate::leanh::lean_dec(v___x_2240_);
                                v___x_2251_ = crate::leanh::lean_box(0);
                                v_isShared_2252_ = v_isSharedCheck_2259_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_x_2235_);
                        v___x_2260_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__3;
                        return v___x_2260_;
                    }
                }
            }
            1 => {
                if v_isShared_2244_ == 0 {
                    v___x_2246_ = v___x_2243_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2247_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
                    v___x_2246_ = v_reuseFailAlloc_2247_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2246_;
            }
            3 => {
                v___x_2253_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2_once), _init_l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2);
                v___x_2254_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4(v___x_2253_, v_a_2249_);
                crate::leanh::lean_dec(v_a_2249_);
                v___x_2255_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2255_, 0, v___x_2254_);
                if v_isShared_2252_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2251_, 0, v___x_2255_);
                    v___x_2257_ = v___x_2251_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2258_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2255_);
                    v___x_2257_ = v_reuseFailAlloc_2258_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2257_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(
    mut v_j_2261_: *mut crate::leanh::LeanObject,
    mut v_k_2262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2263_ = l_Lean_Json_getObjValD(v_j_2261_, v_k_2262_);
    v___x_2264_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2(v___x_2263_);
    return v___x_2264_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1___boxed(
    mut v_j_2265_: *mut crate::leanh::LeanObject,
    mut v_k_2266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2267_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(
            v_j_2265_, v_k_2266_,
        );
    crate::leanh::lean_dec_ref(v_k_2266_);
    return v_res_2267_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2274_: u8 = 0;
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2274_ = 1;
    v___x_2275_ = l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2;
    v___x_2276_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2275_, v___x_2274_);
    return v___x_2276_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2277_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5;
    v___x_2278_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3,
    );
    v___x_2279_ = lean_string_append(v___x_2278_, v___x_2277_);
    return v___x_2279_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2283_: u8 = 0;
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2283_ = 1;
    v___x_2284_ = l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__6;
    v___x_2285_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2284_, v___x_2283_);
    return v___x_2285_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2286_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7_once),
        _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7,
    );
    v___x_2287_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4,
    );
    v___x_2288_ = lean_string_append(v___x_2287_, v___x_2286_);
    return v___x_2288_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2289_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10;
    v___x_2290_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8_once),
        _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8,
    );
    v___x_2291_ = lean_string_append(v___x_2290_, v___x_2289_);
    return v___x_2291_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2296_: u8 = 0;
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2296_ = 1;
    v___x_2297_ = l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__12;
    v___x_2298_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2297_, v___x_2296_);
    return v___x_2298_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2299_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13_once),
        _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13,
    );
    v___x_2300_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4,
    );
    v___x_2301_ = lean_string_append(v___x_2300_, v___x_2299_);
    return v___x_2301_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2302_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10;
    v___x_2303_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14_once),
        _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14,
    );
    v___x_2304_ = lean_string_append(v___x_2303_, v___x_2302_);
    return v___x_2304_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2309_: u8 = 0;
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2309_ = 1;
    v___x_2310_ = l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__18;
    v___x_2311_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2310_, v___x_2309_);
    return v___x_2311_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2312_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19_once),
        _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19,
    );
    v___x_2313_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4,
    );
    v___x_2314_ = lean_string_append(v___x_2313_, v___x_2312_);
    return v___x_2314_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2315_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10;
    v___x_2316_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20_once),
        _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20,
    );
    v___x_2317_ = lean_string_append(v___x_2316_, v___x_2315_);
    return v___x_2317_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonLogConfig_fromJson(
    mut v_json_2318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2324_: u8 = 0;
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2330_: u8 = 0;
    let mut v_a_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2334_: u8 = 0;
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2338_: u8 = 0;
    let mut v_a_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2345_: u8 = 0;
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2351_: u8 = 0;
    let mut v_a_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2355_: u8 = 0;
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2359_: u8 = 0;
    let mut v_a_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2366_: u8 = 0;
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2372_: u8 = 0;
    let mut v_a_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2376_: u8 = 0;
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2380_: u8 = 0;
    let mut v_a_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2384_: u8 = 0;
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2319_ = l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__0;
                crate::leanh::lean_inc(v_json_2318_);
                v___x_2320_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0(v_json_2318_, v___x_2319_);
                if crate::leanh::lean_obj_tag(v___x_2320_) == 0 {
                    crate::leanh::lean_dec(v_json_2318_);
                    v_a_2321_ = crate::leanh::lean_ctor_get(v___x_2320_, 0);
                    v_isSharedCheck_2330_ = (!crate::leanh::lean_is_exclusive(v___x_2320_)) as u8;
                    if v_isSharedCheck_2330_ == 0 {
                        v___x_2323_ = v___x_2320_;
                        v_isShared_2324_ = v_isSharedCheck_2330_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2321_);
                        crate::leanh::lean_dec(v___x_2320_);
                        v___x_2323_ = crate::leanh::lean_box(0);
                        v_isShared_2324_ = v_isSharedCheck_2330_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_2320_) == 0 {
                        crate::leanh::lean_dec(v_json_2318_);
                        v_a_2331_ = crate::leanh::lean_ctor_get(v___x_2320_, 0);
                        v_isSharedCheck_2338_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2320_)) as u8;
                        if v_isSharedCheck_2338_ == 0 {
                            v___x_2333_ = v___x_2320_;
                            v_isShared_2334_ = v_isSharedCheck_2338_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2331_);
                            crate::leanh::lean_dec(v___x_2320_);
                            v___x_2333_ = crate::leanh::lean_box(0);
                            v_isShared_2334_ = v_isSharedCheck_2338_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2339_ = crate::leanh::lean_ctor_get(v___x_2320_, 0);
                        crate::leanh::lean_inc(v_a_2339_);
                        crate::leanh::lean_dec_ref_known(v___x_2320_, 1);
                        v___x_2340_ = l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__10;
                        crate::leanh::lean_inc(v_json_2318_);
                        v___x_2341_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(v_json_2318_, v___x_2340_);
                        if crate::leanh::lean_obj_tag(v___x_2341_) == 0 {
                            crate::leanh::lean_dec(v_a_2339_);
                            crate::leanh::lean_dec(v_json_2318_);
                            v_a_2342_ = crate::leanh::lean_ctor_get(v___x_2341_, 0);
                            v_isSharedCheck_2351_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2341_)) as u8;
                            if v_isSharedCheck_2351_ == 0 {
                                v___x_2344_ = v___x_2341_;
                                v_isShared_2345_ = v_isSharedCheck_2351_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2342_);
                                crate::leanh::lean_dec(v___x_2341_);
                                v___x_2344_ = crate::leanh::lean_box(0);
                                v_isShared_2345_ = v_isSharedCheck_2351_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_2341_) == 0 {
                                crate::leanh::lean_dec(v_a_2339_);
                                crate::leanh::lean_dec(v_json_2318_);
                                v_a_2352_ = crate::leanh::lean_ctor_get(v___x_2341_, 0);
                                v_isSharedCheck_2359_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2341_)) as u8;
                                if v_isSharedCheck_2359_ == 0 {
                                    v___x_2354_ = v___x_2341_;
                                    v_isShared_2355_ = v_isSharedCheck_2359_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2352_);
                                    crate::leanh::lean_dec(v___x_2341_);
                                    v___x_2354_ = crate::leanh::lean_box(0);
                                    v_isShared_2355_ = v_isSharedCheck_2359_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_2360_ = crate::leanh::lean_ctor_get(v___x_2341_, 0);
                                crate::leanh::lean_inc(v_a_2360_);
                                crate::leanh::lean_dec_ref_known(v___x_2341_, 1);
                                v___x_2361_ =
                                    l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__16;
                                v___x_2362_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(v_json_2318_, v___x_2361_);
                                if crate::leanh::lean_obj_tag(v___x_2362_) == 0 {
                                    crate::leanh::lean_dec(v_a_2360_);
                                    crate::leanh::lean_dec(v_a_2339_);
                                    v_a_2363_ = crate::leanh::lean_ctor_get(v___x_2362_, 0);
                                    v_isSharedCheck_2372_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2362_)) as u8;
                                    if v_isSharedCheck_2372_ == 0 {
                                        v___x_2365_ = v___x_2362_;
                                        v_isShared_2366_ = v_isSharedCheck_2372_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2363_);
                                        crate::leanh::lean_dec(v___x_2362_);
                                        v___x_2365_ = crate::leanh::lean_box(0);
                                        v_isShared_2366_ = v_isSharedCheck_2372_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if crate::leanh::lean_obj_tag(v___x_2362_) == 0 {
                                        crate::leanh::lean_dec(v_a_2360_);
                                        crate::leanh::lean_dec(v_a_2339_);
                                        v_a_2373_ = crate::leanh::lean_ctor_get(v___x_2362_, 0);
                                        v_isSharedCheck_2380_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2362_)) as u8;
                                        if v_isSharedCheck_2380_ == 0 {
                                            v___x_2375_ = v___x_2362_;
                                            v_isShared_2376_ = v_isSharedCheck_2380_;
                                            state = 11;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2373_);
                                            crate::leanh::lean_dec(v___x_2362_);
                                            v___x_2375_ = crate::leanh::lean_box(0);
                                            v_isShared_2376_ = v_isSharedCheck_2380_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_2381_ = crate::leanh::lean_ctor_get(v___x_2362_, 0);
                                        v_isSharedCheck_2389_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2362_)) as u8;
                                        if v_isSharedCheck_2389_ == 0 {
                                            v___x_2383_ = v___x_2362_;
                                            v_isShared_2384_ = v_isSharedCheck_2389_;
                                            state = 13;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2381_);
                                            crate::leanh::lean_dec(v___x_2362_);
                                            v___x_2383_ = crate::leanh::lean_box(0);
                                            v_isShared_2384_ = v_isSharedCheck_2389_;
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
                v___x_2325_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9,
                );
                v___x_2326_ = lean_string_append(v___x_2325_, v_a_2321_);
                crate::leanh::lean_dec(v_a_2321_);
                if v_isShared_2324_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2323_, 0, v___x_2326_);
                    v___x_2328_ = v___x_2323_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2329_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2326_);
                    v___x_2328_ = v_reuseFailAlloc_2329_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2328_;
            }
            3 => {
                if v_isShared_2334_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2333_, 0);
                    v___x_2336_ = v___x_2333_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2337_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
                    v___x_2336_ = v_reuseFailAlloc_2337_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2336_;
            }
            5 => {
                v___x_2346_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15,
                );
                v___x_2347_ = lean_string_append(v___x_2346_, v_a_2342_);
                crate::leanh::lean_dec(v_a_2342_);
                if v_isShared_2345_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2344_, 0, v___x_2347_);
                    v___x_2349_ = v___x_2344_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2350_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
                    v___x_2349_ = v_reuseFailAlloc_2350_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2349_;
            }
            7 => {
                if v_isShared_2355_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2354_, 0);
                    v___x_2357_ = v___x_2354_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2358_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
                    v___x_2357_ = v_reuseFailAlloc_2358_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2357_;
            }
            9 => {
                v___x_2367_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21,
                );
                v___x_2368_ = lean_string_append(v___x_2367_, v_a_2363_);
                crate::leanh::lean_dec(v_a_2363_);
                if v_isShared_2366_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2365_, 0, v___x_2368_);
                    v___x_2370_ = v___x_2365_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2371_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2368_);
                    v___x_2370_ = v_reuseFailAlloc_2371_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2370_;
            }
            11 => {
                if v_isShared_2376_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2375_, 0);
                    v___x_2378_ = v___x_2375_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2379_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
                    v___x_2378_ = v_reuseFailAlloc_2379_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2378_;
            }
            13 => {
                v___x_2385_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2385_, 0, v_a_2339_);
                crate::leanh::lean_ctor_set(v___x_2385_, 1, v_a_2360_);
                crate::leanh::lean_ctor_set(v___x_2385_, 2, v_a_2381_);
                if v_isShared_2384_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2383_, 0, v___x_2385_);
                    v___x_2387_ = v___x_2383_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2388_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
                    v___x_2387_ = v_reuseFailAlloc_2388_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2387_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5(
    mut v_00_u03b2_2390_: *mut crate::leanh::LeanObject,
    mut v_m_2391_: *mut crate::leanh::LeanObject,
    mut v_a_2392_: *mut crate::leanh::LeanObject,
    mut v_b_2393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2394_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(v_m_2391_, v_a_2392_, v_b_2393_);
    return v___x_2394_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6(
    mut v_00_u03b2_2395_: *mut crate::leanh::LeanObject,
    mut v_a_2396_: *mut crate::leanh::LeanObject,
    mut v_x_2397_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2398_: u8 = 0;
    v___x_2398_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_a_2396_, v_x_2397_);
    return v___x_2398_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___boxed(
    mut v_00_u03b2_2399_: *mut crate::leanh::LeanObject,
    mut v_a_2400_: *mut crate::leanh::LeanObject,
    mut v_x_2401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2402_: u8 = 0;
    let mut v_r_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2402_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6(v_00_u03b2_2399_, v_a_2400_, v_x_2401_);
    crate::leanh::lean_dec(v_x_2401_);
    crate::leanh::lean_dec_ref(v_a_2400_);
    v_r_2403_ = crate::leanh::lean_box((v_res_2402_) as usize);
    return v_r_2403_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7(
    mut v_00_u03b2_2404_: *mut crate::leanh::LeanObject,
    mut v_data_2405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2406_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7___redArg(v_data_2405_);
    return v___x_2406_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8(
    mut v_00_u03b2_2407_: *mut crate::leanh::LeanObject,
    mut v_i_2408_: *mut crate::leanh::LeanObject,
    mut v_source_2409_: *mut crate::leanh::LeanObject,
    mut v_target_2410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2411_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8___redArg(v_i_2408_, v_source_2409_, v_target_2410_);
    return v___x_2411_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10(
    mut v_00_u03b2_2412_: *mut crate::leanh::LeanObject,
    mut v_x_2413_: *mut crate::leanh::LeanObject,
    mut v_x_2414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2415_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10___redArg(v_x_2413_, v_x_2414_);
    return v___x_2415_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__0(
    mut v_k_2418_: *mut crate::leanh::LeanObject,
    mut v_x_2419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2424_: u8 = 0;
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2431_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2419_) == 0 {
                    crate::leanh::lean_dec_ref(v_k_2418_);
                    v___x_2420_ = crate::leanh::lean_box(0);
                    return v___x_2420_;
                } else {
                    v_val_2421_ = crate::leanh::lean_ctor_get(v_x_2419_, 0);
                    v_isSharedCheck_2431_ = (!crate::leanh::lean_is_exclusive(v_x_2419_)) as u8;
                    if v_isSharedCheck_2431_ == 0 {
                        v___x_2423_ = v_x_2419_;
                        v_isShared_2424_ = v_isSharedCheck_2431_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2421_);
                        crate::leanh::lean_dec(v_x_2419_);
                        v___x_2423_ = crate::leanh::lean_box(0);
                        v_isShared_2424_ = v_isSharedCheck_2431_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2424_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2423_, 3);
                    v___x_2426_ = v___x_2423_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2430_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_val_2421_);
                    v___x_2426_ = v_reuseFailAlloc_2430_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2427_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2427_, 0, v_k_2418_);
                crate::leanh::lean_ctor_set(v___x_2427_, 1, v___x_2426_);
                v___x_2428_ = crate::leanh::lean_box(0);
                v___x_2429_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2429_, 0, v___x_2427_);
                crate::leanh::lean_ctor_set(v___x_2429_, 1, v___x_2428_);
                return v___x_2429_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1(
    mut v_sz_2432_: usize,
    mut v_i_2433_: usize,
    mut v_bs_2434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2435_: u8 = 0;
    let mut v_v_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: usize = 0;
    let mut v___x_2441_: usize = 0;
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2435_ = lean_usize_dec_lt(v_i_2433_, v_sz_2432_);
                if v___x_2435_ == 0 {
                    return v_bs_2434_;
                } else {
                    v_v_2436_ = lean_array_uget(v_bs_2434_, v_i_2433_);
                    v___x_2437_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2438_ = lean_array_uset(v_bs_2434_, v_i_2433_, v___x_2437_);
                    v___x_2439_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2439_, 0, v_v_2436_);
                    v___x_2440_ = 1usize;
                    v___x_2441_ = lean_usize_add(v_i_2433_, v___x_2440_);
                    v___x_2442_ = lean_array_uset(v_bs_x27_2438_, v_i_2433_, v___x_2439_);
                    v_i_2433_ = v___x_2441_;
                    v_bs_2434_ = v___x_2442_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1___boxed(
    mut v_sz_2444_: *mut crate::leanh::LeanObject,
    mut v_i_2445_: *mut crate::leanh::LeanObject,
    mut v_bs_2446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2447_: usize = 0;
    let mut v_i_boxed_2448_: usize = 0;
    let mut v_res_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2447_ = crate::leanh::lean_unbox_usize(v_sz_2444_);
    crate::leanh::lean_dec(v_sz_2444_);
    v_i_boxed_2448_ = crate::leanh::lean_unbox_usize(v_i_2445_);
    crate::leanh::lean_dec(v_i_2445_);
    v_res_2449_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1(v_sz_boxed_2447_, v_i_boxed_2448_, v_bs_2446_);
    return v_res_2449_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__2(
    mut v_x_2450_: *mut crate::leanh::LeanObject,
    mut v_x_2451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2451_) == 0 {
                    return v_x_2450_;
                } else {
                    v_key_2452_ = crate::leanh::lean_ctor_get(v_x_2451_, 0);
                    crate::leanh::lean_inc(v_key_2452_);
                    v_tail_2453_ = crate::leanh::lean_ctor_get(v_x_2451_, 2);
                    crate::leanh::lean_inc(v_tail_2453_);
                    crate::leanh::lean_dec_ref_known(v_x_2451_, 3);
                    v___x_2454_ = lean_array_push(v_x_2450_, v_key_2452_);
                    v_x_2450_ = v___x_2454_;
                    v_x_2451_ = v_tail_2453_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__3(
    mut v_as_2456_: *mut crate::leanh::LeanObject,
    mut v_i_2457_: usize,
    mut v_stop_2458_: usize,
    mut v_b_2459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2460_: u8 = 0;
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: usize = 0;
    let mut v___x_2464_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2460_ = lean_usize_dec_eq(v_i_2457_, v_stop_2458_);
                if v___x_2460_ == 0 {
                    v___x_2461_ = lean_array_uget_borrowed(v_as_2456_, v_i_2457_);
                    crate::leanh::lean_inc(v___x_2461_);
                    v___x_2462_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__2(v_b_2459_, v___x_2461_);
                    v___x_2463_ = 1usize;
                    v___x_2464_ = lean_usize_add(v_i_2457_, v___x_2463_);
                    v_i_2457_ = v___x_2464_;
                    v_b_2459_ = v___x_2462_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2459_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__3___boxed(
    mut v_as_2466_: *mut crate::leanh::LeanObject,
    mut v_i_2467_: *mut crate::leanh::LeanObject,
    mut v_stop_2468_: *mut crate::leanh::LeanObject,
    mut v_b_2469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2470_: usize = 0;
    let mut v_stop_boxed_2471_: usize = 0;
    let mut v_res_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2470_ = crate::leanh::lean_unbox_usize(v_i_2467_);
    crate::leanh::lean_dec(v_i_2467_);
    v_stop_boxed_2471_ = crate::leanh::lean_unbox_usize(v_stop_2468_);
    crate::leanh::lean_dec(v_stop_2468_);
    v_res_2472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__3(v_as_2466_, v_i_boxed_2470_, v_stop_boxed_2471_, v_b_2469_);
    crate::leanh::lean_dec_ref(v_as_2466_);
    return v_res_2472_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(
    mut v_k_2473_: *mut crate::leanh::LeanObject,
    mut v_x_2474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2477_: usize = 0;
    let mut v___x_2478_: usize = 0;
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: u8 = 0;
    let mut v___x_2492_: u8 = 0;
    let mut v___x_2493_: usize = 0;
    let mut v___x_2494_: usize = 0;
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: usize = 0;
    let mut v___x_2497_: usize = 0;
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2474_) == 0 {
                    crate::leanh::lean_dec_ref(v_k_2473_);
                    v___x_2484_ = crate::leanh::lean_box(0);
                    return v___x_2484_;
                } else {
                    v_val_2485_ = crate::leanh::lean_ctor_get(v_x_2474_, 0);
                    v_size_2486_ = crate::leanh::lean_ctor_get(v_val_2485_, 0);
                    v_buckets_2487_ = crate::leanh::lean_ctor_get(v_val_2485_, 1);
                    v___x_2488_ = lean_mk_empty_array_with_capacity(v_size_2486_);
                    v___x_2489_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2490_ = lean_array_get_size(v_buckets_2487_);
                    v___x_2491_ = lean_nat_dec_lt(v___x_2489_, v___x_2490_);
                    if v___x_2491_ == 0 {
                        v___y_2476_ = v___x_2488_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2492_ = lean_nat_dec_le(v___x_2490_, v___x_2490_);
                        if v___x_2492_ == 0 {
                            if v___x_2491_ == 0 {
                                v___y_2476_ = v___x_2488_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2493_ = 0usize;
                                v___x_2494_ = lean_usize_of_nat(v___x_2490_);
                                v___x_2495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__3(v_buckets_2487_, v___x_2493_, v___x_2494_, v___x_2488_);
                                v___y_2476_ = v___x_2495_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_2496_ = 0usize;
                            v___x_2497_ = lean_usize_of_nat(v___x_2490_);
                            v___x_2498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__3(v_buckets_2487_, v___x_2496_, v___x_2497_, v___x_2488_);
                            v___y_2476_ = v___x_2498_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_sz_2477_ = lean_array_size(v___y_2476_);
                v___x_2478_ = 0usize;
                v___x_2479_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1(v_sz_2477_, v___x_2478_, v___y_2476_);
                v___x_2480_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2480_, 0, v___x_2479_);
                v___x_2481_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2481_, 0, v_k_2473_);
                crate::leanh::lean_ctor_set(v___x_2481_, 1, v___x_2480_);
                v___x_2482_ = crate::leanh::lean_box(0);
                v___x_2483_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2483_, 0, v___x_2481_);
                crate::leanh::lean_ctor_set(v___x_2483_, 1, v___x_2482_);
                return v___x_2483_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1___boxed(
    mut v_k_2499_: *mut crate::leanh::LeanObject,
    mut v_x_2500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2501_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(v_k_2499_, v_x_2500_);
    crate::leanh::lean_dec(v_x_2500_);
    return v_res_2501_;
}
pub unsafe fn l_Lean_Lsp_instToJsonLogConfig_toJson(
    mut v_x_2502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_logDir_x3f_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowedMethods_x3f_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_disallowedMethods_x3f_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_logDir_x3f_2503_ = crate::leanh::lean_ctor_get(v_x_2502_, 0);
    crate::leanh::lean_inc(v_logDir_x3f_2503_);
    v_allowedMethods_x3f_2504_ = crate::leanh::lean_ctor_get(v_x_2502_, 1);
    crate::leanh::lean_inc(v_allowedMethods_x3f_2504_);
    v_disallowedMethods_x3f_2505_ = crate::leanh::lean_ctor_get(v_x_2502_, 2);
    crate::leanh::lean_inc(v_disallowedMethods_x3f_2505_);
    crate::leanh::lean_dec_ref(v_x_2502_);
    v___x_2506_ = l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__0;
    v___x_2507_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__0(
        v___x_2506_,
        v_logDir_x3f_2503_,
    );
    v___x_2508_ = l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__10;
    v___x_2509_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(
        v___x_2508_,
        v_allowedMethods_x3f_2504_,
    );
    crate::leanh::lean_dec(v_allowedMethods_x3f_2504_);
    v___x_2510_ = l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__16;
    v___x_2511_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(
        v___x_2510_,
        v_disallowedMethods_x3f_2505_,
    );
    crate::leanh::lean_dec(v_disallowedMethods_x3f_2505_);
    v___x_2512_ = crate::leanh::lean_box(0);
    v___x_2513_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2513_, 0, v___x_2511_);
    crate::leanh::lean_ctor_set(v___x_2513_, 1, v___x_2512_);
    v___x_2514_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2514_, 0, v___x_2509_);
    crate::leanh::lean_ctor_set(v___x_2514_, 1, v___x_2513_);
    v___x_2515_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2515_, 0, v___x_2507_);
    crate::leanh::lean_ctor_set(v___x_2515_, 1, v___x_2514_);
    v___x_2516_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2;
    v___x_2517_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_2515_, v___x_2516_);
    v___x_2518_ = l_Lean_Json_mkObj(v___x_2517_);
    crate::leanh::lean_dec(v___x_2517_);
    return v___x_2518_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0(
    mut v_k_2521_: *mut crate::leanh::LeanObject,
    mut v_x_2522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2522_) == 0 {
        let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_2521_);
        v___x_2523_ = crate::leanh::lean_box(0);
        return v___x_2523_;
    } else {
        let mut v_val_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2526_: u8 = 0;
        let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2524_ = crate::leanh::lean_ctor_get(v_x_2522_, 0);
        v___x_2525_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
        v___x_2526_ = (crate::leanh::lean_unbox(v_val_2524_) as u8);
        crate::leanh::lean_ctor_set_uint8(v___x_2525_, 0 as u32, v___x_2526_);
        v___x_2527_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2527_, 0, v_k_2521_);
        crate::leanh::lean_ctor_set(v___x_2527_, 1, v___x_2525_);
        v___x_2528_ = crate::leanh::lean_box(0);
        v___x_2529_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2529_, 0, v___x_2527_);
        crate::leanh::lean_ctor_set(v___x_2529_, 1, v___x_2528_);
        return v___x_2529_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0___boxed(
    mut v_k_2530_: *mut crate::leanh::LeanObject,
    mut v_x_2531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2532_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0(
        v_k_2530_, v_x_2531_,
    );
    crate::leanh::lean_dec(v_x_2531_);
    return v_res_2532_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__1(
    mut v_k_2533_: *mut crate::leanh::LeanObject,
    mut v_x_2534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2534_) == 0 {
        let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_2533_);
        v___x_2535_ = crate::leanh::lean_box(0);
        return v___x_2535_;
    } else {
        let mut v_val_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2536_ = crate::leanh::lean_ctor_get(v_x_2534_, 0);
        crate::leanh::lean_inc(v_val_2536_);
        crate::leanh::lean_dec_ref_known(v_x_2534_, 1);
        v___x_2537_ = l_Lean_Lsp_instToJsonLogConfig_toJson(v_val_2536_);
        v___x_2538_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2538_, 0, v_k_2533_);
        crate::leanh::lean_ctor_set(v___x_2538_, 1, v___x_2537_);
        v___x_2539_ = crate::leanh::lean_box(0);
        v___x_2540_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2540_, 0, v___x_2538_);
        crate::leanh::lean_ctor_set(v___x_2540_, 1, v___x_2539_);
        return v___x_2540_;
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonInitializationOptions_toJson(
    mut v_x_2543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasWidgets_x3f_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_logCfg_x3f_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2548_: u8 = 0;
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2561_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_hasWidgets_x3f_2544_ = crate::leanh::lean_ctor_get(v_x_2543_, 0);
                v_logCfg_x3f_2545_ = crate::leanh::lean_ctor_get(v_x_2543_, 1);
                v_isSharedCheck_2561_ = (!crate::leanh::lean_is_exclusive(v_x_2543_)) as u8;
                if v_isSharedCheck_2561_ == 0 {
                    v___x_2547_ = v_x_2543_;
                    v_isShared_2548_ = v_isSharedCheck_2561_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_logCfg_x3f_2545_);
                    crate::leanh::lean_inc(v_hasWidgets_x3f_2544_);
                    crate::leanh::lean_dec(v_x_2543_);
                    v___x_2547_ = crate::leanh::lean_box(0);
                    v_isShared_2548_ = v_isSharedCheck_2561_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2549_ = l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__0;
                v___x_2550_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0(v___x_2549_, v_hasWidgets_x3f_2544_);
                crate::leanh::lean_dec(v_hasWidgets_x3f_2544_);
                v___x_2551_ = l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__1;
                v___x_2552_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__1(v___x_2551_, v_logCfg_x3f_2545_);
                v___x_2553_ = crate::leanh::lean_box(0);
                if v_isShared_2548_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2547_, 1);
                    crate::leanh::lean_ctor_set(v___x_2547_, 1, v___x_2553_);
                    crate::leanh::lean_ctor_set(v___x_2547_, 0, v___x_2552_);
                    v___x_2555_ = v___x_2547_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2560_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2552_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2560_, 1, v___x_2553_);
                    v___x_2555_ = v_reuseFailAlloc_2560_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2556_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2556_, 0, v___x_2550_);
                crate::leanh::lean_ctor_set(v___x_2556_, 1, v___x_2555_);
                v___x_2557_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2;
                v___x_2558_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_2556_, v___x_2557_);
                v___x_2559_ = l_Lean_Json_mkObj(v___x_2558_);
                crate::leanh::lean_dec(v___x_2558_);
                return v___x_2559_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2(
    mut v_x_2566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2572_: u8 = 0;
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2576_: u8 = 0;
    let mut v_a_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2580_: u8 = 0;
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2585_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2566_) == 0 {
                    v___x_2567_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2___closed__0;
                    return v___x_2567_;
                } else {
                    v___x_2568_ = l_Lean_Lsp_instFromJsonLogConfig_fromJson(v_x_2566_);
                    if crate::leanh::lean_obj_tag(v___x_2568_) == 0 {
                        v_a_2569_ = crate::leanh::lean_ctor_get(v___x_2568_, 0);
                        v_isSharedCheck_2576_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2568_)) as u8;
                        if v_isSharedCheck_2576_ == 0 {
                            v___x_2571_ = v___x_2568_;
                            v_isShared_2572_ = v_isSharedCheck_2576_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2569_);
                            crate::leanh::lean_dec(v___x_2568_);
                            v___x_2571_ = crate::leanh::lean_box(0);
                            v_isShared_2572_ = v_isSharedCheck_2576_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2577_ = crate::leanh::lean_ctor_get(v___x_2568_, 0);
                        v_isSharedCheck_2585_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2568_)) as u8;
                        if v_isSharedCheck_2585_ == 0 {
                            v___x_2579_ = v___x_2568_;
                            v_isShared_2580_ = v_isSharedCheck_2585_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2577_);
                            crate::leanh::lean_dec(v___x_2568_);
                            v___x_2579_ = crate::leanh::lean_box(0);
                            v_isShared_2580_ = v_isSharedCheck_2585_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2572_ == 0 {
                    v___x_2574_ = v___x_2571_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2575_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
                    v___x_2574_ = v_reuseFailAlloc_2575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2574_;
            }
            3 => {
                v___x_2581_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2581_, 0, v_a_2577_);
                if v_isShared_2580_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2579_, 0, v___x_2581_);
                    v___x_2583_ = v___x_2579_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2584_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
                    v___x_2583_ = v_reuseFailAlloc_2584_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2583_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1(
    mut v_j_2586_: *mut crate::leanh::LeanObject,
    mut v_k_2587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2588_ = l_Lean_Json_getObjValD(v_j_2586_, v_k_2587_);
    v___x_2589_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2(v___x_2588_);
    return v___x_2589_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1___boxed(
    mut v_j_2590_: *mut crate::leanh::LeanObject,
    mut v_k_2591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2592_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1(v_j_2590_, v_k_2591_);
    crate::leanh::lean_dec_ref(v_k_2591_);
    return v_res_2592_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0(
    mut v_x_2595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2601_: u8 = 0;
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2605_: u8 = 0;
    let mut v_a_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2609_: u8 = 0;
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2614_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2595_) == 0 {
                    v___x_2596_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___closed__0;
                    return v___x_2596_;
                } else {
                    v___x_2597_ = l_Lean_Json_getBool_x3f(v_x_2595_);
                    if crate::leanh::lean_obj_tag(v___x_2597_) == 0 {
                        v_a_2598_ = crate::leanh::lean_ctor_get(v___x_2597_, 0);
                        v_isSharedCheck_2605_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2597_)) as u8;
                        if v_isSharedCheck_2605_ == 0 {
                            v___x_2600_ = v___x_2597_;
                            v_isShared_2601_ = v_isSharedCheck_2605_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2598_);
                            crate::leanh::lean_dec(v___x_2597_);
                            v___x_2600_ = crate::leanh::lean_box(0);
                            v_isShared_2601_ = v_isSharedCheck_2605_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2606_ = crate::leanh::lean_ctor_get(v___x_2597_, 0);
                        v_isSharedCheck_2614_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2597_)) as u8;
                        if v_isSharedCheck_2614_ == 0 {
                            v___x_2608_ = v___x_2597_;
                            v_isShared_2609_ = v_isSharedCheck_2614_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2606_);
                            crate::leanh::lean_dec(v___x_2597_);
                            v___x_2608_ = crate::leanh::lean_box(0);
                            v_isShared_2609_ = v_isSharedCheck_2614_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2601_ == 0 {
                    v___x_2603_ = v___x_2600_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2604_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
                    v___x_2603_ = v_reuseFailAlloc_2604_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2603_;
            }
            3 => {
                v___x_2610_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2610_, 0, v_a_2606_);
                if v_isShared_2609_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2608_, 0, v___x_2610_);
                    v___x_2612_ = v___x_2608_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2613_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2610_);
                    v___x_2612_ = v_reuseFailAlloc_2613_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2612_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___boxed(
    mut v_x_2615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2616_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0(v_x_2615_);
    crate::leanh::lean_dec(v_x_2615_);
    return v_res_2616_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0(
    mut v_j_2617_: *mut crate::leanh::LeanObject,
    mut v_k_2618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2619_ = l_Lean_Json_getObjValD(v_j_2617_, v_k_2618_);
    v___x_2620_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0(v___x_2619_);
    crate::leanh::lean_dec(v___x_2619_);
    return v___x_2620_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0___boxed(
    mut v_j_2621_: *mut crate::leanh::LeanObject,
    mut v_k_2622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2623_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0(v_j_2621_, v_k_2622_);
    crate::leanh::lean_dec_ref(v_k_2622_);
    return v_res_2623_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2629_: u8 = 0;
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2629_ = 1;
    v___x_2630_ = l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1;
    v___x_2631_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2630_, v___x_2629_);
    return v___x_2631_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2632_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5;
    v___x_2633_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2,
    );
    v___x_2634_ = lean_string_append(v___x_2633_, v___x_2632_);
    return v___x_2634_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2638_: u8 = 0;
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2638_ = 1;
    v___x_2639_ = l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__5;
    v___x_2640_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2639_, v___x_2638_);
    return v___x_2640_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2641_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6,
    );
    v___x_2642_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3,
    );
    v___x_2643_ = lean_string_append(v___x_2642_, v___x_2641_);
    return v___x_2643_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2644_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10;
    v___x_2645_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7,
    );
    v___x_2646_ = lean_string_append(v___x_2645_, v___x_2644_);
    return v___x_2646_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2650_: u8 = 0;
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2650_ = 1;
    v___x_2651_ = l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__10;
    v___x_2652_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2651_, v___x_2650_);
    return v___x_2652_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2653_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11_once
        ),
        _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11,
    );
    v___x_2654_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3,
    );
    v___x_2655_ = lean_string_append(v___x_2654_, v___x_2653_);
    return v___x_2655_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2656_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10;
    v___x_2657_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12_once
        ),
        _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12,
    );
    v___x_2658_ = lean_string_append(v___x_2657_, v___x_2656_);
    return v___x_2658_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonInitializationOptions_fromJson(
    mut v_json_2659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2665_: u8 = 0;
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2671_: u8 = 0;
    let mut v_a_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2675_: u8 = 0;
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2679_: u8 = 0;
    let mut v_a_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2686_: u8 = 0;
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2692_: u8 = 0;
    let mut v_a_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2696_: u8 = 0;
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2700_: u8 = 0;
    let mut v_a_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2704_: u8 = 0;
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2709_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2660_ = l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__0;
                crate::leanh::lean_inc(v_json_2659_);
                v___x_2661_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0(v_json_2659_, v___x_2660_);
                if crate::leanh::lean_obj_tag(v___x_2661_) == 0 {
                    crate::leanh::lean_dec(v_json_2659_);
                    v_a_2662_ = crate::leanh::lean_ctor_get(v___x_2661_, 0);
                    v_isSharedCheck_2671_ = (!crate::leanh::lean_is_exclusive(v___x_2661_)) as u8;
                    if v_isSharedCheck_2671_ == 0 {
                        v___x_2664_ = v___x_2661_;
                        v_isShared_2665_ = v_isSharedCheck_2671_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2662_);
                        crate::leanh::lean_dec(v___x_2661_);
                        v___x_2664_ = crate::leanh::lean_box(0);
                        v_isShared_2665_ = v_isSharedCheck_2671_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_2661_) == 0 {
                        crate::leanh::lean_dec(v_json_2659_);
                        v_a_2672_ = crate::leanh::lean_ctor_get(v___x_2661_, 0);
                        v_isSharedCheck_2679_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2661_)) as u8;
                        if v_isSharedCheck_2679_ == 0 {
                            v___x_2674_ = v___x_2661_;
                            v_isShared_2675_ = v_isSharedCheck_2679_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2672_);
                            crate::leanh::lean_dec(v___x_2661_);
                            v___x_2674_ = crate::leanh::lean_box(0);
                            v_isShared_2675_ = v_isSharedCheck_2679_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2680_ = crate::leanh::lean_ctor_get(v___x_2661_, 0);
                        crate::leanh::lean_inc(v_a_2680_);
                        crate::leanh::lean_dec_ref_known(v___x_2661_, 1);
                        v___x_2681_ = l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__1;
                        v___x_2682_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1(v_json_2659_, v___x_2681_);
                        if crate::leanh::lean_obj_tag(v___x_2682_) == 0 {
                            crate::leanh::lean_dec(v_a_2680_);
                            v_a_2683_ = crate::leanh::lean_ctor_get(v___x_2682_, 0);
                            v_isSharedCheck_2692_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2682_)) as u8;
                            if v_isSharedCheck_2692_ == 0 {
                                v___x_2685_ = v___x_2682_;
                                v_isShared_2686_ = v_isSharedCheck_2692_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2683_);
                                crate::leanh::lean_dec(v___x_2682_);
                                v___x_2685_ = crate::leanh::lean_box(0);
                                v_isShared_2686_ = v_isSharedCheck_2692_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_2682_) == 0 {
                                crate::leanh::lean_dec(v_a_2680_);
                                v_a_2693_ = crate::leanh::lean_ctor_get(v___x_2682_, 0);
                                v_isSharedCheck_2700_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2682_)) as u8;
                                if v_isSharedCheck_2700_ == 0 {
                                    v___x_2695_ = v___x_2682_;
                                    v_isShared_2696_ = v_isSharedCheck_2700_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2693_);
                                    crate::leanh::lean_dec(v___x_2682_);
                                    v___x_2695_ = crate::leanh::lean_box(0);
                                    v_isShared_2696_ = v_isSharedCheck_2700_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_2701_ = crate::leanh::lean_ctor_get(v___x_2682_, 0);
                                v_isSharedCheck_2709_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2682_)) as u8;
                                if v_isSharedCheck_2709_ == 0 {
                                    v___x_2703_ = v___x_2682_;
                                    v_isShared_2704_ = v_isSharedCheck_2709_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2701_);
                                    crate::leanh::lean_dec(v___x_2682_);
                                    v___x_2703_ = crate::leanh::lean_box(0);
                                    v_isShared_2704_ = v_isSharedCheck_2709_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2666_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8,
                );
                v___x_2667_ = lean_string_append(v___x_2666_, v_a_2662_);
                crate::leanh::lean_dec(v_a_2662_);
                if v_isShared_2665_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2664_, 0, v___x_2667_);
                    v___x_2669_ = v___x_2664_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2670_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2667_);
                    v___x_2669_ = v_reuseFailAlloc_2670_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2669_;
            }
            3 => {
                if v_isShared_2675_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2674_, 0);
                    v___x_2677_ = v___x_2674_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2678_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
                    v___x_2677_ = v_reuseFailAlloc_2678_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2677_;
            }
            5 => {
                v___x_2687_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13,
                );
                v___x_2688_ = lean_string_append(v___x_2687_, v_a_2683_);
                crate::leanh::lean_dec(v_a_2683_);
                if v_isShared_2686_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2685_, 0, v___x_2688_);
                    v___x_2690_ = v___x_2685_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2691_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2688_);
                    v___x_2690_ = v_reuseFailAlloc_2691_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2690_;
            }
            7 => {
                if v_isShared_2696_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2695_, 0);
                    v___x_2698_ = v___x_2695_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2699_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
                    v___x_2698_ = v_reuseFailAlloc_2699_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2698_;
            }
            9 => {
                v___x_2705_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2705_, 0, v_a_2680_);
                crate::leanh::lean_ctor_set(v___x_2705_, 1, v_a_2701_);
                if v_isShared_2704_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2703_, 0, v___x_2705_);
                    v___x_2707_ = v___x_2703_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2708_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2705_);
                    v___x_2707_ = v_reuseFailAlloc_2708_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2707_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__0(
    mut v_k_2712_: *mut crate::leanh::LeanObject,
    mut v_x_2713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2718_: u8 = 0;
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2726_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2713_) == 0 {
                    crate::leanh::lean_dec_ref(v_k_2712_);
                    v___x_2714_ = crate::leanh::lean_box(0);
                    return v___x_2714_;
                } else {
                    v_val_2715_ = crate::leanh::lean_ctor_get(v_x_2713_, 0);
                    v_isSharedCheck_2726_ = (!crate::leanh::lean_is_exclusive(v_x_2713_)) as u8;
                    if v_isSharedCheck_2726_ == 0 {
                        v___x_2717_ = v_x_2713_;
                        v_isShared_2718_ = v_isSharedCheck_2726_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2715_);
                        crate::leanh::lean_dec(v_x_2713_);
                        v___x_2717_ = crate::leanh::lean_box(0);
                        v_isShared_2718_ = v_isSharedCheck_2726_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2719_ = l_Lean_JsonNumber_fromInt(v_val_2715_);
                if v_isShared_2718_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2717_, 2);
                    crate::leanh::lean_ctor_set(v___x_2717_, 0, v___x_2719_);
                    v___x_2721_ = v___x_2717_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2725_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2719_);
                    v___x_2721_ = v_reuseFailAlloc_2725_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2722_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2722_, 0, v_k_2712_);
                crate::leanh::lean_ctor_set(v___x_2722_, 1, v___x_2721_);
                v___x_2723_ = crate::leanh::lean_box(0);
                v___x_2724_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2724_, 0, v___x_2722_);
                crate::leanh::lean_ctor_set(v___x_2724_, 1, v___x_2723_);
                return v___x_2724_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__1(
    mut v_k_2727_: *mut crate::leanh::LeanObject,
    mut v_x_2728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2728_) == 0 {
        let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_2727_);
        v___x_2729_ = crate::leanh::lean_box(0);
        return v___x_2729_;
    } else {
        let mut v_val_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2730_ = crate::leanh::lean_ctor_get(v_x_2728_, 0);
        crate::leanh::lean_inc(v_val_2730_);
        crate::leanh::lean_dec_ref_known(v_x_2728_, 1);
        v___x_2731_ = l_Lean_Lsp_instToJsonClientInfo_toJson(v_val_2730_);
        v___x_2732_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2732_, 0, v_k_2727_);
        crate::leanh::lean_ctor_set(v___x_2732_, 1, v___x_2731_);
        v___x_2733_ = crate::leanh::lean_box(0);
        v___x_2734_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2734_, 0, v___x_2732_);
        crate::leanh::lean_ctor_set(v___x_2734_, 1, v___x_2733_);
        return v___x_2734_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__2(
    mut v_k_2735_: *mut crate::leanh::LeanObject,
    mut v_x_2736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2736_) == 0 {
        let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_2735_);
        v___x_2737_ = crate::leanh::lean_box(0);
        return v___x_2737_;
    } else {
        let mut v_val_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2738_ = crate::leanh::lean_ctor_get(v_x_2736_, 0);
        crate::leanh::lean_inc(v_val_2738_);
        crate::leanh::lean_dec_ref_known(v_x_2736_, 1);
        v___x_2739_ = l_Lean_Lsp_instToJsonInitializationOptions_toJson(v_val_2738_);
        v___x_2740_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2740_, 0, v_k_2735_);
        crate::leanh::lean_ctor_set(v___x_2740_, 1, v___x_2739_);
        v___x_2741_ = crate::leanh::lean_box(0);
        v___x_2742_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2742_, 0, v___x_2740_);
        crate::leanh::lean_ctor_set(v___x_2742_, 1, v___x_2741_);
        return v___x_2742_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4(
    mut v_sz_2743_: usize,
    mut v_i_2744_: usize,
    mut v_bs_2745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2746_: u8 = 0;
    let mut v_v_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: usize = 0;
    let mut v___x_2752_: usize = 0;
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2746_ = lean_usize_dec_lt(v_i_2744_, v_sz_2743_);
                if v___x_2746_ == 0 {
                    return v_bs_2745_;
                } else {
                    v_v_2747_ = lean_array_uget(v_bs_2745_, v_i_2744_);
                    v___x_2748_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2749_ = lean_array_uset(v_bs_2745_, v_i_2744_, v___x_2748_);
                    v___x_2750_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson(v_v_2747_);
                    v___x_2751_ = 1usize;
                    v___x_2752_ = lean_usize_add(v_i_2744_, v___x_2751_);
                    v___x_2753_ = lean_array_uset(v_bs_x27_2749_, v_i_2744_, v___x_2750_);
                    v_i_2744_ = v___x_2752_;
                    v_bs_2745_ = v___x_2753_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4___boxed(
    mut v_sz_2755_: *mut crate::leanh::LeanObject,
    mut v_i_2756_: *mut crate::leanh::LeanObject,
    mut v_bs_2757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2758_: usize = 0;
    let mut v_i_boxed_2759_: usize = 0;
    let mut v_res_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2758_ = crate::leanh::lean_unbox_usize(v_sz_2755_);
    crate::leanh::lean_dec(v_sz_2755_);
    v_i_boxed_2759_ = crate::leanh::lean_unbox_usize(v_i_2756_);
    crate::leanh::lean_dec(v_i_2756_);
    v_res_2760_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4(v_sz_boxed_2758_, v_i_boxed_2759_, v_bs_2757_);
    return v_res_2760_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3(
    mut v_a_2761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_2762_: usize = 0;
    let mut v___x_2763_: usize = 0;
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_2762_ = lean_array_size(v_a_2761_);
    v___x_2763_ = 0usize;
    v___x_2764_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4(v_sz_2762_, v___x_2763_, v_a_2761_);
    v___x_2765_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2765_, 0, v___x_2764_);
    return v___x_2765_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3(
    mut v_k_2766_: *mut crate::leanh::LeanObject,
    mut v_x_2767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2767_) == 0 {
        let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_2766_);
        v___x_2768_ = crate::leanh::lean_box(0);
        return v___x_2768_;
    } else {
        let mut v_val_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2769_ = crate::leanh::lean_ctor_get(v_x_2767_, 0);
        crate::leanh::lean_inc(v_val_2769_);
        crate::leanh::lean_dec_ref_known(v_x_2767_, 1);
        v___x_2770_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3(v_val_2769_);
        v___x_2771_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2771_, 0, v_k_2766_);
        crate::leanh::lean_ctor_set(v___x_2771_, 1, v___x_2770_);
        v___x_2772_ = crate::leanh::lean_box(0);
        v___x_2773_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2773_, 0, v___x_2771_);
        crate::leanh::lean_ctor_set(v___x_2773_, 1, v___x_2772_);
        return v___x_2773_;
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonInitializeParams_toJson(
    mut v_x_2781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_processId_x3f_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_clientInfo_x3f_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rootUri_x3f_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initializationOptions_x3f_2785_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_capabilities_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trace_2787_: u8 = 0;
    let mut v_workspaceFolders_x3f_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_processId_x3f_2782_ = crate::leanh::lean_ctor_get(v_x_2781_, 0);
                crate::leanh::lean_inc(v_processId_x3f_2782_);
                v_clientInfo_x3f_2783_ = crate::leanh::lean_ctor_get(v_x_2781_, 1);
                crate::leanh::lean_inc(v_clientInfo_x3f_2783_);
                v_rootUri_x3f_2784_ = crate::leanh::lean_ctor_get(v_x_2781_, 2);
                crate::leanh::lean_inc(v_rootUri_x3f_2784_);
                v_initializationOptions_x3f_2785_ = crate::leanh::lean_ctor_get(v_x_2781_, 3);
                crate::leanh::lean_inc(v_initializationOptions_x3f_2785_);
                v_capabilities_2786_ = crate::leanh::lean_ctor_get(v_x_2781_, 4);
                crate::leanh::lean_inc_ref(v_capabilities_2786_);
                v_trace_2787_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_2781_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_workspaceFolders_x3f_2788_ = crate::leanh::lean_ctor_get(v_x_2781_, 5);
                crate::leanh::lean_inc(v_workspaceFolders_x3f_2788_);
                crate::leanh::lean_dec_ref(v_x_2781_);
                v___x_2789_ = l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__0;
                v___x_2790_ =
                    l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__0(
                        v___x_2789_,
                        v_processId_x3f_2782_,
                    );
                v___x_2791_ = l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__1;
                v___x_2792_ =
                    l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__1(
                        v___x_2791_,
                        v_clientInfo_x3f_2783_,
                    );
                v___x_2793_ = l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__2;
                v___x_2794_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__0(
                    v___x_2793_,
                    v_rootUri_x3f_2784_,
                );
                v___x_2795_ = l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__3;
                v___x_2796_ =
                    l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__2(
                        v___x_2795_,
                        v_initializationOptions_x3f_2785_,
                    );
                v___x_2797_ = l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4;
                v___x_2798_ = l_Lean_Lsp_instToJsonClientCapabilities_toJson(v_capabilities_2786_);
                v___x_2799_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2799_, 0, v___x_2797_);
                crate::leanh::lean_ctor_set(v___x_2799_, 1, v___x_2798_);
                v___x_2800_ = crate::leanh::lean_box(0);
                v___x_2801_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2801_, 0, v___x_2799_);
                crate::leanh::lean_ctor_set(v___x_2801_, 1, v___x_2800_);
                v___x_2802_ = l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__5;
                match v_trace_2787_ {
                    0 => {
                        v___x_2819_ = l_Lean_Lsp_Trace_hasToJson___lam__0___closed__0;
                        v___y_2804_ = v___x_2819_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_2820_ = l_Lean_Lsp_Trace_hasToJson___lam__0___closed__1;
                        v___y_2804_ = v___x_2820_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_2821_ = l_Lean_Lsp_Trace_hasToJson___lam__0___closed__2;
                        v___y_2804_ = v___x_2821_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_2804_);
                v___x_2805_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2805_, 0, v___x_2802_);
                crate::leanh::lean_ctor_set(v___x_2805_, 1, v___y_2804_);
                v___x_2806_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2806_, 0, v___x_2805_);
                crate::leanh::lean_ctor_set(v___x_2806_, 1, v___x_2800_);
                v___x_2807_ = l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__6;
                v___x_2808_ =
                    l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3(
                        v___x_2807_,
                        v_workspaceFolders_x3f_2788_,
                    );
                v___x_2809_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2809_, 0, v___x_2808_);
                crate::leanh::lean_ctor_set(v___x_2809_, 1, v___x_2800_);
                v___x_2810_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2810_, 0, v___x_2806_);
                crate::leanh::lean_ctor_set(v___x_2810_, 1, v___x_2809_);
                v___x_2811_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2811_, 0, v___x_2801_);
                crate::leanh::lean_ctor_set(v___x_2811_, 1, v___x_2810_);
                v___x_2812_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2812_, 0, v___x_2796_);
                crate::leanh::lean_ctor_set(v___x_2812_, 1, v___x_2811_);
                v___x_2813_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2813_, 0, v___x_2794_);
                crate::leanh::lean_ctor_set(v___x_2813_, 1, v___x_2812_);
                v___x_2814_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2814_, 0, v___x_2792_);
                crate::leanh::lean_ctor_set(v___x_2814_, 1, v___x_2813_);
                v___x_2815_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2815_, 0, v___x_2790_);
                crate::leanh::lean_ctor_set(v___x_2815_, 1, v___x_2814_);
                v___x_2816_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2;
                v___x_2817_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_2815_, v___x_2816_);
                v___x_2818_ = l_Lean_Json_mkObj(v___x_2817_);
                crate::leanh::lean_dec(v___x_2817_);
                return v___x_2818_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instFromJsonInitializeParams___lam__0(
    mut v___x_2824_: *mut crate::leanh::LeanObject,
    mut v___x_2825_: *mut crate::leanh::LeanObject,
    mut v___x_2826_: *mut crate::leanh::LeanObject,
    mut v___x_2827_: *mut crate::leanh::LeanObject,
    mut v___x_2828_: *mut crate::leanh::LeanObject,
    mut v___x_2829_: *mut crate::leanh::LeanObject,
    mut v___f_2830_: *mut crate::leanh::LeanObject,
    mut v_j_2831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_processId_x3f_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_clientInfo_x3f_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rootUri_x3f_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initializationOptions_x3f_2839_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2845_: u8 = 0;
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2849_: u8 = 0;
    let mut v_a_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2853_: u8 = 0;
    let mut v___y_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2859_: u8 = 0;
    let mut v___y_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2870_: u8 = 0;
    let mut v___y_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2876_: u8 = 0;
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2880_: u8 = 0;
    let mut v___y_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2885_: u8 = 0;
    let mut v___y_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2891_: u8 = 0;
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2895_: u8 = 0;
    let mut v___y_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2899_: u8 = 0;
    let mut v___y_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2905_: u8 = 0;
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2909_: u8 = 0;
    let mut v___y_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2912_: u8 = 0;
    let mut v___y_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2918_: u8 = 0;
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2922_: u8 = 0;
    let mut v___y_2924_: u8 = 0;
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2931_: u8 = 0;
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2935_: u8 = 0;
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: u8 = 0;
    let mut v_a_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: u8 = 0;
    let mut v_isSharedCheck_2941_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2832_ = l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__0;
                crate::leanh::lean_inc_n(v_j_2831_, 5);
                v_processId_x3f_2833_ =
                    l_Lean_Json_getObjValAs_x3f___redArg(v_j_2831_, v___x_2824_, v___x_2832_);
                v___x_2834_ = l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__1;
                v_clientInfo_x3f_2835_ =
                    l_Lean_Json_getObjValAs_x3f___redArg(v_j_2831_, v___x_2825_, v___x_2834_);
                v___x_2836_ = l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__2;
                v_rootUri_x3f_2837_ =
                    l_Lean_Json_getObjValAs_x3f___redArg(v_j_2831_, v___x_2826_, v___x_2836_);
                v___x_2838_ = l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__3;
                v_initializationOptions_x3f_2839_ =
                    l_Lean_Json_getObjValAs_x3f___redArg(v_j_2831_, v___x_2827_, v___x_2838_);
                v___x_2840_ = l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4;
                v___x_2841_ =
                    l_Lean_Json_getObjValAs_x3f___redArg(v_j_2831_, v___x_2828_, v___x_2840_);
                if crate::leanh::lean_obj_tag(v___x_2841_) == 0 {
                    crate::leanh::lean_dec_ref(v_initializationOptions_x3f_2839_);
                    crate::leanh::lean_dec_ref(v_rootUri_x3f_2837_);
                    crate::leanh::lean_dec_ref(v_clientInfo_x3f_2835_);
                    crate::leanh::lean_dec_ref(v_processId_x3f_2833_);
                    crate::leanh::lean_dec(v_j_2831_);
                    crate::leanh::lean_dec_ref(v___f_2830_);
                    crate::leanh::lean_dec_ref(v___x_2829_);
                    v_a_2842_ = crate::leanh::lean_ctor_get(v___x_2841_, 0);
                    v_isSharedCheck_2849_ = (!crate::leanh::lean_is_exclusive(v___x_2841_)) as u8;
                    if v_isSharedCheck_2849_ == 0 {
                        v___x_2844_ = v___x_2841_;
                        v_isShared_2845_ = v_isSharedCheck_2849_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2842_);
                        crate::leanh::lean_dec(v___x_2841_);
                        v___x_2844_ = crate::leanh::lean_box(0);
                        v_isShared_2845_ = v_isSharedCheck_2849_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2850_ = crate::leanh::lean_ctor_get(v___x_2841_, 0);
                    v_isSharedCheck_2941_ = (!crate::leanh::lean_is_exclusive(v___x_2841_)) as u8;
                    if v_isSharedCheck_2941_ == 0 {
                        v___x_2852_ = v___x_2841_;
                        v_isShared_2853_ = v_isSharedCheck_2941_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2850_);
                        crate::leanh::lean_dec(v___x_2841_);
                        v___x_2852_ = crate::leanh::lean_box(0);
                        v_isShared_2853_ = v_isSharedCheck_2941_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2845_ == 0 {
                    v___x_2847_ = v___x_2844_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2848_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
                    v___x_2847_ = v_reuseFailAlloc_2848_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2847_;
            }
            3 => {
                v___x_2936_ = l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__5;
                crate::leanh::lean_inc(v_j_2831_);
                v___x_2937_ =
                    l_Lean_Json_getObjValAs_x3f___redArg(v_j_2831_, v___f_2830_, v___x_2936_);
                if crate::leanh::lean_obj_tag(v___x_2937_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2937_, 1);
                    v___x_2938_ = 0;
                    v___y_2924_ = v___x_2938_;
                    state = 18;
                    continue;
                } else {
                    v_a_2939_ = crate::leanh::lean_ctor_get(v___x_2937_, 0);
                    crate::leanh::lean_inc(v_a_2939_);
                    crate::leanh::lean_dec_ref_known(v___x_2937_, 1);
                    v___x_2940_ = (crate::leanh::lean_unbox(v_a_2939_) as u8);
                    crate::leanh::lean_dec(v_a_2939_);
                    v___y_2924_ = v___x_2940_;
                    state = 18;
                    continue;
                }
            }
            4 => {
                v___x_2861_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2861_, 0, v___y_2857_);
                crate::leanh::lean_ctor_set(v___x_2861_, 1, v___y_2858_);
                crate::leanh::lean_ctor_set(v___x_2861_, 2, v___y_2856_);
                crate::leanh::lean_ctor_set(v___x_2861_, 3, v___y_2855_);
                crate::leanh::lean_ctor_set(v___x_2861_, 4, v_a_2850_);
                crate::leanh::lean_ctor_set(v___x_2861_, 5, v___y_2860_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2861_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                    v___y_2859_,
                );
                if v_isShared_2853_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2852_, 0, v___x_2861_);
                    v___x_2863_ = v___x_2852_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2864_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2861_);
                    v___x_2863_ = v_reuseFailAlloc_2864_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2863_;
            }
            6 => {
                if crate::leanh::lean_obj_tag(v___y_2866_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2866_, 1);
                    v___x_2872_ = crate::leanh::lean_box(0);
                    v___y_2855_ = v___y_2871_;
                    v___y_2856_ = v___y_2867_;
                    v___y_2857_ = v___y_2868_;
                    v___y_2858_ = v___y_2869_;
                    v___y_2859_ = v___y_2870_;
                    v___y_2860_ = v___x_2872_;
                    state = 4;
                    continue;
                } else {
                    v_a_2873_ = crate::leanh::lean_ctor_get(v___y_2866_, 0);
                    v_isSharedCheck_2880_ = (!crate::leanh::lean_is_exclusive(v___y_2866_)) as u8;
                    if v_isSharedCheck_2880_ == 0 {
                        v___x_2875_ = v___y_2866_;
                        v_isShared_2876_ = v_isSharedCheck_2880_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2873_);
                        crate::leanh::lean_dec(v___y_2866_);
                        v___x_2875_ = crate::leanh::lean_box(0);
                        v_isShared_2876_ = v_isSharedCheck_2880_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_2876_ == 0 {
                    v___x_2878_ = v___x_2875_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2879_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
                    v___x_2878_ = v_reuseFailAlloc_2879_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___y_2855_ = v___y_2871_;
                v___y_2856_ = v___y_2867_;
                v___y_2857_ = v___y_2868_;
                v___y_2858_ = v___y_2869_;
                v___y_2859_ = v___y_2870_;
                v___y_2860_ = v___x_2878_;
                state = 4;
                continue;
            }
            9 => {
                if crate::leanh::lean_obj_tag(v_initializationOptions_x3f_2839_) == 0 {
                    crate::leanh::lean_dec_ref_known(v_initializationOptions_x3f_2839_, 1);
                    v___x_2887_ = crate::leanh::lean_box(0);
                    v___y_2866_ = v___y_2882_;
                    v___y_2867_ = v___y_2886_;
                    v___y_2868_ = v___y_2883_;
                    v___y_2869_ = v___y_2884_;
                    v___y_2870_ = v___y_2885_;
                    v___y_2871_ = v___x_2887_;
                    state = 6;
                    continue;
                } else {
                    v_a_2888_ = crate::leanh::lean_ctor_get(v_initializationOptions_x3f_2839_, 0);
                    v_isSharedCheck_2895_ =
                        (!crate::leanh::lean_is_exclusive(v_initializationOptions_x3f_2839_)) as u8;
                    if v_isSharedCheck_2895_ == 0 {
                        v___x_2890_ = v_initializationOptions_x3f_2839_;
                        v_isShared_2891_ = v_isSharedCheck_2895_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2888_);
                        crate::leanh::lean_dec(v_initializationOptions_x3f_2839_);
                        v___x_2890_ = crate::leanh::lean_box(0);
                        v_isShared_2891_ = v_isSharedCheck_2895_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_2891_ == 0 {
                    v___x_2893_ = v___x_2890_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2894_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
                    v___x_2893_ = v_reuseFailAlloc_2894_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___y_2866_ = v___y_2882_;
                v___y_2867_ = v___y_2886_;
                v___y_2868_ = v___y_2883_;
                v___y_2869_ = v___y_2884_;
                v___y_2870_ = v___y_2885_;
                v___y_2871_ = v___x_2893_;
                state = 6;
                continue;
            }
            12 => {
                if crate::leanh::lean_obj_tag(v_rootUri_x3f_2837_) == 0 {
                    crate::leanh::lean_dec_ref_known(v_rootUri_x3f_2837_, 1);
                    v___x_2901_ = crate::leanh::lean_box(0);
                    v___y_2882_ = v___y_2897_;
                    v___y_2883_ = v___y_2898_;
                    v___y_2884_ = v___y_2900_;
                    v___y_2885_ = v___y_2899_;
                    v___y_2886_ = v___x_2901_;
                    state = 9;
                    continue;
                } else {
                    v_a_2902_ = crate::leanh::lean_ctor_get(v_rootUri_x3f_2837_, 0);
                    v_isSharedCheck_2909_ =
                        (!crate::leanh::lean_is_exclusive(v_rootUri_x3f_2837_)) as u8;
                    if v_isSharedCheck_2909_ == 0 {
                        v___x_2904_ = v_rootUri_x3f_2837_;
                        v_isShared_2905_ = v_isSharedCheck_2909_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2902_);
                        crate::leanh::lean_dec(v_rootUri_x3f_2837_);
                        v___x_2904_ = crate::leanh::lean_box(0);
                        v_isShared_2905_ = v_isSharedCheck_2909_;
                        state = 13;
                        continue;
                    }
                }
            }
            13 => {
                if v_isShared_2905_ == 0 {
                    v___x_2907_ = v___x_2904_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2908_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
                    v___x_2907_ = v_reuseFailAlloc_2908_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___y_2882_ = v___y_2897_;
                v___y_2883_ = v___y_2898_;
                v___y_2884_ = v___y_2900_;
                v___y_2885_ = v___y_2899_;
                v___y_2886_ = v___x_2907_;
                state = 9;
                continue;
            }
            15 => {
                if crate::leanh::lean_obj_tag(v_clientInfo_x3f_2835_) == 0 {
                    crate::leanh::lean_dec_ref_known(v_clientInfo_x3f_2835_, 1);
                    v___x_2914_ = crate::leanh::lean_box(0);
                    v___y_2897_ = v___y_2911_;
                    v___y_2898_ = v___y_2913_;
                    v___y_2899_ = v___y_2912_;
                    v___y_2900_ = v___x_2914_;
                    state = 12;
                    continue;
                } else {
                    v_a_2915_ = crate::leanh::lean_ctor_get(v_clientInfo_x3f_2835_, 0);
                    v_isSharedCheck_2922_ =
                        (!crate::leanh::lean_is_exclusive(v_clientInfo_x3f_2835_)) as u8;
                    if v_isSharedCheck_2922_ == 0 {
                        v___x_2917_ = v_clientInfo_x3f_2835_;
                        v_isShared_2918_ = v_isSharedCheck_2922_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2915_);
                        crate::leanh::lean_dec(v_clientInfo_x3f_2835_);
                        v___x_2917_ = crate::leanh::lean_box(0);
                        v_isShared_2918_ = v_isSharedCheck_2922_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_2918_ == 0 {
                    v___x_2920_ = v___x_2917_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2921_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
                    v___x_2920_ = v_reuseFailAlloc_2921_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___y_2897_ = v___y_2911_;
                v___y_2898_ = v___y_2913_;
                v___y_2899_ = v___y_2912_;
                v___y_2900_ = v___x_2920_;
                state = 12;
                continue;
            }
            18 => {
                v___x_2925_ = l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__6;
                v___x_2926_ =
                    l_Lean_Json_getObjValAs_x3f___redArg(v_j_2831_, v___x_2829_, v___x_2925_);
                if crate::leanh::lean_obj_tag(v_processId_x3f_2833_) == 0 {
                    crate::leanh::lean_dec_ref_known(v_processId_x3f_2833_, 1);
                    v___x_2927_ = crate::leanh::lean_box(0);
                    v___y_2911_ = v___x_2926_;
                    v___y_2912_ = v___y_2924_;
                    v___y_2913_ = v___x_2927_;
                    state = 15;
                    continue;
                } else {
                    v_a_2928_ = crate::leanh::lean_ctor_get(v_processId_x3f_2833_, 0);
                    v_isSharedCheck_2935_ =
                        (!crate::leanh::lean_is_exclusive(v_processId_x3f_2833_)) as u8;
                    if v_isSharedCheck_2935_ == 0 {
                        v___x_2930_ = v_processId_x3f_2833_;
                        v_isShared_2931_ = v_isSharedCheck_2935_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2928_);
                        crate::leanh::lean_dec(v_processId_x3f_2833_);
                        v___x_2930_ = crate::leanh::lean_box(0);
                        v_isShared_2931_ = v_isSharedCheck_2935_;
                        state = 19;
                        continue;
                    }
                }
            }
            19 => {
                if v_isShared_2931_ == 0 {
                    v___x_2933_ = v___x_2930_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2934_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
                    v___x_2933_ = v_reuseFailAlloc_2934_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___y_2911_ = v___x_2926_;
                v___y_2912_ = v___y_2924_;
                v___y_2913_ = v___x_2933_;
                state = 15;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_InitializedParams_toCtorIdx(
    mut v_x_2957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2958_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_2958_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonInitializedParams___lam__0(
    mut v_x_2961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2962_ = l_Lean_Lsp_instFromJsonInitializedParams___lam__0___closed__0;
    return v___x_2962_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonInitializedParams___lam__0___boxed(
    mut v_x_2963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2964_ = l_Lean_Lsp_instFromJsonInitializedParams___lam__0(v_x_2963_);
    crate::leanh::lean_dec(v_x_2963_);
    return v_res_2964_;
}
pub unsafe fn l_Lean_Lsp_instToJsonInitializedParams___lam__0(
    mut v_x_2967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2968_ = crate::leanh::lean_box(0);
    return v___x_2968_;
}
pub unsafe fn l_Lean_Lsp_instToJsonServerInfo_toJson(
    mut v_x_2971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_x3f_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2976_: u8 = 0;
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2991_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_2972_ = crate::leanh::lean_ctor_get(v_x_2971_, 0);
                v_version_x3f_2973_ = crate::leanh::lean_ctor_get(v_x_2971_, 1);
                v_isSharedCheck_2991_ = (!crate::leanh::lean_is_exclusive(v_x_2971_)) as u8;
                if v_isSharedCheck_2991_ == 0 {
                    v___x_2975_ = v_x_2971_;
                    v_isShared_2976_ = v_isSharedCheck_2991_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_version_x3f_2973_);
                    crate::leanh::lean_inc(v_name_2972_);
                    crate::leanh::lean_dec(v_x_2971_);
                    v___x_2975_ = crate::leanh::lean_box(0);
                    v_isShared_2976_ = v_isSharedCheck_2991_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2977_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0;
                v___x_2978_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2978_, 0, v_name_2972_);
                if v_isShared_2976_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2975_, 1, v___x_2978_);
                    crate::leanh::lean_ctor_set(v___x_2975_, 0, v___x_2977_);
                    v___x_2980_ = v___x_2975_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2990_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2977_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2990_, 1, v___x_2978_);
                    v___x_2980_ = v_reuseFailAlloc_2990_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2981_ = crate::leanh::lean_box(0);
                v___x_2982_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2982_, 0, v___x_2980_);
                crate::leanh::lean_ctor_set(v___x_2982_, 1, v___x_2981_);
                v___x_2983_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1;
                v___x_2984_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__0(
                    v___x_2983_,
                    v_version_x3f_2973_,
                );
                v___x_2985_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2985_, 0, v___x_2984_);
                crate::leanh::lean_ctor_set(v___x_2985_, 1, v___x_2981_);
                v___x_2986_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2986_, 0, v___x_2982_);
                crate::leanh::lean_ctor_set(v___x_2986_, 1, v___x_2985_);
                v___x_2987_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2;
                v___x_2988_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_2986_, v___x_2987_);
                v___x_2989_ = l_Lean_Json_mkObj(v___x_2988_);
                crate::leanh::lean_dec(v___x_2988_);
                return v___x_2989_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2999_: u8 = 0;
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2999_ = 1;
    v___x_3000_ = l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1;
    v___x_3001_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3000_, v___x_2999_);
    return v___x_3001_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3002_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5;
    v___x_3003_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2_once),
        _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2,
    );
    v___x_3004_ = lean_string_append(v___x_3003_, v___x_3002_);
    return v___x_3004_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3005_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8_once),
        _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8,
    );
    v___x_3006_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3,
    );
    v___x_3007_ = lean_string_append(v___x_3006_, v___x_3005_);
    return v___x_3007_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3008_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10;
    v___x_3009_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4,
    );
    v___x_3010_ = lean_string_append(v___x_3009_, v___x_3008_);
    return v___x_3010_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3011_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14_once),
        _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14,
    );
    v___x_3012_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3,
    );
    v___x_3013_ = lean_string_append(v___x_3012_, v___x_3011_);
    return v___x_3013_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3014_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10;
    v___x_3015_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6,
    );
    v___x_3016_ = lean_string_append(v___x_3015_, v___x_3014_);
    return v___x_3016_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonServerInfo_fromJson(
    mut v_json_3017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3023_: u8 = 0;
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3029_: u8 = 0;
    let mut v_a_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3033_: u8 = 0;
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3037_: u8 = 0;
    let mut v_a_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3044_: u8 = 0;
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3050_: u8 = 0;
    let mut v_a_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3054_: u8 = 0;
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3058_: u8 = 0;
    let mut v_a_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3062_: u8 = 0;
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3067_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3018_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0;
                crate::leanh::lean_inc(v_json_3017_);
                v___x_3019_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__0(v_json_3017_, v___x_3018_);
                if crate::leanh::lean_obj_tag(v___x_3019_) == 0 {
                    crate::leanh::lean_dec(v_json_3017_);
                    v_a_3020_ = crate::leanh::lean_ctor_get(v___x_3019_, 0);
                    v_isSharedCheck_3029_ = (!crate::leanh::lean_is_exclusive(v___x_3019_)) as u8;
                    if v_isSharedCheck_3029_ == 0 {
                        v___x_3022_ = v___x_3019_;
                        v_isShared_3023_ = v_isSharedCheck_3029_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3020_);
                        crate::leanh::lean_dec(v___x_3019_);
                        v___x_3022_ = crate::leanh::lean_box(0);
                        v_isShared_3023_ = v_isSharedCheck_3029_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_3019_) == 0 {
                        crate::leanh::lean_dec(v_json_3017_);
                        v_a_3030_ = crate::leanh::lean_ctor_get(v___x_3019_, 0);
                        v_isSharedCheck_3037_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3019_)) as u8;
                        if v_isSharedCheck_3037_ == 0 {
                            v___x_3032_ = v___x_3019_;
                            v_isShared_3033_ = v_isSharedCheck_3037_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3030_);
                            crate::leanh::lean_dec(v___x_3019_);
                            v___x_3032_ = crate::leanh::lean_box(0);
                            v_isShared_3033_ = v_isSharedCheck_3037_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3038_ = crate::leanh::lean_ctor_get(v___x_3019_, 0);
                        crate::leanh::lean_inc(v_a_3038_);
                        crate::leanh::lean_dec_ref_known(v___x_3019_, 1);
                        v___x_3039_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1;
                        v___x_3040_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1(v_json_3017_, v___x_3039_);
                        if crate::leanh::lean_obj_tag(v___x_3040_) == 0 {
                            crate::leanh::lean_dec(v_a_3038_);
                            v_a_3041_ = crate::leanh::lean_ctor_get(v___x_3040_, 0);
                            v_isSharedCheck_3050_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3040_)) as u8;
                            if v_isSharedCheck_3050_ == 0 {
                                v___x_3043_ = v___x_3040_;
                                v_isShared_3044_ = v_isSharedCheck_3050_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3041_);
                                crate::leanh::lean_dec(v___x_3040_);
                                v___x_3043_ = crate::leanh::lean_box(0);
                                v_isShared_3044_ = v_isSharedCheck_3050_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_3040_) == 0 {
                                crate::leanh::lean_dec(v_a_3038_);
                                v_a_3051_ = crate::leanh::lean_ctor_get(v___x_3040_, 0);
                                v_isSharedCheck_3058_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3040_)) as u8;
                                if v_isSharedCheck_3058_ == 0 {
                                    v___x_3053_ = v___x_3040_;
                                    v_isShared_3054_ = v_isSharedCheck_3058_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3051_);
                                    crate::leanh::lean_dec(v___x_3040_);
                                    v___x_3053_ = crate::leanh::lean_box(0);
                                    v_isShared_3054_ = v_isSharedCheck_3058_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_3059_ = crate::leanh::lean_ctor_get(v___x_3040_, 0);
                                v_isSharedCheck_3067_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3040_)) as u8;
                                if v_isSharedCheck_3067_ == 0 {
                                    v___x_3061_ = v___x_3040_;
                                    v_isShared_3062_ = v_isSharedCheck_3067_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3059_);
                                    crate::leanh::lean_dec(v___x_3040_);
                                    v___x_3061_ = crate::leanh::lean_box(0);
                                    v_isShared_3062_ = v_isSharedCheck_3067_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3024_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5,
                );
                v___x_3025_ = lean_string_append(v___x_3024_, v_a_3020_);
                crate::leanh::lean_dec(v_a_3020_);
                if v_isShared_3023_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3022_, 0, v___x_3025_);
                    v___x_3027_ = v___x_3022_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3028_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3025_);
                    v___x_3027_ = v_reuseFailAlloc_3028_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3027_;
            }
            3 => {
                if v_isShared_3033_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3032_, 0);
                    v___x_3035_ = v___x_3032_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3036_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
                    v___x_3035_ = v_reuseFailAlloc_3036_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3035_;
            }
            5 => {
                v___x_3045_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7,
                );
                v___x_3046_ = lean_string_append(v___x_3045_, v_a_3041_);
                crate::leanh::lean_dec(v_a_3041_);
                if v_isShared_3044_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3043_, 0, v___x_3046_);
                    v___x_3048_ = v___x_3043_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3049_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3046_);
                    v___x_3048_ = v_reuseFailAlloc_3049_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3048_;
            }
            7 => {
                if v_isShared_3054_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3053_, 0);
                    v___x_3056_ = v___x_3053_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3057_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
                    v___x_3056_ = v_reuseFailAlloc_3057_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3056_;
            }
            9 => {
                v___x_3063_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3063_, 0, v_a_3038_);
                crate::leanh::lean_ctor_set(v___x_3063_, 1, v_a_3059_);
                if v_isShared_3062_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3061_, 0, v___x_3063_);
                    v___x_3065_ = v___x_3061_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3066_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3063_);
                    v___x_3065_ = v_reuseFailAlloc_3066_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3065_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeResult_toJson_spec__0(
    mut v_k_3070_: *mut crate::leanh::LeanObject,
    mut v_x_3071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3071_) == 0 {
        let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_3070_);
        v___x_3072_ = crate::leanh::lean_box(0);
        return v___x_3072_;
    } else {
        let mut v_val_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3073_ = crate::leanh::lean_ctor_get(v_x_3071_, 0);
        crate::leanh::lean_inc(v_val_3073_);
        crate::leanh::lean_dec_ref_known(v_x_3071_, 1);
        v___x_3074_ = l_Lean_Lsp_instToJsonServerInfo_toJson(v_val_3073_);
        v___x_3075_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3075_, 0, v_k_3070_);
        crate::leanh::lean_ctor_set(v___x_3075_, 1, v___x_3074_);
        v___x_3076_ = crate::leanh::lean_box(0);
        v___x_3077_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3077_, 0, v___x_3075_);
        crate::leanh::lean_ctor_set(v___x_3077_, 1, v___x_3076_);
        return v___x_3077_;
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonInitializeResult_toJson(
    mut v_x_3079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_capabilities_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_serverInfo_x3f_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3084_: u8 = 0;
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3099_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_capabilities_3080_ = crate::leanh::lean_ctor_get(v_x_3079_, 0);
                v_serverInfo_x3f_3081_ = crate::leanh::lean_ctor_get(v_x_3079_, 1);
                v_isSharedCheck_3099_ = (!crate::leanh::lean_is_exclusive(v_x_3079_)) as u8;
                if v_isSharedCheck_3099_ == 0 {
                    v___x_3083_ = v_x_3079_;
                    v_isShared_3084_ = v_isSharedCheck_3099_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_serverInfo_x3f_3081_);
                    crate::leanh::lean_inc(v_capabilities_3080_);
                    crate::leanh::lean_dec(v_x_3079_);
                    v___x_3083_ = crate::leanh::lean_box(0);
                    v_isShared_3084_ = v_isSharedCheck_3099_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3085_ = l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4;
                v___x_3086_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson(v_capabilities_3080_);
                if v_isShared_3084_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3083_, 1, v___x_3086_);
                    crate::leanh::lean_ctor_set(v___x_3083_, 0, v___x_3085_);
                    v___x_3088_ = v___x_3083_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3098_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 1, v___x_3086_);
                    v___x_3088_ = v_reuseFailAlloc_3098_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3089_ = crate::leanh::lean_box(0);
                v___x_3090_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3090_, 0, v___x_3088_);
                crate::leanh::lean_ctor_set(v___x_3090_, 1, v___x_3089_);
                v___x_3091_ = l_Lean_Lsp_instToJsonInitializeResult_toJson___closed__0;
                v___x_3092_ =
                    l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeResult_toJson_spec__0(
                        v___x_3091_,
                        v_serverInfo_x3f_3081_,
                    );
                v___x_3093_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3093_, 0, v___x_3092_);
                crate::leanh::lean_ctor_set(v___x_3093_, 1, v___x_3089_);
                v___x_3094_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3094_, 0, v___x_3090_);
                crate::leanh::lean_ctor_set(v___x_3094_, 1, v___x_3093_);
                v___x_3095_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2;
                v___x_3096_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_3094_, v___x_3095_);
                v___x_3097_ = l_Lean_Json_mkObj(v___x_3096_);
                crate::leanh::lean_dec(v___x_3096_);
                return v___x_3097_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0(
    mut v_j_3102_: *mut crate::leanh::LeanObject,
    mut v_k_3103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3104_ = l_Lean_Json_getObjValD(v_j_3102_, v_k_3103_);
    v___x_3105_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson(v___x_3104_);
    return v___x_3105_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0___boxed(
    mut v_j_3106_: *mut crate::leanh::LeanObject,
    mut v_k_3107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3108_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0(
            v_j_3106_, v_k_3107_,
        );
    crate::leanh::lean_dec_ref(v_k_3107_);
    return v_res_3108_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1(
    mut v_x_3111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3117_: u8 = 0;
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3121_: u8 = 0;
    let mut v_a_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3125_: u8 = 0;
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3130_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3111_) == 0 {
                    v___x_3112_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1___closed__0;
                    return v___x_3112_;
                } else {
                    v___x_3113_ = l_Lean_Lsp_instFromJsonServerInfo_fromJson(v_x_3111_);
                    if crate::leanh::lean_obj_tag(v___x_3113_) == 0 {
                        v_a_3114_ = crate::leanh::lean_ctor_get(v___x_3113_, 0);
                        v_isSharedCheck_3121_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3113_)) as u8;
                        if v_isSharedCheck_3121_ == 0 {
                            v___x_3116_ = v___x_3113_;
                            v_isShared_3117_ = v_isSharedCheck_3121_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3114_);
                            crate::leanh::lean_dec(v___x_3113_);
                            v___x_3116_ = crate::leanh::lean_box(0);
                            v_isShared_3117_ = v_isSharedCheck_3121_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3122_ = crate::leanh::lean_ctor_get(v___x_3113_, 0);
                        v_isSharedCheck_3130_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3113_)) as u8;
                        if v_isSharedCheck_3130_ == 0 {
                            v___x_3124_ = v___x_3113_;
                            v_isShared_3125_ = v_isSharedCheck_3130_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3122_);
                            crate::leanh::lean_dec(v___x_3113_);
                            v___x_3124_ = crate::leanh::lean_box(0);
                            v_isShared_3125_ = v_isSharedCheck_3130_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3117_ == 0 {
                    v___x_3119_ = v___x_3116_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3120_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
                    v___x_3119_ = v_reuseFailAlloc_3120_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3119_;
            }
            3 => {
                v___x_3126_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3126_, 0, v_a_3122_);
                if v_isShared_3125_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3124_, 0, v___x_3126_);
                    v___x_3128_ = v___x_3124_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3129_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3126_);
                    v___x_3128_ = v_reuseFailAlloc_3129_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3128_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1(
    mut v_j_3131_: *mut crate::leanh::LeanObject,
    mut v_k_3132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3133_ = l_Lean_Json_getObjValD(v_j_3131_, v_k_3132_);
    v___x_3134_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1(v___x_3133_);
    return v___x_3134_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1___boxed(
    mut v_j_3135_: *mut crate::leanh::LeanObject,
    mut v_k_3136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3137_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1(
            v_j_3135_, v_k_3136_,
        );
    crate::leanh::lean_dec_ref(v_k_3136_);
    return v_res_3137_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3143_: u8 = 0;
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3143_ = 1;
    v___x_3144_ = l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1;
    v___x_3145_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3144_, v___x_3143_);
    return v___x_3145_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3146_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5;
    v___x_3147_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2_once),
        _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2,
    );
    v___x_3148_ = lean_string_append(v___x_3147_, v___x_3146_);
    return v___x_3148_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3151_: u8 = 0;
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3151_ = 1;
    v___x_3152_ = l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__4;
    v___x_3153_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3152_, v___x_3151_);
    return v___x_3153_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3154_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5_once),
        _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5,
    );
    v___x_3155_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3,
    );
    v___x_3156_ = lean_string_append(v___x_3155_, v___x_3154_);
    return v___x_3156_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3157_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10;
    v___x_3158_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6,
    );
    v___x_3159_ = lean_string_append(v___x_3158_, v___x_3157_);
    return v___x_3159_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3163_: u8 = 0;
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3163_ = 1;
    v___x_3164_ = l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__9;
    v___x_3165_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3164_, v___x_3163_);
    return v___x_3165_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3166_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10_once),
        _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10,
    );
    v___x_3167_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3,
    );
    v___x_3168_ = lean_string_append(v___x_3167_, v___x_3166_);
    return v___x_3168_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3169_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10;
    v___x_3170_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11_once),
        _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11,
    );
    v___x_3171_ = lean_string_append(v___x_3170_, v___x_3169_);
    return v___x_3171_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonInitializeResult_fromJson(
    mut v_json_3172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3178_: u8 = 0;
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3184_: u8 = 0;
    let mut v_a_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3188_: u8 = 0;
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3192_: u8 = 0;
    let mut v_a_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3199_: u8 = 0;
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3205_: u8 = 0;
    let mut v_a_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3209_: u8 = 0;
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3213_: u8 = 0;
    let mut v_a_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3217_: u8 = 0;
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3222_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3173_ = l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4;
                crate::leanh::lean_inc(v_json_3172_);
                v___x_3174_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0(v_json_3172_, v___x_3173_);
                if crate::leanh::lean_obj_tag(v___x_3174_) == 0 {
                    crate::leanh::lean_dec(v_json_3172_);
                    v_a_3175_ = crate::leanh::lean_ctor_get(v___x_3174_, 0);
                    v_isSharedCheck_3184_ = (!crate::leanh::lean_is_exclusive(v___x_3174_)) as u8;
                    if v_isSharedCheck_3184_ == 0 {
                        v___x_3177_ = v___x_3174_;
                        v_isShared_3178_ = v_isSharedCheck_3184_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3175_);
                        crate::leanh::lean_dec(v___x_3174_);
                        v___x_3177_ = crate::leanh::lean_box(0);
                        v_isShared_3178_ = v_isSharedCheck_3184_;
                        state = 1;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___x_3174_) == 0 {
                        crate::leanh::lean_dec(v_json_3172_);
                        v_a_3185_ = crate::leanh::lean_ctor_get(v___x_3174_, 0);
                        v_isSharedCheck_3192_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3174_)) as u8;
                        if v_isSharedCheck_3192_ == 0 {
                            v___x_3187_ = v___x_3174_;
                            v_isShared_3188_ = v_isSharedCheck_3192_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3185_);
                            crate::leanh::lean_dec(v___x_3174_);
                            v___x_3187_ = crate::leanh::lean_box(0);
                            v_isShared_3188_ = v_isSharedCheck_3192_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3193_ = crate::leanh::lean_ctor_get(v___x_3174_, 0);
                        crate::leanh::lean_inc(v_a_3193_);
                        crate::leanh::lean_dec_ref_known(v___x_3174_, 1);
                        v___x_3194_ = l_Lean_Lsp_instToJsonInitializeResult_toJson___closed__0;
                        v___x_3195_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1(v_json_3172_, v___x_3194_);
                        if crate::leanh::lean_obj_tag(v___x_3195_) == 0 {
                            crate::leanh::lean_dec(v_a_3193_);
                            v_a_3196_ = crate::leanh::lean_ctor_get(v___x_3195_, 0);
                            v_isSharedCheck_3205_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3195_)) as u8;
                            if v_isSharedCheck_3205_ == 0 {
                                v___x_3198_ = v___x_3195_;
                                v_isShared_3199_ = v_isSharedCheck_3205_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3196_);
                                crate::leanh::lean_dec(v___x_3195_);
                                v___x_3198_ = crate::leanh::lean_box(0);
                                v_isShared_3199_ = v_isSharedCheck_3205_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_3195_) == 0 {
                                crate::leanh::lean_dec(v_a_3193_);
                                v_a_3206_ = crate::leanh::lean_ctor_get(v___x_3195_, 0);
                                v_isSharedCheck_3213_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3195_)) as u8;
                                if v_isSharedCheck_3213_ == 0 {
                                    v___x_3208_ = v___x_3195_;
                                    v_isShared_3209_ = v_isSharedCheck_3213_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3206_);
                                    crate::leanh::lean_dec(v___x_3195_);
                                    v___x_3208_ = crate::leanh::lean_box(0);
                                    v_isShared_3209_ = v_isSharedCheck_3213_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_3214_ = crate::leanh::lean_ctor_get(v___x_3195_, 0);
                                v_isSharedCheck_3222_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3195_)) as u8;
                                if v_isSharedCheck_3222_ == 0 {
                                    v___x_3216_ = v___x_3195_;
                                    v_isShared_3217_ = v_isSharedCheck_3222_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3214_);
                                    crate::leanh::lean_dec(v___x_3195_);
                                    v___x_3216_ = crate::leanh::lean_box(0);
                                    v_isShared_3217_ = v_isSharedCheck_3222_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3179_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7,
                );
                v___x_3180_ = lean_string_append(v___x_3179_, v_a_3175_);
                crate::leanh::lean_dec(v_a_3175_);
                if v_isShared_3178_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3177_, 0, v___x_3180_);
                    v___x_3182_ = v___x_3177_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3183_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3180_);
                    v___x_3182_ = v_reuseFailAlloc_3183_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3182_;
            }
            3 => {
                if v_isShared_3188_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3187_, 0);
                    v___x_3190_ = v___x_3187_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3191_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_a_3185_);
                    v___x_3190_ = v_reuseFailAlloc_3191_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3190_;
            }
            5 => {
                v___x_3200_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12,
                );
                v___x_3201_ = lean_string_append(v___x_3200_, v_a_3196_);
                crate::leanh::lean_dec(v_a_3196_);
                if v_isShared_3199_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3198_, 0, v___x_3201_);
                    v___x_3203_ = v___x_3198_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3204_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3204_, 0, v___x_3201_);
                    v___x_3203_ = v_reuseFailAlloc_3204_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3203_;
            }
            7 => {
                if v_isShared_3209_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3208_, 0);
                    v___x_3211_ = v___x_3208_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3212_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
                    v___x_3211_ = v_reuseFailAlloc_3212_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3211_;
            }
            9 => {
                v___x_3218_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3218_, 0, v_a_3193_);
                crate::leanh::lean_ctor_set(v___x_3218_, 1, v_a_3214_);
                if v_isShared_3217_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3216_, 0, v___x_3218_);
                    v___x_3220_ = v___x_3216_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3221_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3218_);
                    v___x_3220_ = v_reuseFailAlloc_3221_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3220_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Lsp_InitShutdown(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Lsp_Capabilities(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Workspace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Lsp_InitShutdown(
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
pub unsafe fn initialize_Lean_Data_Lsp_InitShutdown(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Lsp_Capabilities(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Lsp_Workspace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_InitShutdown(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Lsp_InitShutdown(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Lsp_InitShutdown(builtin);
}
