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
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr3};
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_div, lean_nat_mul, lean_string_dec_eq, lean_string_hash, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once,
    lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1_value: LeanStringObject<8> =
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
        m_data: [118, 101, 114, 115, 105, 111, 110, 0],
    };
static mut l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2_value: LeanArrayObject<0> =
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
static mut l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonClientInfo___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonClientInfo_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonClientInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonClientInfo___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonClientInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonClientInfo___closed__0_value) as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1_value: LeanStringObject<4> =
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
        m_data: [76, 115, 112, 0],
    };
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__2_value: LeanStringObject<11> =
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
        m_data: [67, 108, 105, 101, 110, 116, 73, 110, 102, 111, 0],
    };
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__2_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1_value)
                as *mut LeanObject,
            6773744487318448338 as *mut LeanObject,
        ],
    };
pub static l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__2_value)
                as *mut LeanObject,
            3907392747204505285 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5_value: LeanStringObject<2> =
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
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0_value)
                as *mut LeanObject,
            5949480926448383572 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10_value: LeanStringObject<3> =
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
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__12_value: LeanStringObject<9> =
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
        m_data: [118, 101, 114, 115, 105, 111, 110, 63, 0],
    };
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__13_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__12_value)
                as *mut LeanObject,
            5707914067652744443 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__13_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__16: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonClientInfo___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonClientInfo_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonClientInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonClientInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTrace___lam__0___closed__0_value: LeanStringObject<14> =
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
            117, 110, 107, 110, 111, 119, 110, 32, 116, 114, 97, 99, 101, 0,
        ],
    };
static mut l_Lean_Lsp_instFromJsonTrace___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTrace___lam__0___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonTrace___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTrace___lam__0___closed__2_value: LeanStringObject<4> =
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
        m_data: [111, 102, 102, 0],
    };
static mut l_Lean_Lsp_instFromJsonTrace___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTrace___lam__0___closed__3_value: LeanStringObject<9> =
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
        m_data: [109, 101, 115, 115, 97, 103, 101, 115, 0],
    };
static mut l_Lean_Lsp_instFromJsonTrace___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTrace___lam__0___closed__4_value: LeanStringObject<8> =
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
        m_data: [118, 101, 114, 98, 111, 115, 101, 0],
    };
static mut l_Lean_Lsp_instFromJsonTrace___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTrace___lam__0___closed__5_value: LeanCtorObject<1> =
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
static mut l_Lean_Lsp_instFromJsonTrace___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTrace___lam__0___closed__6_value: LeanCtorObject<1> =
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
static mut l_Lean_Lsp_instFromJsonTrace___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTrace___lam__0___closed__7_value: LeanCtorObject<1> =
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
static mut l_Lean_Lsp_instFromJsonTrace___lam__0___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__7_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTrace___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonTrace___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonTrace___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonTrace: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_Trace_hasToJson___lam__0___closed__0_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_Trace_hasToJson___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_Trace_hasToJson___lam__0___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_Trace_hasToJson___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Lsp_Trace_hasToJson___lam__0___closed__2_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___lam__0___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_Trace_hasToJson___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_Trace_hasToJson___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_Lsp_Trace_hasToJson___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_Trace_hasToJson___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_Trace_hasToJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_Trace_hasToJson___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_Trace_hasToJson: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_Trace_hasToJson___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__5_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__6_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__7_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__8_value: LeanCtorObject<5> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__9_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonHashSet___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonHashSet___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonHashSet___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__0_value: LeanClosureObject<
    1,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__9_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__1_value: LeanClosureObject<
    1,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instForInOfForIn_x27___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__0_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__4_value: LeanStringObject<
    51,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__5_value: LeanCtorObject<1> =
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
            l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__4_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Except_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Except_instMonad___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Except_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Except_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___closed__4_value: LeanClosureObject<1> =
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
        m_fun: l_Except_map as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___closed__5_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___closed__6_value: LeanClosureObject<1> =
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
        m_fun: l_Except_pure as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___closed__7_value: LeanCtorObject<5> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___closed__8_value: LeanClosureObject<1> =
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
        m_fun: l_Except_bind as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonHashSet___redArg___closed__9_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonHashSet___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__0_value) as *mut LeanObject;
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__4_value) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__3_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__0_value: LeanStringObject<7> =
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
        m_data: [108, 111, 103, 68, 105, 114, 0],
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__1_value: LeanStringObject<10> =
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
        m_data: [76, 111, 103, 67, 111, 110, 102, 105, 103, 0],
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__1_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1_value)
                as *mut LeanObject,
            6773744487318448338 as *mut LeanObject,
        ],
    };
pub static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__1_value)
                as *mut LeanObject,
            13822333033241362512 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__5_value: LeanStringObject<8> =
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
        m_data: [108, 111, 103, 68, 105, 114, 63, 0],
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__5_value)
                as *mut LeanObject,
            12006921733506407479 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__10_value: LeanStringObject<15> =
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
            97, 108, 108, 111, 119, 101, 100, 77, 101, 116, 104, 111, 100, 115, 0,
        ],
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__11_value: LeanStringObject<16> =
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
            97, 108, 108, 111, 119, 101, 100, 77, 101, 116, 104, 111, 100, 115, 63, 0,
        ],
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__11_value)
                as *mut LeanObject,
            2002671136272417502 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__16_value: LeanStringObject<18> =
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
            100, 105, 115, 97, 108, 108, 111, 119, 101, 100, 77, 101, 116, 104, 111, 100, 115, 0,
        ],
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__17_value: LeanStringObject<19> =
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
            100, 105, 115, 97, 108, 108, 111, 119, 101, 100, 77, 101, 116, 104, 111, 100, 115, 63,
            0,
        ],
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__18_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__17_value)
                as *mut LeanObject,
            16624093685862140986 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__18_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonLogConfig___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonLogConfig_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonLogConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonLogConfig: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonLogConfig___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonLogConfig___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonLogConfig_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonLogConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLogConfig___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonLogConfig: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonLogConfig___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__0_value: LeanStringObject<
    11,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__1_value: LeanStringObject<
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
    m_data: [108, 111, 103, 67, 102, 103, 0],
};
static mut l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonInitializationOptions___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonInitializationOptions_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonInitializationOptions___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializationOptions___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonInitializationOptions: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializationOptions___closed__0_value)
        as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2___closed__0_value) as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__0_value:
    LeanStringObject<22> = LeanStringObject {
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
        73, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 79, 112, 116, 105, 111,
        110, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__0_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1_value_aux_1:
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
            l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1_value)
            as *mut LeanObject,
        6773744487318448338 as *mut LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1_value: LeanCtorObject<
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
            l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__0_value)
            as *mut LeanObject,
        7316217595702879692 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__4_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__5_value: LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__4_value)
            as *mut LeanObject,
        2865615965707119338 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__9_value:
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
    m_data: [108, 111, 103, 67, 102, 103, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__10_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__9_value)
            as *mut LeanObject,
        1435684361439067299 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonInitializationOptions___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonInitializationOptions_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonInitializationOptions___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonInitializationOptions: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__0_value: LeanStringObject<10> =
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
        m_data: [112, 114, 111, 99, 101, 115, 115, 73, 100, 0],
    };
static mut l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__1_value: LeanStringObject<11> =
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
        m_data: [99, 108, 105, 101, 110, 116, 73, 110, 102, 111, 0],
    };
static mut l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__2_value: LeanStringObject<8> =
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
        m_data: [114, 111, 111, 116, 85, 114, 105, 0],
    };
static mut l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__3_value: LeanStringObject<22> =
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
            105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 79, 112, 116, 105,
            111, 110, 115, 0,
        ],
    };
static mut l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4_value: LeanStringObject<13> =
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
        m_data: [99, 97, 112, 97, 98, 105, 108, 105, 116, 105, 101, 115, 0],
    };
static mut l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__5_value: LeanStringObject<6> =
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
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__6_value: LeanStringObject<17> =
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
            119, 111, 114, 107, 115, 112, 97, 99, 101, 70, 111, 108, 100, 101, 114, 115, 0,
        ],
    };
static mut l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonInitializeParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonInitializeParams_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonInitializeParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeParams___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonInitializeParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeParams___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializeParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_getInt_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonInitializeParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializeParams___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_getStr_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonInitializeParams___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializeParams___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonClientCapabilities_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonInitializeParams___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializeParams___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonInitializeParams___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializeParams___closed__4_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Array_fromJson_x3f as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 2,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonInitializeParams___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializeParams___closed__5_value: LeanClosureObject<7> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 7) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Lsp_instFromJsonInitializeParams___lam__0 as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 7,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializationOptions___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTrace___closed__0_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonInitializeParams___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__5_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonInitializeParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeParams___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializedParams___lam__0___closed__0_value: LeanCtorObject<1> =
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
static mut l_Lean_Lsp_instFromJsonInitializedParams___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializedParams___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializedParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonInitializedParams___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonInitializedParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializedParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonInitializedParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializedParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonInitializedParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonInitializedParams___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonInitializedParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializedParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonInitializedParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializedParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonServerInfo___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonServerInfo_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonServerInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerInfo___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonServerInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonServerInfo___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__0_value: LeanStringObject<11> =
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
        m_data: [83, 101, 114, 118, 101, 114, 73, 110, 102, 111, 0],
    };
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__0_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1_value)
                as *mut LeanObject,
            6773744487318448338 as *mut LeanObject,
        ],
    };
pub static l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__0_value)
                as *mut LeanObject,
            213377184366943763 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonServerInfo___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonServerInfo_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonServerInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerInfo___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonServerInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonServerInfo___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonInitializeResult_toJson___closed__0_value: LeanStringObject<11> =
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
        m_data: [115, 101, 114, 118, 101, 114, 73, 110, 102, 111, 0],
    };
static mut l_Lean_Lsp_instToJsonInitializeResult_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeResult_toJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonInitializeResult___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonInitializeResult_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonInitializeResult___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeResult___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonInitializeResult: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeResult___closed__0_value) as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__0_value: LeanStringObject<
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
        73, 110, 105, 116, 105, 97, 108, 105, 122, 101, 82, 101, 115, 117, 108, 116, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__0_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__1_value)
                as *mut LeanObject,
            6773744487318448338 as *mut LeanObject,
        ],
    };
pub static l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1_value: LeanCtorObject<3> =
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
                l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__0_value)
                as *mut LeanObject,
            4948849926862197272 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4_value)
                as *mut LeanObject,
            18164368300990074274 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__8_value: LeanStringObject<
    12,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__8_value)
                as *mut LeanObject,
            1486792206322009551 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__9_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonInitializeResult___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonInitializeResult_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonInitializeResult___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeResult___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonInitializeResult: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonInitializeResult___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__0(
    mut v_k_1613_: *mut LeanObject,
    mut v_x_1614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1619_: u8 = 0;
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1626_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1614_) == 0 {
                    lean_dec_ref(v_k_1613_);
                    v___x_1615_ = lean_box(0);
                    return v___x_1615_;
                } else {
                    v_val_1616_ = lean_ctor_get(v_x_1614_, 0);
                    v_isSharedCheck_1626_ = (!lean_is_exclusive(v_x_1614_)) as u8;
                    if v_isSharedCheck_1626_ == 0 {
                        v___x_1618_ = v_x_1614_;
                        v_isShared_1619_ = v_isSharedCheck_1626_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1616_);
                        lean_dec(v_x_1614_);
                        v___x_1618_ = lean_box(0);
                        v_isShared_1619_ = v_isSharedCheck_1626_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1619_ == 0 {
                    lean_ctor_set_tag(v___x_1618_, 3);
                    v___x_1621_ = v___x_1618_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1625_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_val_1616_);
                    v___x_1621_ = v_reuseFailAlloc_1625_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1622_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1622_, 0, v_k_1613_);
                lean_ctor_set(v___x_1622_, 1, v___x_1621_);
                v___x_1623_ = lean_box(0);
                v___x_1624_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1624_, 0, v___x_1622_);
                lean_ctor_set(v___x_1624_, 1, v___x_1623_);
                return v___x_1624_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(
    mut v_a_1627_: *mut LeanObject,
    mut v_a_1628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1627_) == 0 {
                    v___x_1629_ = lean_array_to_list(v_a_1628_);
                    return v___x_1629_;
                } else {
                    v_head_1630_ = lean_ctor_get(v_a_1627_, 0);
                    lean_inc(v_head_1630_);
                    v_tail_1631_ = lean_ctor_get(v_a_1627_, 1);
                    lean_inc(v_tail_1631_);
                    lean_dec_ref_known(v_a_1627_, 2);
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
    mut v_x_1638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_version_x3f_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1643_: u8 = 0;
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1658_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_1639_ = lean_ctor_get(v_x_1638_, 0);
                v_version_x3f_1640_ = lean_ctor_get(v_x_1638_, 1);
                v_isSharedCheck_1658_ = (!lean_is_exclusive(v_x_1638_)) as u8;
                if v_isSharedCheck_1658_ == 0 {
                    v___x_1642_ = v_x_1638_;
                    v_isShared_1643_ = v_isSharedCheck_1658_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_version_x3f_1640_);
                    lean_inc(v_name_1639_);
                    lean_dec(v_x_1638_);
                    v___x_1642_ = lean_box(0);
                    v_isShared_1643_ = v_isSharedCheck_1658_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1644_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0;
                v___x_1645_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1645_, 0, v_name_1639_);
                if v_isShared_1643_ == 0 {
                    lean_ctor_set(v___x_1642_, 1, v___x_1645_);
                    lean_ctor_set(v___x_1642_, 0, v___x_1644_);
                    v___x_1647_ = v___x_1642_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1644_);
                    lean_ctor_set(v_reuseFailAlloc_1657_, 1, v___x_1645_);
                    v___x_1647_ = v_reuseFailAlloc_1657_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1648_ = lean_box(0);
                v___x_1649_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1649_, 0, v___x_1647_);
                lean_ctor_set(v___x_1649_, 1, v___x_1648_);
                v___x_1650_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1;
                v___x_1651_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__0(
                    v___x_1650_,
                    v_version_x3f_1640_,
                );
                v___x_1652_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1652_, 0, v___x_1651_);
                lean_ctor_set(v___x_1652_, 1, v___x_1648_);
                v___x_1653_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1653_, 0, v___x_1649_);
                lean_ctor_set(v___x_1653_, 1, v___x_1652_);
                v___x_1654_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2;
                v___x_1655_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_1653_, v___x_1654_);
                v___x_1656_ = l_Lean_Json_mkObj(v___x_1655_);
                lean_dec(v___x_1655_);
                return v___x_1656_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__0(
    mut v_j_1661_: *mut LeanObject,
    mut v_k_1662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    v___x_1663_ = l_Lean_Json_getObjValD(v_j_1661_, v_k_1662_);
    v___x_1664_ = l_Lean_Json_getStr_x3f(v___x_1663_);
    return v___x_1664_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__0___boxed(
    mut v_j_1665_: *mut LeanObject,
    mut v_k_1666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1667_: *mut LeanObject = core::ptr::null_mut();
    v_res_1667_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__0(
            v_j_1665_, v_k_1666_,
        );
    lean_dec_ref(v_k_1666_);
    return v_res_1667_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1(
    mut v_x_1670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1676_: u8 = 0;
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1680_: u8 = 0;
    let mut v_a_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1684_: u8 = 0;
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1689_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1670_) == 0 {
                    v___x_1671_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1___closed__0;
                    return v___x_1671_;
                } else {
                    v___x_1672_ = l_Lean_Json_getStr_x3f(v_x_1670_);
                    if lean_obj_tag(v___x_1672_) == 0 {
                        v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
                        v_isSharedCheck_1680_ = (!lean_is_exclusive(v___x_1672_)) as u8;
                        if v_isSharedCheck_1680_ == 0 {
                            v___x_1675_ = v___x_1672_;
                            v_isShared_1676_ = v_isSharedCheck_1680_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1673_);
                            lean_dec(v___x_1672_);
                            v___x_1675_ = lean_box(0);
                            v_isShared_1676_ = v_isSharedCheck_1680_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1681_ = lean_ctor_get(v___x_1672_, 0);
                        v_isSharedCheck_1689_ = (!lean_is_exclusive(v___x_1672_)) as u8;
                        if v_isSharedCheck_1689_ == 0 {
                            v___x_1683_ = v___x_1672_;
                            v_isShared_1684_ = v_isSharedCheck_1689_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1681_);
                            lean_dec(v___x_1672_);
                            v___x_1683_ = lean_box(0);
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
                    v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
                    v___x_1678_ = v_reuseFailAlloc_1679_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1678_;
            }
            3 => {
                v___x_1685_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1685_, 0, v_a_1681_);
                if v_isShared_1684_ == 0 {
                    lean_ctor_set(v___x_1683_, 0, v___x_1685_);
                    v___x_1687_ = v___x_1683_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1685_);
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
    mut v_j_1690_: *mut LeanObject,
    mut v_k_1691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    v___x_1692_ = l_Lean_Json_getObjValD(v_j_1690_, v_k_1691_);
    v___x_1693_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1(v___x_1692_);
    return v___x_1693_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1___boxed(
    mut v_j_1694_: *mut LeanObject,
    mut v_k_1695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1696_: *mut LeanObject = core::ptr::null_mut();
    v_res_1696_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1(
            v_j_1694_, v_k_1695_,
        );
    lean_dec_ref(v_k_1695_);
    return v_res_1696_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__4() -> *mut LeanObject {
    let mut v___x_1704_: u8 = 0;
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    v___x_1704_ = 1;
    v___x_1705_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__3;
    v___x_1706_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1705_, v___x_1704_);
    return v___x_1706_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6() -> *mut LeanObject {
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    v___x_1708_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5;
    v___x_1709_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__4,
    );
    v___x_1710_ = lean_string_append(v___x_1709_, v___x_1708_);
    return v___x_1710_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8() -> *mut LeanObject {
    let mut v___x_1713_: u8 = 0;
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    v___x_1713_ = 1;
    v___x_1714_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__7;
    v___x_1715_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1714_, v___x_1713_);
    return v___x_1715_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__9() -> *mut LeanObject {
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    v___x_1716_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8_once),
        _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8,
    );
    v___x_1717_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6,
    );
    v___x_1718_ = lean_string_append(v___x_1717_, v___x_1716_);
    return v___x_1718_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__11() -> *mut LeanObject {
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    v___x_1720_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10;
    v___x_1721_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__9_once),
        _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__9,
    );
    v___x_1722_ = lean_string_append(v___x_1721_, v___x_1720_);
    return v___x_1722_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14() -> *mut LeanObject {
    let mut v___x_1726_: u8 = 0;
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    v___x_1726_ = 1;
    v___x_1727_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__13;
    v___x_1728_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1727_, v___x_1726_);
    return v___x_1728_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__15() -> *mut LeanObject {
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    v___x_1729_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14_once),
        _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14,
    );
    v___x_1730_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__6,
    );
    v___x_1731_ = lean_string_append(v___x_1730_, v___x_1729_);
    return v___x_1731_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__16() -> *mut LeanObject {
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    v___x_1732_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10;
    v___x_1733_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__15_once),
        _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__15,
    );
    v___x_1734_ = lean_string_append(v___x_1733_, v___x_1732_);
    return v___x_1734_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonClientInfo_fromJson(
    mut v_json_1735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1741_: u8 = 0;
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1747_: u8 = 0;
    let mut v_a_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1751_: u8 = 0;
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1755_: u8 = 0;
    let mut v_a_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1762_: u8 = 0;
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1768_: u8 = 0;
    let mut v_a_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1772_: u8 = 0;
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1776_: u8 = 0;
    let mut v_a_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1780_: u8 = 0;
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1785_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1736_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0;
                lean_inc(v_json_1735_);
                v___x_1737_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__0(v_json_1735_, v___x_1736_);
                if lean_obj_tag(v___x_1737_) == 0 {
                    lean_dec(v_json_1735_);
                    v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
                    v_isSharedCheck_1747_ = (!lean_is_exclusive(v___x_1737_)) as u8;
                    if v_isSharedCheck_1747_ == 0 {
                        v___x_1740_ = v___x_1737_;
                        v_isShared_1741_ = v_isSharedCheck_1747_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1738_);
                        lean_dec(v___x_1737_);
                        v___x_1740_ = lean_box(0);
                        v_isShared_1741_ = v_isSharedCheck_1747_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_1737_) == 0 {
                        lean_dec(v_json_1735_);
                        v_a_1748_ = lean_ctor_get(v___x_1737_, 0);
                        v_isSharedCheck_1755_ = (!lean_is_exclusive(v___x_1737_)) as u8;
                        if v_isSharedCheck_1755_ == 0 {
                            v___x_1750_ = v___x_1737_;
                            v_isShared_1751_ = v_isSharedCheck_1755_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1748_);
                            lean_dec(v___x_1737_);
                            v___x_1750_ = lean_box(0);
                            v_isShared_1751_ = v_isSharedCheck_1755_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1756_ = lean_ctor_get(v___x_1737_, 0);
                        lean_inc(v_a_1756_);
                        lean_dec_ref_known(v___x_1737_, 1);
                        v___x_1757_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1;
                        v___x_1758_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1(v_json_1735_, v___x_1757_);
                        if lean_obj_tag(v___x_1758_) == 0 {
                            lean_dec(v_a_1756_);
                            v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
                            v_isSharedCheck_1768_ = (!lean_is_exclusive(v___x_1758_)) as u8;
                            if v_isSharedCheck_1768_ == 0 {
                                v___x_1761_ = v___x_1758_;
                                v_isShared_1762_ = v_isSharedCheck_1768_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_1759_);
                                lean_dec(v___x_1758_);
                                v___x_1761_ = lean_box(0);
                                v_isShared_1762_ = v_isSharedCheck_1768_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_1758_) == 0 {
                                lean_dec(v_a_1756_);
                                v_a_1769_ = lean_ctor_get(v___x_1758_, 0);
                                v_isSharedCheck_1776_ = (!lean_is_exclusive(v___x_1758_)) as u8;
                                if v_isSharedCheck_1776_ == 0 {
                                    v___x_1771_ = v___x_1758_;
                                    v_isShared_1772_ = v_isSharedCheck_1776_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_1769_);
                                    lean_dec(v___x_1758_);
                                    v___x_1771_ = lean_box(0);
                                    v_isShared_1772_ = v_isSharedCheck_1776_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_1777_ = lean_ctor_get(v___x_1758_, 0);
                                v_isSharedCheck_1785_ = (!lean_is_exclusive(v___x_1758_)) as u8;
                                if v_isSharedCheck_1785_ == 0 {
                                    v___x_1779_ = v___x_1758_;
                                    v_isShared_1780_ = v_isSharedCheck_1785_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_1777_);
                                    lean_dec(v___x_1758_);
                                    v___x_1779_ = lean_box(0);
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
                v___x_1742_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__11_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__11,
                );
                v___x_1743_ = lean_string_append(v___x_1742_, v_a_1738_);
                lean_dec(v_a_1738_);
                if v_isShared_1741_ == 0 {
                    lean_ctor_set(v___x_1740_, 0, v___x_1743_);
                    v___x_1745_ = v___x_1740_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
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
                    lean_ctor_set_tag(v___x_1750_, 0);
                    v___x_1753_ = v___x_1750_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
                    v___x_1753_ = v_reuseFailAlloc_1754_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1753_;
            }
            5 => {
                v___x_1763_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__16
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__16_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__16,
                );
                v___x_1764_ = lean_string_append(v___x_1763_, v_a_1759_);
                lean_dec(v_a_1759_);
                if v_isShared_1762_ == 0 {
                    lean_ctor_set(v___x_1761_, 0, v___x_1764_);
                    v___x_1766_ = v___x_1761_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
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
                    lean_ctor_set_tag(v___x_1771_, 0);
                    v___x_1774_ = v___x_1771_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
                    v___x_1774_ = v_reuseFailAlloc_1775_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1774_;
            }
            9 => {
                v___x_1781_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1781_, 0, v_a_1756_);
                lean_ctor_set(v___x_1781_, 1, v_a_1777_);
                if v_isShared_1780_ == 0 {
                    lean_ctor_set(v___x_1779_, 0, v___x_1781_);
                    v___x_1783_ = v___x_1779_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1781_);
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
pub unsafe fn l_Lean_Lsp_Trace_ctorIdx(mut v_x_1788_: u8) -> *mut LeanObject {
    match v_x_1788_ {
        0 => {
            let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
            v___x_1789_ = lean_unsigned_to_nat(0);
            return v___x_1789_;
        }
        1 => {
            let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
            v___x_1790_ = lean_unsigned_to_nat(1);
            return v___x_1790_;
        }
        _ => {
            let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
            v___x_1791_ = lean_unsigned_to_nat(2);
            return v___x_1791_;
        }
    }
}
pub unsafe fn l_Lean_Lsp_Trace_ctorIdx___boxed(mut v_x_1792_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_1793_: u8 = 0;
    let mut v_res_1794_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_1793_ = (lean_unbox(v_x_1792_) as u8);
    v_res_1794_ = l_Lean_Lsp_Trace_ctorIdx(v_x_boxed_1793_);
    return v_res_1794_;
}
pub unsafe fn l_Lean_Lsp_Trace_toCtorIdx(mut v_x_1795_: u8) -> *mut LeanObject {
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    v___x_1796_ = l_Lean_Lsp_Trace_ctorIdx(v_x_1795_);
    return v___x_1796_;
}
pub unsafe fn l_Lean_Lsp_Trace_toCtorIdx___boxed(
    mut v_x_1797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_1798_: u8 = 0;
    let mut v_res_1799_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1798_ = (lean_unbox(v_x_1797_) as u8);
    v_res_1799_ = l_Lean_Lsp_Trace_toCtorIdx(v_x_4__boxed_1798_);
    return v_res_1799_;
}
pub unsafe fn l_Lean_Lsp_Trace_ctorElim___redArg(
    mut v_k_1800_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_1800_);
    return v_k_1800_;
}
pub unsafe fn l_Lean_Lsp_Trace_ctorElim___redArg___boxed(
    mut v_k_1801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1802_: *mut LeanObject = core::ptr::null_mut();
    v_res_1802_ = l_Lean_Lsp_Trace_ctorElim___redArg(v_k_1801_);
    lean_dec(v_k_1801_);
    return v_res_1802_;
}
pub unsafe fn l_Lean_Lsp_Trace_ctorElim(
    mut v_motive_1803_: *mut LeanObject,
    mut v_ctorIdx_1804_: *mut LeanObject,
    mut v_t_1805_: u8,
    mut v_h_1806_: *mut LeanObject,
    mut v_k_1807_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_1807_);
    return v_k_1807_;
}
pub unsafe fn l_Lean_Lsp_Trace_ctorElim___boxed(
    mut v_motive_1808_: *mut LeanObject,
    mut v_ctorIdx_1809_: *mut LeanObject,
    mut v_t_1810_: *mut LeanObject,
    mut v_h_1811_: *mut LeanObject,
    mut v_k_1812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1813_: u8 = 0;
    let mut v_res_1814_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1813_ = (lean_unbox(v_t_1810_) as u8);
    v_res_1814_ = l_Lean_Lsp_Trace_ctorElim(
        v_motive_1808_,
        v_ctorIdx_1809_,
        v_t_boxed_1813_,
        v_h_1811_,
        v_k_1812_,
    );
    lean_dec(v_k_1812_);
    lean_dec(v_ctorIdx_1809_);
    return v_res_1814_;
}
pub unsafe fn l_Lean_Lsp_Trace_off_elim___redArg(
    mut v_off_1815_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_off_1815_);
    return v_off_1815_;
}
pub unsafe fn l_Lean_Lsp_Trace_off_elim___redArg___boxed(
    mut v_off_1816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1817_: *mut LeanObject = core::ptr::null_mut();
    v_res_1817_ = l_Lean_Lsp_Trace_off_elim___redArg(v_off_1816_);
    lean_dec(v_off_1816_);
    return v_res_1817_;
}
pub unsafe fn l_Lean_Lsp_Trace_off_elim(
    mut v_motive_1818_: *mut LeanObject,
    mut v_t_1819_: u8,
    mut v_h_1820_: *mut LeanObject,
    mut v_off_1821_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_off_1821_);
    return v_off_1821_;
}
pub unsafe fn l_Lean_Lsp_Trace_off_elim___boxed(
    mut v_motive_1822_: *mut LeanObject,
    mut v_t_1823_: *mut LeanObject,
    mut v_h_1824_: *mut LeanObject,
    mut v_off_1825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1826_: u8 = 0;
    let mut v_res_1827_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1826_ = (lean_unbox(v_t_1823_) as u8);
    v_res_1827_ =
        l_Lean_Lsp_Trace_off_elim(v_motive_1822_, v_t_boxed_1826_, v_h_1824_, v_off_1825_);
    lean_dec(v_off_1825_);
    return v_res_1827_;
}
pub unsafe fn l_Lean_Lsp_Trace_messages_elim___redArg(
    mut v_messages_1828_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_messages_1828_);
    return v_messages_1828_;
}
pub unsafe fn l_Lean_Lsp_Trace_messages_elim___redArg___boxed(
    mut v_messages_1829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1830_: *mut LeanObject = core::ptr::null_mut();
    v_res_1830_ = l_Lean_Lsp_Trace_messages_elim___redArg(v_messages_1829_);
    lean_dec(v_messages_1829_);
    return v_res_1830_;
}
pub unsafe fn l_Lean_Lsp_Trace_messages_elim(
    mut v_motive_1831_: *mut LeanObject,
    mut v_t_1832_: u8,
    mut v_h_1833_: *mut LeanObject,
    mut v_messages_1834_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_messages_1834_);
    return v_messages_1834_;
}
pub unsafe fn l_Lean_Lsp_Trace_messages_elim___boxed(
    mut v_motive_1835_: *mut LeanObject,
    mut v_t_1836_: *mut LeanObject,
    mut v_h_1837_: *mut LeanObject,
    mut v_messages_1838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1839_: u8 = 0;
    let mut v_res_1840_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1839_ = (lean_unbox(v_t_1836_) as u8);
    v_res_1840_ = l_Lean_Lsp_Trace_messages_elim(
        v_motive_1835_,
        v_t_boxed_1839_,
        v_h_1837_,
        v_messages_1838_,
    );
    lean_dec(v_messages_1838_);
    return v_res_1840_;
}
pub unsafe fn l_Lean_Lsp_Trace_verbose_elim___redArg(
    mut v_verbose_1841_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_verbose_1841_);
    return v_verbose_1841_;
}
pub unsafe fn l_Lean_Lsp_Trace_verbose_elim___redArg___boxed(
    mut v_verbose_1842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1843_: *mut LeanObject = core::ptr::null_mut();
    v_res_1843_ = l_Lean_Lsp_Trace_verbose_elim___redArg(v_verbose_1842_);
    lean_dec(v_verbose_1842_);
    return v_res_1843_;
}
pub unsafe fn l_Lean_Lsp_Trace_verbose_elim(
    mut v_motive_1844_: *mut LeanObject,
    mut v_t_1845_: u8,
    mut v_h_1846_: *mut LeanObject,
    mut v_verbose_1847_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_verbose_1847_);
    return v_verbose_1847_;
}
pub unsafe fn l_Lean_Lsp_Trace_verbose_elim___boxed(
    mut v_motive_1848_: *mut LeanObject,
    mut v_t_1849_: *mut LeanObject,
    mut v_h_1850_: *mut LeanObject,
    mut v_verbose_1851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1852_: u8 = 0;
    let mut v_res_1853_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1852_ = (lean_unbox(v_t_1849_) as u8);
    v_res_1853_ =
        l_Lean_Lsp_Trace_verbose_elim(v_motive_1848_, v_t_boxed_1852_, v_h_1850_, v_verbose_1851_);
    lean_dec(v_verbose_1851_);
    return v_res_1853_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonTrace___lam__0(
    mut v_j_1869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: u8 = 0;
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: u8 = 0;
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: u8 = 0;
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1872_ = l_Lean_Json_getStr_x3f(v_j_1869_);
                if lean_obj_tag(v___x_1872_) == 1 {
                    v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
                    lean_inc(v_a_1873_);
                    lean_dec_ref_known(v___x_1872_, 1);
                    v___x_1874_ = l_Lean_Lsp_instFromJsonTrace___lam__0___closed__2;
                    v___x_1875_ = lean_string_dec_eq(v_a_1873_, v___x_1874_);
                    if v___x_1875_ == 0 {
                        v___x_1876_ = l_Lean_Lsp_instFromJsonTrace___lam__0___closed__3;
                        v___x_1877_ = lean_string_dec_eq(v_a_1873_, v___x_1876_);
                        if v___x_1877_ == 0 {
                            v___x_1878_ = l_Lean_Lsp_instFromJsonTrace___lam__0___closed__4;
                            v___x_1879_ = lean_string_dec_eq(v_a_1873_, v___x_1878_);
                            lean_dec(v_a_1873_);
                            if v___x_1879_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                v___x_1880_ = l_Lean_Lsp_instFromJsonTrace___lam__0___closed__5;
                                return v___x_1880_;
                            }
                        } else {
                            lean_dec(v_a_1873_);
                            v___x_1881_ = l_Lean_Lsp_instFromJsonTrace___lam__0___closed__6;
                            return v___x_1881_;
                        }
                    } else {
                        lean_dec(v_a_1873_);
                        v___x_1882_ = l_Lean_Lsp_instFromJsonTrace___lam__0___closed__7;
                        return v___x_1882_;
                    }
                } else {
                    lean_dec_ref(v___x_1872_);
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
pub unsafe fn l_Lean_Lsp_Trace_hasToJson___lam__0(mut v_x_1891_: u8) -> *mut LeanObject {
    match v_x_1891_ {
        0 => {
            let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
            v___x_1892_ = l_Lean_Lsp_Trace_hasToJson___lam__0___closed__0;
            return v___x_1892_;
        }
        1 => {
            let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
            v___x_1893_ = l_Lean_Lsp_Trace_hasToJson___lam__0___closed__1;
            return v___x_1893_;
        }
        _ => {
            let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
            v___x_1894_ = l_Lean_Lsp_Trace_hasToJson___lam__0___closed__2;
            return v___x_1894_;
        }
    }
}
pub unsafe fn l_Lean_Lsp_Trace_hasToJson___lam__0___boxed(
    mut v_x_1895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_54__boxed_1896_: u8 = 0;
    let mut v_res_1897_: *mut LeanObject = core::ptr::null_mut();
    v_x_54__boxed_1896_ = (lean_unbox(v_x_1895_) as u8);
    v_res_1897_ = l_Lean_Lsp_Trace_hasToJson___lam__0(v_x_54__boxed_1896_);
    return v_res_1897_;
}
pub unsafe fn l_Lean_Lsp_instToJsonHashSet___redArg___lam__0(
    mut v_x1_1900_: *mut LeanObject,
    mut v_x2_1901_: *mut LeanObject,
    mut v_x3_1902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    v___x_1903_ = lean_array_push(v_x1_1900_, v_x2_1901_);
    return v___x_1903_;
}
pub unsafe fn l_Lean_Lsp_instToJsonHashSet___redArg___lam__1(
    mut v_inst_1904_: *mut LeanObject,
    mut v_x_1905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    v___x_1906_ = lean_apply_1(v_inst_1904_, v_x_1905_);
    return v___x_1906_;
}
pub unsafe fn l_Lean_Lsp_instToJsonHashSet___redArg___lam__2(
    mut v___x_1907_: *mut LeanObject,
    mut v___f_1908_: *mut LeanObject,
    mut v_acc_1909_: *mut LeanObject,
    mut v_l_1910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    v___x_1911_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_1907_,
        v___f_1908_,
        v_acc_1909_,
        v_l_1910_,
    );
    return v___x_1911_;
}
pub unsafe fn l_Lean_Lsp_instToJsonHashSet___redArg___lam__3(
    mut v___f_1931_: *mut LeanObject,
    mut v___f_1932_: *mut LeanObject,
    mut v_s_1933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1937_: usize = 0;
    let mut v___x_1938_: usize = 0;
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: u8 = 0;
    let mut v___f_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: u8 = 0;
    let mut v___x_1950_: usize = 0;
    let mut v___x_1951_: usize = 0;
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: usize = 0;
    let mut v___x_1954_: usize = 0;
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1941_ = lean_ctor_get(v_s_1933_, 0);
                lean_inc(v_size_1941_);
                v_buckets_1942_ = lean_ctor_get(v_s_1933_, 1);
                lean_inc_ref(v_buckets_1942_);
                lean_dec_ref(v_s_1933_);
                v___x_1943_ = lean_mk_empty_array_with_capacity(v_size_1941_);
                lean_dec(v_size_1941_);
                v___x_1944_ = l_Lean_Lsp_instToJsonHashSet___redArg___lam__3___closed__9;
                v___x_1945_ = lean_unsigned_to_nat(0);
                v___x_1946_ = lean_array_get_size(v_buckets_1942_);
                v___x_1947_ = lean_nat_dec_lt(v___x_1945_, v___x_1946_);
                if v___x_1947_ == 0 {
                    lean_dec_ref(v_buckets_1942_);
                    lean_dec_ref(v___f_1932_);
                    v___y_1935_ = v___x_1943_;
                    state = 1;
                    continue;
                } else {
                    v___f_1948_ = lean_alloc_closure(
                        l_Lean_Lsp_instToJsonHashSet___redArg___lam__2 as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    lean_closure_set(v___f_1948_, 0, v___x_1944_);
                    lean_closure_set(v___f_1948_, 1, v___f_1932_);
                    v___x_1949_ = lean_nat_dec_le(v___x_1946_, v___x_1946_);
                    if v___x_1949_ == 0 {
                        if v___x_1947_ == 0 {
                            lean_dec_ref(v___f_1948_);
                            lean_dec_ref(v_buckets_1942_);
                            v___y_1935_ = v___x_1943_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1950_ = 0usize;
                            v___x_1951_ = lean_usize_of_nat(v___x_1946_);
                            v___x_1952_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
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
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
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
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_1936_,
                    v___f_1931_,
                    v_sz_1937_,
                    v___x_1938_,
                    v___y_1935_,
                );
                v___x_1940_ = lean_alloc_ctor(4, 1, (0) as u32);
                lean_ctor_set(v___x_1940_, 0, v___x_1939_);
                return v___x_1940_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonHashSet___redArg(
    mut v_inst_1957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1960_: *mut LeanObject = core::ptr::null_mut();
    v___f_1958_ = l_Lean_Lsp_instToJsonHashSet___redArg___closed__0;
    v___f_1959_ = lean_alloc_closure(
        l_Lean_Lsp_instToJsonHashSet___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1959_, 0, v_inst_1957_);
    v___f_1960_ = lean_alloc_closure(
        l_Lean_Lsp_instToJsonHashSet___redArg___lam__3 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1960_, 0, v___f_1959_);
    lean_closure_set(v___f_1960_, 1, v___f_1958_);
    return v___f_1960_;
}
pub unsafe fn l_Lean_Lsp_instToJsonHashSet(
    mut v_00_u03b1_1961_: *mut LeanObject,
    mut v_inst_1962_: *mut LeanObject,
    mut v_inst_1963_: *mut LeanObject,
    mut v_inst_1964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    v___x_1965_ = l_Lean_Lsp_instToJsonHashSet___redArg(v_inst_1964_);
    return v___x_1965_;
}
pub unsafe fn l_Lean_Lsp_instToJsonHashSet___boxed(
    mut v_00_u03b1_1966_: *mut LeanObject,
    mut v_inst_1967_: *mut LeanObject,
    mut v_inst_1968_: *mut LeanObject,
    mut v_inst_1969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1970_: *mut LeanObject = core::ptr::null_mut();
    v_res_1970_ =
        l_Lean_Lsp_instToJsonHashSet(v_00_u03b1_1966_, v_inst_1967_, v_inst_1968_, v_inst_1969_);
    lean_dec_ref(v_inst_1968_);
    lean_dec_ref(v_inst_1967_);
    return v_res_1970_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2() -> *mut LeanObject
{
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    v___x_1975_ = lean_box(0);
    v___x_1976_ = lean_unsigned_to_nat(16);
    v___x_1977_ = lean_mk_array(v___x_1976_, v___x_1975_);
    return v___x_1977_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__3() -> *mut LeanObject
{
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    v___x_1978_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2_once),
        _init_l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0___closed__2,
    );
    v___x_1979_ = lean_unsigned_to_nat(0);
    v___x_1980_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1980_, 0, v___x_1979_);
    lean_ctor_set(v___x_1980_, 1, v___x_1978_);
    return v___x_1980_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0(
    mut v___x_1984_: *mut LeanObject,
    mut v_inst_1985_: *mut LeanObject,
    mut v_inst_1986_: *mut LeanObject,
    mut v_inst_1987_: *mut LeanObject,
    mut v_x_1988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_elems_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1990_: usize = 0;
    let mut v___x_1991_: usize = 0;
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1996_: u8 = 0;
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2000_: u8 = 0;
    let mut v_a_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2004_: u8 = 0;
    let mut v___f_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2011_: u8 = 0;
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1988_) == 4 {
                    v_elems_1989_ = lean_ctor_get(v_x_1988_, 0);
                    lean_inc_ref(v_elems_1989_);
                    lean_dec_ref_known(v_x_1988_, 1);
                    v_sz_1990_ = lean_array_size(v_elems_1989_);
                    v___x_1991_ = 0usize;
                    v___x_1992_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
                        v___x_1984_,
                        v_inst_1985_,
                        v_sz_1990_,
                        v___x_1991_,
                        v_elems_1989_,
                    );
                    if lean_obj_tag(v___x_1992_) == 0 {
                        lean_dec_ref(v_inst_1987_);
                        lean_dec_ref(v_inst_1986_);
                        v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
                        v_isSharedCheck_2000_ = (!lean_is_exclusive(v___x_1992_)) as u8;
                        if v_isSharedCheck_2000_ == 0 {
                            v___x_1995_ = v___x_1992_;
                            v_isShared_1996_ = v_isSharedCheck_2000_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1993_);
                            lean_dec(v___x_1992_);
                            v___x_1995_ = lean_box(0);
                            v_isShared_1996_ = v_isSharedCheck_2000_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2001_ = lean_ctor_get(v___x_1992_, 0);
                        v_isSharedCheck_2011_ = (!lean_is_exclusive(v___x_1992_)) as u8;
                        if v_isSharedCheck_2011_ == 0 {
                            v___x_2003_ = v___x_1992_;
                            v_isShared_2004_ = v_isSharedCheck_2011_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2001_);
                            lean_dec(v___x_1992_);
                            v___x_2003_ = lean_box(0);
                            v_isShared_2004_ = v_isSharedCheck_2011_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_x_1988_);
                    lean_dec_ref(v_inst_1987_);
                    lean_dec_ref(v_inst_1986_);
                    lean_dec_ref(v_inst_1985_);
                    lean_dec_ref(v___x_1984_);
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
                    v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
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
                v___x_2006_ = lean_obj_once(
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
                    lean_ctor_set(v___x_2003_, 0, v___x_2007_);
                    v___x_2009_ = v___x_2003_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2007_);
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
    mut v_inst_2032_: *mut LeanObject,
    mut v_inst_2033_: *mut LeanObject,
    mut v_inst_2034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2036_: *mut LeanObject = core::ptr::null_mut();
    v___x_2035_ = l_Lean_Lsp_instFromJsonHashSet___redArg___closed__9;
    v___f_2036_ = lean_alloc_closure(
        l_Lean_Lsp_instFromJsonHashSet___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2036_, 0, v___x_2035_);
    lean_closure_set(v___f_2036_, 1, v_inst_2034_);
    lean_closure_set(v___f_2036_, 2, v_inst_2032_);
    lean_closure_set(v___f_2036_, 3, v_inst_2033_);
    return v___f_2036_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonHashSet(
    mut v_00_u03b1_2037_: *mut LeanObject,
    mut v_inst_2038_: *mut LeanObject,
    mut v_inst_2039_: *mut LeanObject,
    mut v_inst_2040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    v___x_2041_ = l_Lean_Lsp_instFromJsonHashSet___redArg(v_inst_2038_, v_inst_2039_, v_inst_2040_);
    return v___x_2041_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0_spec__0(
    mut v_x_2042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2048_: u8 = 0;
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2052_: u8 = 0;
    let mut v_a_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2056_: u8 = 0;
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2061_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2042_) == 0 {
                    v___x_2043_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1_spec__1___closed__0;
                    return v___x_2043_;
                } else {
                    v___x_2044_ = l_Lean_Json_getStr_x3f(v_x_2042_);
                    if lean_obj_tag(v___x_2044_) == 0 {
                        v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
                        v_isSharedCheck_2052_ = (!lean_is_exclusive(v___x_2044_)) as u8;
                        if v_isSharedCheck_2052_ == 0 {
                            v___x_2047_ = v___x_2044_;
                            v_isShared_2048_ = v_isSharedCheck_2052_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2045_);
                            lean_dec(v___x_2044_);
                            v___x_2047_ = lean_box(0);
                            v_isShared_2048_ = v_isSharedCheck_2052_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2053_ = lean_ctor_get(v___x_2044_, 0);
                        v_isSharedCheck_2061_ = (!lean_is_exclusive(v___x_2044_)) as u8;
                        if v_isSharedCheck_2061_ == 0 {
                            v___x_2055_ = v___x_2044_;
                            v_isShared_2056_ = v_isSharedCheck_2061_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2053_);
                            lean_dec(v___x_2044_);
                            v___x_2055_ = lean_box(0);
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
                    v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
                    v___x_2050_ = v_reuseFailAlloc_2051_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2050_;
            }
            3 => {
                v___x_2057_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2057_, 0, v_a_2053_);
                if v_isShared_2056_ == 0 {
                    lean_ctor_set(v___x_2055_, 0, v___x_2057_);
                    v___x_2059_ = v___x_2055_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2057_);
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
    mut v_j_2062_: *mut LeanObject,
    mut v_k_2063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    v___x_2064_ = l_Lean_Json_getObjValD(v_j_2062_, v_k_2063_);
    v___x_2065_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0_spec__0(v___x_2064_);
    return v___x_2065_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0___boxed(
    mut v_j_2066_: *mut LeanObject,
    mut v_k_2067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2068_: *mut LeanObject = core::ptr::null_mut();
    v_res_2068_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0(
            v_j_2066_, v_k_2067_,
        );
    lean_dec_ref(v_k_2067_);
    return v_res_2068_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3(
    mut v_sz_2069_: usize,
    mut v_i_2070_: usize,
    mut v_bs_2071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2072_: u8 = 0;
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2079_: u8 = 0;
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2083_: u8 = 0;
    let mut v_a_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: usize = 0;
    let mut v___x_2088_: usize = 0;
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2072_ = lean_usize_dec_lt(v_i_2070_, v_sz_2069_);
                if v___x_2072_ == 0 {
                    v___x_2073_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2073_, 0, v_bs_2071_);
                    return v___x_2073_;
                } else {
                    v_v_2074_ = lean_array_uget_borrowed(v_bs_2071_, v_i_2070_);
                    lean_inc(v_v_2074_);
                    v___x_2075_ = l_Lean_Json_getStr_x3f(v_v_2074_);
                    if lean_obj_tag(v___x_2075_) == 0 {
                        lean_dec_ref(v_bs_2071_);
                        v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
                        v_isSharedCheck_2083_ = (!lean_is_exclusive(v___x_2075_)) as u8;
                        if v_isSharedCheck_2083_ == 0 {
                            v___x_2078_ = v___x_2075_;
                            v_isShared_2079_ = v_isSharedCheck_2083_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2076_);
                            lean_dec(v___x_2075_);
                            v___x_2078_ = lean_box(0);
                            v_isShared_2079_ = v_isSharedCheck_2083_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2084_ = lean_ctor_get(v___x_2075_, 0);
                        lean_inc(v_a_2084_);
                        lean_dec_ref_known(v___x_2075_, 1);
                        v___x_2085_ = lean_unsigned_to_nat(0);
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
                    v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
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
    mut v_sz_2091_: *mut LeanObject,
    mut v_i_2092_: *mut LeanObject,
    mut v_bs_2093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2094_: usize = 0;
    let mut v_i_boxed_2095_: usize = 0;
    let mut v_res_2096_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2094_ = lean_unbox_usize(v_sz_2091_);
    lean_dec(v_sz_2091_);
    v_i_boxed_2095_ = lean_unbox_usize(v_i_2092_);
    lean_dec(v_i_2092_);
    v_res_2096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3(v_sz_boxed_2094_, v_i_boxed_2095_, v_bs_2093_);
    return v_res_2096_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10___redArg(
    mut v_x_2097_: *mut LeanObject,
    mut v_x_2098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2104_: u8 = 0;
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2124_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2098_) == 0 {
                    return v_x_2097_;
                } else {
                    v_key_2099_ = lean_ctor_get(v_x_2098_, 0);
                    v_value_2100_ = lean_ctor_get(v_x_2098_, 1);
                    v_tail_2101_ = lean_ctor_get(v_x_2098_, 2);
                    v_isSharedCheck_2124_ = (!lean_is_exclusive(v_x_2098_)) as u8;
                    if v_isSharedCheck_2124_ == 0 {
                        v___x_2103_ = v_x_2098_;
                        v_isShared_2104_ = v_isSharedCheck_2124_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2101_);
                        lean_inc(v_value_2100_);
                        lean_inc(v_key_2099_);
                        lean_dec(v_x_2098_);
                        v___x_2103_ = lean_box(0);
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
                lean_inc(v___x_2118_);
                if v_isShared_2104_ == 0 {
                    lean_ctor_set(v___x_2103_, 2, v___x_2118_);
                    v___x_2120_ = v___x_2103_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_key_2099_);
                    lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_value_2100_);
                    lean_ctor_set(v_reuseFailAlloc_2123_, 2, v___x_2118_);
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
    mut v_i_2125_: *mut LeanObject,
    mut v_source_2126_: *mut LeanObject,
    mut v_target_2127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: u8 = 0;
    let mut v_es_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2128_ = lean_array_get_size(v_source_2126_);
                v___x_2129_ = lean_nat_dec_lt(v_i_2125_, v___x_2128_);
                if v___x_2129_ == 0 {
                    lean_dec_ref(v_source_2126_);
                    lean_dec(v_i_2125_);
                    return v_target_2127_;
                } else {
                    v_es_2130_ = lean_array_fget(v_source_2126_, v_i_2125_);
                    v___x_2131_ = lean_box(0);
                    v_source_2132_ = lean_array_fset(v_source_2126_, v_i_2125_, v___x_2131_);
                    v_target_2133_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10___redArg(v_target_2127_, v_es_2130_);
                    v___x_2134_ = lean_unsigned_to_nat(1);
                    v___x_2135_ = lean_nat_add(v_i_2125_, v___x_2134_);
                    lean_dec(v_i_2125_);
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
    mut v_data_2137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    v___x_2138_ = lean_array_get_size(v_data_2137_);
    v___x_2139_ = lean_unsigned_to_nat(2);
    v_nbuckets_2140_ = lean_nat_mul(v___x_2138_, v___x_2139_);
    v___x_2141_ = lean_unsigned_to_nat(0);
    v___x_2142_ = lean_box(0);
    v___x_2143_ = lean_mk_array(v_nbuckets_2140_, v___x_2142_);
    v___x_2144_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8___redArg(v___x_2141_, v_data_2137_, v___x_2143_);
    return v___x_2144_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(
    mut v_a_2145_: *mut LeanObject,
    mut v_x_2146_: *mut LeanObject,
) -> u8 {
    let mut v___x_2147_: u8 = 0;
    let mut v_key_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2146_) == 0 {
                    v___x_2147_ = 0;
                    return v___x_2147_;
                } else {
                    v_key_2148_ = lean_ctor_get(v_x_2146_, 0);
                    v_tail_2149_ = lean_ctor_get(v_x_2146_, 2);
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
    mut v_a_2152_: *mut LeanObject,
    mut v_x_2153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2154_: u8 = 0;
    let mut v_r_2155_: *mut LeanObject = core::ptr::null_mut();
    v_res_2154_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_a_2152_, v_x_2153_);
    lean_dec(v_x_2153_);
    lean_dec_ref(v_a_2152_);
    v_r_2155_ = lean_box((v_res_2154_) as usize);
    return v_r_2155_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(
    mut v_m_2156_: *mut LeanObject,
    mut v_a_2157_: *mut LeanObject,
    mut v_b_2158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: u8 = 0;
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2178_: u8 = 0;
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: u8 = 0;
    let mut v_val_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2196_: u8 = 0;
    let mut v_unused_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2159_ = lean_ctor_get(v_m_2156_, 0);
                v_buckets_2160_ = lean_ctor_get(v_m_2156_, 1);
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
                    lean_inc_ref(v_buckets_2160_);
                    lean_inc(v_size_2159_);
                    v_isSharedCheck_2196_ = (!lean_is_exclusive(v_m_2156_)) as u8;
                    if v_isSharedCheck_2196_ == 0 {
                        v_unused_2197_ = lean_ctor_get(v_m_2156_, 1);
                        lean_dec(v_unused_2197_);
                        v_unused_2198_ = lean_ctor_get(v_m_2156_, 0);
                        lean_dec(v_unused_2198_);
                        v___x_2177_ = v_m_2156_;
                        v_isShared_2178_ = v_isSharedCheck_2196_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_2156_);
                        v___x_2177_ = lean_box(0);
                        v_isShared_2178_ = v_isSharedCheck_2196_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_2158_);
                    lean_dec_ref(v_a_2157_);
                    return v_m_2156_;
                }
            }
            1 => {
                v___x_2179_ = lean_unsigned_to_nat(1);
                v_size_x27_2180_ = lean_nat_add(v_size_2159_, v___x_2179_);
                lean_dec(v_size_2159_);
                lean_inc(v_bkt_2174_);
                v___x_2181_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2181_, 0, v_a_2157_);
                lean_ctor_set(v___x_2181_, 1, v_b_2158_);
                lean_ctor_set(v___x_2181_, 2, v_bkt_2174_);
                v_buckets_x27_2182_ = lean_array_uset(v_buckets_2160_, v___x_2173_, v___x_2181_);
                v___x_2183_ = lean_unsigned_to_nat(4);
                v___x_2184_ = lean_nat_mul(v_size_x27_2180_, v___x_2183_);
                v___x_2185_ = lean_unsigned_to_nat(3);
                v___x_2186_ = lean_nat_div(v___x_2184_, v___x_2185_);
                lean_dec(v___x_2184_);
                v___x_2187_ = lean_array_get_size(v_buckets_x27_2182_);
                v___x_2188_ = lean_nat_dec_le(v___x_2186_, v___x_2187_);
                lean_dec(v___x_2186_);
                if v___x_2188_ == 0 {
                    v_val_2189_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7___redArg(v_buckets_x27_2182_);
                    if v_isShared_2178_ == 0 {
                        lean_ctor_set(v___x_2177_, 1, v_val_2189_);
                        lean_ctor_set(v___x_2177_, 0, v_size_x27_2180_);
                        v___x_2191_ = v___x_2177_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_size_x27_2180_);
                        lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_val_2189_);
                        v___x_2191_ = v_reuseFailAlloc_2192_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_2178_ == 0 {
                        lean_ctor_set(v___x_2177_, 1, v_buckets_x27_2182_);
                        lean_ctor_set(v___x_2177_, 0, v_size_x27_2180_);
                        v___x_2194_ = v___x_2177_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_size_x27_2180_);
                        lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_buckets_x27_2182_);
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
    mut v_as_2199_: *mut LeanObject,
    mut v_sz_2200_: usize,
    mut v_i_2201_: usize,
    mut v_b_2202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2203_: u8 = 0;
    let mut v_a_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2206_: *mut LeanObject = core::ptr::null_mut();
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
                    v___x_2205_ = lean_box(0);
                    lean_inc(v_a_2204_);
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
    mut v_as_2210_: *mut LeanObject,
    mut v_sz_2211_: *mut LeanObject,
    mut v_i_2212_: *mut LeanObject,
    mut v_b_2213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2214_: usize = 0;
    let mut v_i_boxed_2215_: usize = 0;
    let mut v_res_2216_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2214_ = lean_unbox_usize(v_sz_2211_);
    lean_dec(v_sz_2211_);
    v_i_boxed_2215_ = lean_unbox_usize(v_i_2212_);
    lean_dec(v_i_2212_);
    v_res_2216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6(v_as_2210_, v_sz_boxed_2214_, v_i_boxed_2215_, v_b_2213_);
    lean_dec_ref(v_as_2210_);
    return v_res_2216_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4(
    mut v_m_2217_: *mut LeanObject,
    mut v_l_2218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_2219_: usize = 0;
    let mut v___x_2220_: usize = 0;
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    v_sz_2219_ = lean_array_size(v_l_2218_);
    v___x_2220_ = 0usize;
    v___x_2221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__6(v_l_2218_, v_sz_2219_, v___x_2220_, v_m_2217_);
    return v___x_2221_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4___boxed(
    mut v_m_2222_: *mut LeanObject,
    mut v_l_2223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2224_: *mut LeanObject = core::ptr::null_mut();
    v_res_2224_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4(v_m_2222_, v_l_2223_);
    lean_dec_ref(v_l_2223_);
    return v_res_2224_;
}
pub unsafe fn _init_l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1()
-> *mut LeanObject {
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    v___x_2227_ = lean_box(0);
    v___x_2228_ = lean_unsigned_to_nat(16);
    v___x_2229_ = lean_mk_array(v___x_2228_, v___x_2227_);
    return v___x_2229_;
}
pub unsafe fn _init_l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2()
-> *mut LeanObject {
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    v___x_2230_ = lean_obj_once(core::ptr::addr_of_mut!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1_once), _init_l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__1);
    v___x_2231_ = lean_unsigned_to_nat(0);
    v___x_2232_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2232_, 0, v___x_2231_);
    lean_ctor_set(v___x_2232_, 1, v___x_2230_);
    return v___x_2232_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2(
    mut v_x_2235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elems_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2238_: usize = 0;
    let mut v___x_2239_: usize = 0;
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2244_: u8 = 0;
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2248_: u8 = 0;
    let mut v_a_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2252_: u8 = 0;
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2259_: u8 = 0;
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2235_) == 0 {
                    v___x_2236_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__0;
                    return v___x_2236_;
                } else {
                    if lean_obj_tag(v_x_2235_) == 4 {
                        v_elems_2237_ = lean_ctor_get(v_x_2235_, 0);
                        lean_inc_ref(v_elems_2237_);
                        lean_dec_ref_known(v_x_2235_, 1);
                        v_sz_2238_ = lean_array_size(v_elems_2237_);
                        v___x_2239_ = 0usize;
                        v___x_2240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__3(v_sz_2238_, v___x_2239_, v_elems_2237_);
                        if lean_obj_tag(v___x_2240_) == 0 {
                            v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
                            v_isSharedCheck_2248_ = (!lean_is_exclusive(v___x_2240_)) as u8;
                            if v_isSharedCheck_2248_ == 0 {
                                v___x_2243_ = v___x_2240_;
                                v_isShared_2244_ = v_isSharedCheck_2248_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_2241_);
                                lean_dec(v___x_2240_);
                                v___x_2243_ = lean_box(0);
                                v_isShared_2244_ = v_isSharedCheck_2248_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_2249_ = lean_ctor_get(v___x_2240_, 0);
                            v_isSharedCheck_2259_ = (!lean_is_exclusive(v___x_2240_)) as u8;
                            if v_isSharedCheck_2259_ == 0 {
                                v___x_2251_ = v___x_2240_;
                                v_isShared_2252_ = v_isSharedCheck_2259_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_2249_);
                                lean_dec(v___x_2240_);
                                v___x_2251_ = lean_box(0);
                                v_isShared_2252_ = v_isSharedCheck_2259_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_x_2235_);
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
                    v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
                    v___x_2246_ = v_reuseFailAlloc_2247_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2246_;
            }
            3 => {
                v___x_2253_ = lean_obj_once(core::ptr::addr_of_mut!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2_once), _init_l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2___closed__2);
                v___x_2254_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4(v___x_2253_, v_a_2249_);
                lean_dec(v_a_2249_);
                v___x_2255_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2255_, 0, v___x_2254_);
                if v_isShared_2252_ == 0 {
                    lean_ctor_set(v___x_2251_, 0, v___x_2255_);
                    v___x_2257_ = v___x_2251_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2255_);
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
    mut v_j_2261_: *mut LeanObject,
    mut v_k_2262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    v___x_2263_ = l_Lean_Json_getObjValD(v_j_2261_, v_k_2262_);
    v___x_2264_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2(v___x_2263_);
    return v___x_2264_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1___boxed(
    mut v_j_2265_: *mut LeanObject,
    mut v_k_2266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2267_: *mut LeanObject = core::ptr::null_mut();
    v_res_2267_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(
            v_j_2265_, v_k_2266_,
        );
    lean_dec_ref(v_k_2266_);
    return v_res_2267_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3() -> *mut LeanObject {
    let mut v___x_2274_: u8 = 0;
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    v___x_2274_ = 1;
    v___x_2275_ = l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__2;
    v___x_2276_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2275_, v___x_2274_);
    return v___x_2276_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4() -> *mut LeanObject {
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    v___x_2277_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5;
    v___x_2278_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__3,
    );
    v___x_2279_ = lean_string_append(v___x_2278_, v___x_2277_);
    return v___x_2279_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7() -> *mut LeanObject {
    let mut v___x_2283_: u8 = 0;
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    v___x_2283_ = 1;
    v___x_2284_ = l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__6;
    v___x_2285_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2284_, v___x_2283_);
    return v___x_2285_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8() -> *mut LeanObject {
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    v___x_2286_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7_once),
        _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__7,
    );
    v___x_2287_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4,
    );
    v___x_2288_ = lean_string_append(v___x_2287_, v___x_2286_);
    return v___x_2288_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9() -> *mut LeanObject {
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    v___x_2289_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10;
    v___x_2290_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8_once),
        _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__8,
    );
    v___x_2291_ = lean_string_append(v___x_2290_, v___x_2289_);
    return v___x_2291_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13() -> *mut LeanObject {
    let mut v___x_2296_: u8 = 0;
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    v___x_2296_ = 1;
    v___x_2297_ = l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__12;
    v___x_2298_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2297_, v___x_2296_);
    return v___x_2298_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14() -> *mut LeanObject {
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    v___x_2299_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13_once),
        _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__13,
    );
    v___x_2300_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4,
    );
    v___x_2301_ = lean_string_append(v___x_2300_, v___x_2299_);
    return v___x_2301_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15() -> *mut LeanObject {
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    v___x_2302_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10;
    v___x_2303_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14_once),
        _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__14,
    );
    v___x_2304_ = lean_string_append(v___x_2303_, v___x_2302_);
    return v___x_2304_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19() -> *mut LeanObject {
    let mut v___x_2309_: u8 = 0;
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    v___x_2309_ = 1;
    v___x_2310_ = l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__18;
    v___x_2311_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2310_, v___x_2309_);
    return v___x_2311_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20() -> *mut LeanObject {
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    v___x_2312_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19_once),
        _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__19,
    );
    v___x_2313_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__4,
    );
    v___x_2314_ = lean_string_append(v___x_2313_, v___x_2312_);
    return v___x_2314_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21() -> *mut LeanObject {
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    v___x_2315_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10;
    v___x_2316_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20_once),
        _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__20,
    );
    v___x_2317_ = lean_string_append(v___x_2316_, v___x_2315_);
    return v___x_2317_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonLogConfig_fromJson(
    mut v_json_2318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2324_: u8 = 0;
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2330_: u8 = 0;
    let mut v_a_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2334_: u8 = 0;
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2338_: u8 = 0;
    let mut v_a_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2345_: u8 = 0;
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2351_: u8 = 0;
    let mut v_a_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2355_: u8 = 0;
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2359_: u8 = 0;
    let mut v_a_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2366_: u8 = 0;
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2372_: u8 = 0;
    let mut v_a_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2376_: u8 = 0;
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2380_: u8 = 0;
    let mut v_a_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2384_: u8 = 0;
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2319_ = l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__0;
                lean_inc(v_json_2318_);
                v___x_2320_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__0(v_json_2318_, v___x_2319_);
                if lean_obj_tag(v___x_2320_) == 0 {
                    lean_dec(v_json_2318_);
                    v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
                    v_isSharedCheck_2330_ = (!lean_is_exclusive(v___x_2320_)) as u8;
                    if v_isSharedCheck_2330_ == 0 {
                        v___x_2323_ = v___x_2320_;
                        v_isShared_2324_ = v_isSharedCheck_2330_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2321_);
                        lean_dec(v___x_2320_);
                        v___x_2323_ = lean_box(0);
                        v_isShared_2324_ = v_isSharedCheck_2330_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_2320_) == 0 {
                        lean_dec(v_json_2318_);
                        v_a_2331_ = lean_ctor_get(v___x_2320_, 0);
                        v_isSharedCheck_2338_ = (!lean_is_exclusive(v___x_2320_)) as u8;
                        if v_isSharedCheck_2338_ == 0 {
                            v___x_2333_ = v___x_2320_;
                            v_isShared_2334_ = v_isSharedCheck_2338_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2331_);
                            lean_dec(v___x_2320_);
                            v___x_2333_ = lean_box(0);
                            v_isShared_2334_ = v_isSharedCheck_2338_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2339_ = lean_ctor_get(v___x_2320_, 0);
                        lean_inc(v_a_2339_);
                        lean_dec_ref_known(v___x_2320_, 1);
                        v___x_2340_ = l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__10;
                        lean_inc(v_json_2318_);
                        v___x_2341_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(v_json_2318_, v___x_2340_);
                        if lean_obj_tag(v___x_2341_) == 0 {
                            lean_dec(v_a_2339_);
                            lean_dec(v_json_2318_);
                            v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
                            v_isSharedCheck_2351_ = (!lean_is_exclusive(v___x_2341_)) as u8;
                            if v_isSharedCheck_2351_ == 0 {
                                v___x_2344_ = v___x_2341_;
                                v_isShared_2345_ = v_isSharedCheck_2351_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_2342_);
                                lean_dec(v___x_2341_);
                                v___x_2344_ = lean_box(0);
                                v_isShared_2345_ = v_isSharedCheck_2351_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_2341_) == 0 {
                                lean_dec(v_a_2339_);
                                lean_dec(v_json_2318_);
                                v_a_2352_ = lean_ctor_get(v___x_2341_, 0);
                                v_isSharedCheck_2359_ = (!lean_is_exclusive(v___x_2341_)) as u8;
                                if v_isSharedCheck_2359_ == 0 {
                                    v___x_2354_ = v___x_2341_;
                                    v_isShared_2355_ = v_isSharedCheck_2359_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_2352_);
                                    lean_dec(v___x_2341_);
                                    v___x_2354_ = lean_box(0);
                                    v_isShared_2355_ = v_isSharedCheck_2359_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_2360_ = lean_ctor_get(v___x_2341_, 0);
                                lean_inc(v_a_2360_);
                                lean_dec_ref_known(v___x_2341_, 1);
                                v___x_2361_ =
                                    l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__16;
                                v___x_2362_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1(v_json_2318_, v___x_2361_);
                                if lean_obj_tag(v___x_2362_) == 0 {
                                    lean_dec(v_a_2360_);
                                    lean_dec(v_a_2339_);
                                    v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
                                    v_isSharedCheck_2372_ = (!lean_is_exclusive(v___x_2362_)) as u8;
                                    if v_isSharedCheck_2372_ == 0 {
                                        v___x_2365_ = v___x_2362_;
                                        v_isShared_2366_ = v_isSharedCheck_2372_;
                                        state = 9;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2363_);
                                        lean_dec(v___x_2362_);
                                        v___x_2365_ = lean_box(0);
                                        v_isShared_2366_ = v_isSharedCheck_2372_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if lean_obj_tag(v___x_2362_) == 0 {
                                        lean_dec(v_a_2360_);
                                        lean_dec(v_a_2339_);
                                        v_a_2373_ = lean_ctor_get(v___x_2362_, 0);
                                        v_isSharedCheck_2380_ =
                                            (!lean_is_exclusive(v___x_2362_)) as u8;
                                        if v_isSharedCheck_2380_ == 0 {
                                            v___x_2375_ = v___x_2362_;
                                            v_isShared_2376_ = v_isSharedCheck_2380_;
                                            state = 11;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2373_);
                                            lean_dec(v___x_2362_);
                                            v___x_2375_ = lean_box(0);
                                            v_isShared_2376_ = v_isSharedCheck_2380_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_2381_ = lean_ctor_get(v___x_2362_, 0);
                                        v_isSharedCheck_2389_ =
                                            (!lean_is_exclusive(v___x_2362_)) as u8;
                                        if v_isSharedCheck_2389_ == 0 {
                                            v___x_2383_ = v___x_2362_;
                                            v_isShared_2384_ = v_isSharedCheck_2389_;
                                            state = 13;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2381_);
                                            lean_dec(v___x_2362_);
                                            v___x_2383_ = lean_box(0);
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
                v___x_2325_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__9,
                );
                v___x_2326_ = lean_string_append(v___x_2325_, v_a_2321_);
                lean_dec(v_a_2321_);
                if v_isShared_2324_ == 0 {
                    lean_ctor_set(v___x_2323_, 0, v___x_2326_);
                    v___x_2328_ = v___x_2323_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2326_);
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
                    lean_ctor_set_tag(v___x_2333_, 0);
                    v___x_2336_ = v___x_2333_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
                    v___x_2336_ = v_reuseFailAlloc_2337_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2336_;
            }
            5 => {
                v___x_2346_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__15,
                );
                v___x_2347_ = lean_string_append(v___x_2346_, v_a_2342_);
                lean_dec(v_a_2342_);
                if v_isShared_2345_ == 0 {
                    lean_ctor_set(v___x_2344_, 0, v___x_2347_);
                    v___x_2349_ = v___x_2344_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
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
                    lean_ctor_set_tag(v___x_2354_, 0);
                    v___x_2357_ = v___x_2354_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
                    v___x_2357_ = v_reuseFailAlloc_2358_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2357_;
            }
            9 => {
                v___x_2367_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__21,
                );
                v___x_2368_ = lean_string_append(v___x_2367_, v_a_2363_);
                lean_dec(v_a_2363_);
                if v_isShared_2366_ == 0 {
                    lean_ctor_set(v___x_2365_, 0, v___x_2368_);
                    v___x_2370_ = v___x_2365_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2368_);
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
                    lean_ctor_set_tag(v___x_2375_, 0);
                    v___x_2378_ = v___x_2375_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
                    v___x_2378_ = v_reuseFailAlloc_2379_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2378_;
            }
            13 => {
                v___x_2385_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2385_, 0, v_a_2339_);
                lean_ctor_set(v___x_2385_, 1, v_a_2360_);
                lean_ctor_set(v___x_2385_, 2, v_a_2381_);
                if v_isShared_2384_ == 0 {
                    lean_ctor_set(v___x_2383_, 0, v___x_2385_);
                    v___x_2387_ = v___x_2383_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
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
    mut v_00_u03b2_2390_: *mut LeanObject,
    mut v_m_2391_: *mut LeanObject,
    mut v_a_2392_: *mut LeanObject,
    mut v_b_2393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    v___x_2394_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5___redArg(v_m_2391_, v_a_2392_, v_b_2393_);
    return v___x_2394_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6(
    mut v_00_u03b2_2395_: *mut LeanObject,
    mut v_a_2396_: *mut LeanObject,
    mut v_x_2397_: *mut LeanObject,
) -> u8 {
    let mut v___x_2398_: u8 = 0;
    v___x_2398_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___redArg(v_a_2396_, v_x_2397_);
    return v___x_2398_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6___boxed(
    mut v_00_u03b2_2399_: *mut LeanObject,
    mut v_a_2400_: *mut LeanObject,
    mut v_x_2401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2402_: u8 = 0;
    let mut v_r_2403_: *mut LeanObject = core::ptr::null_mut();
    v_res_2402_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__6(v_00_u03b2_2399_, v_a_2400_, v_x_2401_);
    lean_dec(v_x_2401_);
    lean_dec_ref(v_a_2400_);
    v_r_2403_ = lean_box((v_res_2402_) as usize);
    return v_r_2403_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7(
    mut v_00_u03b2_2404_: *mut LeanObject,
    mut v_data_2405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    v___x_2406_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7___redArg(v_data_2405_);
    return v___x_2406_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8(
    mut v_00_u03b2_2407_: *mut LeanObject,
    mut v_i_2408_: *mut LeanObject,
    mut v_source_2409_: *mut LeanObject,
    mut v_target_2410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    v___x_2411_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8___redArg(v_i_2408_, v_source_2409_, v_target_2410_);
    return v___x_2411_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10(
    mut v_00_u03b2_2412_: *mut LeanObject,
    mut v_x_2413_: *mut LeanObject,
    mut v_x_2414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    v___x_2415_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLogConfig_fromJson_spec__1_spec__2_spec__4_spec__5_spec__7_spec__8_spec__10___redArg(v_x_2413_, v_x_2414_);
    return v___x_2415_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__0(
    mut v_k_2418_: *mut LeanObject,
    mut v_x_2419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2424_: u8 = 0;
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2431_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2419_) == 0 {
                    lean_dec_ref(v_k_2418_);
                    v___x_2420_ = lean_box(0);
                    return v___x_2420_;
                } else {
                    v_val_2421_ = lean_ctor_get(v_x_2419_, 0);
                    v_isSharedCheck_2431_ = (!lean_is_exclusive(v_x_2419_)) as u8;
                    if v_isSharedCheck_2431_ == 0 {
                        v___x_2423_ = v_x_2419_;
                        v_isShared_2424_ = v_isSharedCheck_2431_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2421_);
                        lean_dec(v_x_2419_);
                        v___x_2423_ = lean_box(0);
                        v_isShared_2424_ = v_isSharedCheck_2431_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2424_ == 0 {
                    lean_ctor_set_tag(v___x_2423_, 3);
                    v___x_2426_ = v___x_2423_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2430_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_val_2421_);
                    v___x_2426_ = v_reuseFailAlloc_2430_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2427_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2427_, 0, v_k_2418_);
                lean_ctor_set(v___x_2427_, 1, v___x_2426_);
                v___x_2428_ = lean_box(0);
                v___x_2429_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2429_, 0, v___x_2427_);
                lean_ctor_set(v___x_2429_, 1, v___x_2428_);
                return v___x_2429_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1(
    mut v_sz_2432_: usize,
    mut v_i_2433_: usize,
    mut v_bs_2434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2435_: u8 = 0;
    let mut v_v_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: usize = 0;
    let mut v___x_2441_: usize = 0;
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2435_ = lean_usize_dec_lt(v_i_2433_, v_sz_2432_);
                if v___x_2435_ == 0 {
                    return v_bs_2434_;
                } else {
                    v_v_2436_ = lean_array_uget(v_bs_2434_, v_i_2433_);
                    v___x_2437_ = lean_unsigned_to_nat(0);
                    v_bs_x27_2438_ = lean_array_uset(v_bs_2434_, v_i_2433_, v___x_2437_);
                    v___x_2439_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2439_, 0, v_v_2436_);
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
    mut v_sz_2444_: *mut LeanObject,
    mut v_i_2445_: *mut LeanObject,
    mut v_bs_2446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2447_: usize = 0;
    let mut v_i_boxed_2448_: usize = 0;
    let mut v_res_2449_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2447_ = lean_unbox_usize(v_sz_2444_);
    lean_dec(v_sz_2444_);
    v_i_boxed_2448_ = lean_unbox_usize(v_i_2445_);
    lean_dec(v_i_2445_);
    v_res_2449_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__1(v_sz_boxed_2447_, v_i_boxed_2448_, v_bs_2446_);
    return v_res_2449_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__2(
    mut v_x_2450_: *mut LeanObject,
    mut v_x_2451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2451_) == 0 {
                    return v_x_2450_;
                } else {
                    v_key_2452_ = lean_ctor_get(v_x_2451_, 0);
                    lean_inc(v_key_2452_);
                    v_tail_2453_ = lean_ctor_get(v_x_2451_, 2);
                    lean_inc(v_tail_2453_);
                    lean_dec_ref_known(v_x_2451_, 3);
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
    mut v_as_2456_: *mut LeanObject,
    mut v_i_2457_: usize,
    mut v_stop_2458_: usize,
    mut v_b_2459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2460_: u8 = 0;
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: usize = 0;
    let mut v___x_2464_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2460_ = lean_usize_dec_eq(v_i_2457_, v_stop_2458_);
                if v___x_2460_ == 0 {
                    v___x_2461_ = lean_array_uget_borrowed(v_as_2456_, v_i_2457_);
                    lean_inc(v___x_2461_);
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
    mut v_as_2466_: *mut LeanObject,
    mut v_i_2467_: *mut LeanObject,
    mut v_stop_2468_: *mut LeanObject,
    mut v_b_2469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2470_: usize = 0;
    let mut v_stop_boxed_2471_: usize = 0;
    let mut v_res_2472_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2470_ = lean_unbox_usize(v_i_2467_);
    lean_dec(v_i_2467_);
    v_stop_boxed_2471_ = lean_unbox_usize(v_stop_2468_);
    lean_dec(v_stop_2468_);
    v_res_2472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1_spec__3(v_as_2466_, v_i_boxed_2470_, v_stop_boxed_2471_, v_b_2469_);
    lean_dec_ref(v_as_2466_);
    return v_res_2472_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(
    mut v_k_2473_: *mut LeanObject,
    mut v_x_2474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2477_: usize = 0;
    let mut v___x_2478_: usize = 0;
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: u8 = 0;
    let mut v___x_2492_: u8 = 0;
    let mut v___x_2493_: usize = 0;
    let mut v___x_2494_: usize = 0;
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: usize = 0;
    let mut v___x_2497_: usize = 0;
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2474_) == 0 {
                    lean_dec_ref(v_k_2473_);
                    v___x_2484_ = lean_box(0);
                    return v___x_2484_;
                } else {
                    v_val_2485_ = lean_ctor_get(v_x_2474_, 0);
                    v_size_2486_ = lean_ctor_get(v_val_2485_, 0);
                    v_buckets_2487_ = lean_ctor_get(v_val_2485_, 1);
                    v___x_2488_ = lean_mk_empty_array_with_capacity(v_size_2486_);
                    v___x_2489_ = lean_unsigned_to_nat(0);
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
                v___x_2480_ = lean_alloc_ctor(4, 1, (0) as u32);
                lean_ctor_set(v___x_2480_, 0, v___x_2479_);
                v___x_2481_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2481_, 0, v_k_2473_);
                lean_ctor_set(v___x_2481_, 1, v___x_2480_);
                v___x_2482_ = lean_box(0);
                v___x_2483_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2483_, 0, v___x_2481_);
                lean_ctor_set(v___x_2483_, 1, v___x_2482_);
                return v___x_2483_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1___boxed(
    mut v_k_2499_: *mut LeanObject,
    mut v_x_2500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2501_: *mut LeanObject = core::ptr::null_mut();
    v_res_2501_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(v_k_2499_, v_x_2500_);
    lean_dec(v_x_2500_);
    return v_res_2501_;
}
pub unsafe fn l_Lean_Lsp_instToJsonLogConfig_toJson(
    mut v_x_2502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logDir_x3f_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_allowedMethods_x3f_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_disallowedMethods_x3f_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    v_logDir_x3f_2503_ = lean_ctor_get(v_x_2502_, 0);
    lean_inc(v_logDir_x3f_2503_);
    v_allowedMethods_x3f_2504_ = lean_ctor_get(v_x_2502_, 1);
    lean_inc(v_allowedMethods_x3f_2504_);
    v_disallowedMethods_x3f_2505_ = lean_ctor_get(v_x_2502_, 2);
    lean_inc(v_disallowedMethods_x3f_2505_);
    lean_dec_ref(v_x_2502_);
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
    lean_dec(v_allowedMethods_x3f_2504_);
    v___x_2510_ = l_Lean_Lsp_instFromJsonLogConfig_fromJson___closed__16;
    v___x_2511_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLogConfig_toJson_spec__1(
        v___x_2510_,
        v_disallowedMethods_x3f_2505_,
    );
    lean_dec(v_disallowedMethods_x3f_2505_);
    v___x_2512_ = lean_box(0);
    v___x_2513_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2513_, 0, v___x_2511_);
    lean_ctor_set(v___x_2513_, 1, v___x_2512_);
    v___x_2514_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2514_, 0, v___x_2509_);
    lean_ctor_set(v___x_2514_, 1, v___x_2513_);
    v___x_2515_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2515_, 0, v___x_2507_);
    lean_ctor_set(v___x_2515_, 1, v___x_2514_);
    v___x_2516_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2;
    v___x_2517_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_2515_, v___x_2516_);
    v___x_2518_ = l_Lean_Json_mkObj(v___x_2517_);
    lean_dec(v___x_2517_);
    return v___x_2518_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0(
    mut v_k_2521_: *mut LeanObject,
    mut v_x_2522_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2522_) == 0 {
        let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_k_2521_);
        v___x_2523_ = lean_box(0);
        return v___x_2523_;
    } else {
        let mut v_val_2524_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2526_: u8 = 0;
        let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
        v_val_2524_ = lean_ctor_get(v_x_2522_, 0);
        v___x_2525_ = lean_alloc_ctor(1, 0, (1) as u32);
        v___x_2526_ = (lean_unbox(v_val_2524_) as u8);
        lean_ctor_set_uint8(v___x_2525_, 0 as u32, v___x_2526_);
        v___x_2527_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2527_, 0, v_k_2521_);
        lean_ctor_set(v___x_2527_, 1, v___x_2525_);
        v___x_2528_ = lean_box(0);
        v___x_2529_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2529_, 0, v___x_2527_);
        lean_ctor_set(v___x_2529_, 1, v___x_2528_);
        return v___x_2529_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0___boxed(
    mut v_k_2530_: *mut LeanObject,
    mut v_x_2531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2532_: *mut LeanObject = core::ptr::null_mut();
    v_res_2532_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0(
        v_k_2530_, v_x_2531_,
    );
    lean_dec(v_x_2531_);
    return v_res_2532_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__1(
    mut v_k_2533_: *mut LeanObject,
    mut v_x_2534_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2534_) == 0 {
        let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_k_2533_);
        v___x_2535_ = lean_box(0);
        return v___x_2535_;
    } else {
        let mut v_val_2536_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
        v_val_2536_ = lean_ctor_get(v_x_2534_, 0);
        lean_inc(v_val_2536_);
        lean_dec_ref_known(v_x_2534_, 1);
        v___x_2537_ = l_Lean_Lsp_instToJsonLogConfig_toJson(v_val_2536_);
        v___x_2538_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2538_, 0, v_k_2533_);
        lean_ctor_set(v___x_2538_, 1, v___x_2537_);
        v___x_2539_ = lean_box(0);
        v___x_2540_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2540_, 0, v___x_2538_);
        lean_ctor_set(v___x_2540_, 1, v___x_2539_);
        return v___x_2540_;
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonInitializationOptions_toJson(
    mut v_x_2543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hasWidgets_x3f_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_logCfg_x3f_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2548_: u8 = 0;
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2561_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_hasWidgets_x3f_2544_ = lean_ctor_get(v_x_2543_, 0);
                v_logCfg_x3f_2545_ = lean_ctor_get(v_x_2543_, 1);
                v_isSharedCheck_2561_ = (!lean_is_exclusive(v_x_2543_)) as u8;
                if v_isSharedCheck_2561_ == 0 {
                    v___x_2547_ = v_x_2543_;
                    v_isShared_2548_ = v_isSharedCheck_2561_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_logCfg_x3f_2545_);
                    lean_inc(v_hasWidgets_x3f_2544_);
                    lean_dec(v_x_2543_);
                    v___x_2547_ = lean_box(0);
                    v_isShared_2548_ = v_isSharedCheck_2561_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2549_ = l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__0;
                v___x_2550_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__0(v___x_2549_, v_hasWidgets_x3f_2544_);
                lean_dec(v_hasWidgets_x3f_2544_);
                v___x_2551_ = l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__1;
                v___x_2552_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializationOptions_toJson_spec__1(v___x_2551_, v_logCfg_x3f_2545_);
                v___x_2553_ = lean_box(0);
                if v_isShared_2548_ == 0 {
                    lean_ctor_set_tag(v___x_2547_, 1);
                    lean_ctor_set(v___x_2547_, 1, v___x_2553_);
                    lean_ctor_set(v___x_2547_, 0, v___x_2552_);
                    v___x_2555_ = v___x_2547_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2552_);
                    lean_ctor_set(v_reuseFailAlloc_2560_, 1, v___x_2553_);
                    v___x_2555_ = v_reuseFailAlloc_2560_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2556_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2556_, 0, v___x_2550_);
                lean_ctor_set(v___x_2556_, 1, v___x_2555_);
                v___x_2557_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2;
                v___x_2558_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_2556_, v___x_2557_);
                v___x_2559_ = l_Lean_Json_mkObj(v___x_2558_);
                lean_dec(v___x_2558_);
                return v___x_2559_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2(
    mut v_x_2566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2572_: u8 = 0;
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2576_: u8 = 0;
    let mut v_a_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2580_: u8 = 0;
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2585_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2566_) == 0 {
                    v___x_2567_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2___closed__0;
                    return v___x_2567_;
                } else {
                    v___x_2568_ = l_Lean_Lsp_instFromJsonLogConfig_fromJson(v_x_2566_);
                    if lean_obj_tag(v___x_2568_) == 0 {
                        v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
                        v_isSharedCheck_2576_ = (!lean_is_exclusive(v___x_2568_)) as u8;
                        if v_isSharedCheck_2576_ == 0 {
                            v___x_2571_ = v___x_2568_;
                            v_isShared_2572_ = v_isSharedCheck_2576_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2569_);
                            lean_dec(v___x_2568_);
                            v___x_2571_ = lean_box(0);
                            v_isShared_2572_ = v_isSharedCheck_2576_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2577_ = lean_ctor_get(v___x_2568_, 0);
                        v_isSharedCheck_2585_ = (!lean_is_exclusive(v___x_2568_)) as u8;
                        if v_isSharedCheck_2585_ == 0 {
                            v___x_2579_ = v___x_2568_;
                            v_isShared_2580_ = v_isSharedCheck_2585_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2577_);
                            lean_dec(v___x_2568_);
                            v___x_2579_ = lean_box(0);
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
                    v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
                    v___x_2574_ = v_reuseFailAlloc_2575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2574_;
            }
            3 => {
                v___x_2581_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2581_, 0, v_a_2577_);
                if v_isShared_2580_ == 0 {
                    lean_ctor_set(v___x_2579_, 0, v___x_2581_);
                    v___x_2583_ = v___x_2579_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
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
    mut v_j_2586_: *mut LeanObject,
    mut v_k_2587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    v___x_2588_ = l_Lean_Json_getObjValD(v_j_2586_, v_k_2587_);
    v___x_2589_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1_spec__2(v___x_2588_);
    return v___x_2589_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1___boxed(
    mut v_j_2590_: *mut LeanObject,
    mut v_k_2591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2592_: *mut LeanObject = core::ptr::null_mut();
    v_res_2592_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1(v_j_2590_, v_k_2591_);
    lean_dec_ref(v_k_2591_);
    return v_res_2592_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0(
    mut v_x_2595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2601_: u8 = 0;
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2605_: u8 = 0;
    let mut v_a_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2609_: u8 = 0;
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2614_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2595_) == 0 {
                    v___x_2596_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0___closed__0;
                    return v___x_2596_;
                } else {
                    v___x_2597_ = l_Lean_Json_getBool_x3f(v_x_2595_);
                    if lean_obj_tag(v___x_2597_) == 0 {
                        v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
                        v_isSharedCheck_2605_ = (!lean_is_exclusive(v___x_2597_)) as u8;
                        if v_isSharedCheck_2605_ == 0 {
                            v___x_2600_ = v___x_2597_;
                            v_isShared_2601_ = v_isSharedCheck_2605_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2598_);
                            lean_dec(v___x_2597_);
                            v___x_2600_ = lean_box(0);
                            v_isShared_2601_ = v_isSharedCheck_2605_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2606_ = lean_ctor_get(v___x_2597_, 0);
                        v_isSharedCheck_2614_ = (!lean_is_exclusive(v___x_2597_)) as u8;
                        if v_isSharedCheck_2614_ == 0 {
                            v___x_2608_ = v___x_2597_;
                            v_isShared_2609_ = v_isSharedCheck_2614_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2606_);
                            lean_dec(v___x_2597_);
                            v___x_2608_ = lean_box(0);
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
                    v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
                    v___x_2603_ = v_reuseFailAlloc_2604_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2603_;
            }
            3 => {
                v___x_2610_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2610_, 0, v_a_2606_);
                if v_isShared_2609_ == 0 {
                    lean_ctor_set(v___x_2608_, 0, v___x_2610_);
                    v___x_2612_ = v___x_2608_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2610_);
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
    mut v_x_2615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2616_: *mut LeanObject = core::ptr::null_mut();
    v_res_2616_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0(v_x_2615_);
    lean_dec(v_x_2615_);
    return v_res_2616_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0(
    mut v_j_2617_: *mut LeanObject,
    mut v_k_2618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    v___x_2619_ = l_Lean_Json_getObjValD(v_j_2617_, v_k_2618_);
    v___x_2620_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0_spec__0(v___x_2619_);
    lean_dec(v___x_2619_);
    return v___x_2620_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0___boxed(
    mut v_j_2621_: *mut LeanObject,
    mut v_k_2622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2623_: *mut LeanObject = core::ptr::null_mut();
    v_res_2623_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0(v_j_2621_, v_k_2622_);
    lean_dec_ref(v_k_2622_);
    return v_res_2623_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__2()
-> *mut LeanObject {
    let mut v___x_2629_: u8 = 0;
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    v___x_2629_ = 1;
    v___x_2630_ = l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__1;
    v___x_2631_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2630_, v___x_2629_);
    return v___x_2631_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__3()
-> *mut LeanObject {
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    v___x_2632_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5;
    v___x_2633_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_2638_: u8 = 0;
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    v___x_2638_ = 1;
    v___x_2639_ = l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__5;
    v___x_2640_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2639_, v___x_2638_);
    return v___x_2640_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__7()
-> *mut LeanObject {
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    v___x_2641_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__6,
    );
    v___x_2642_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    v___x_2644_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10;
    v___x_2645_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_2650_: u8 = 0;
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    v___x_2650_ = 1;
    v___x_2651_ = l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__10;
    v___x_2652_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2651_, v___x_2650_);
    return v___x_2652_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__12()
-> *mut LeanObject {
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    v___x_2653_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11_once
        ),
        _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__11,
    );
    v___x_2654_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    v___x_2656_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10;
    v___x_2657_ = lean_obj_once(
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
    mut v_json_2659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2665_: u8 = 0;
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2671_: u8 = 0;
    let mut v_a_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2675_: u8 = 0;
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2679_: u8 = 0;
    let mut v_a_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2686_: u8 = 0;
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2692_: u8 = 0;
    let mut v_a_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2696_: u8 = 0;
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2700_: u8 = 0;
    let mut v_a_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2704_: u8 = 0;
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2709_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2660_ = l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__0;
                lean_inc(v_json_2659_);
                v___x_2661_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__0(v_json_2659_, v___x_2660_);
                if lean_obj_tag(v___x_2661_) == 0 {
                    lean_dec(v_json_2659_);
                    v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
                    v_isSharedCheck_2671_ = (!lean_is_exclusive(v___x_2661_)) as u8;
                    if v_isSharedCheck_2671_ == 0 {
                        v___x_2664_ = v___x_2661_;
                        v_isShared_2665_ = v_isSharedCheck_2671_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2662_);
                        lean_dec(v___x_2661_);
                        v___x_2664_ = lean_box(0);
                        v_isShared_2665_ = v_isSharedCheck_2671_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_2661_) == 0 {
                        lean_dec(v_json_2659_);
                        v_a_2672_ = lean_ctor_get(v___x_2661_, 0);
                        v_isSharedCheck_2679_ = (!lean_is_exclusive(v___x_2661_)) as u8;
                        if v_isSharedCheck_2679_ == 0 {
                            v___x_2674_ = v___x_2661_;
                            v_isShared_2675_ = v_isSharedCheck_2679_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2672_);
                            lean_dec(v___x_2661_);
                            v___x_2674_ = lean_box(0);
                            v_isShared_2675_ = v_isSharedCheck_2679_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2680_ = lean_ctor_get(v___x_2661_, 0);
                        lean_inc(v_a_2680_);
                        lean_dec_ref_known(v___x_2661_, 1);
                        v___x_2681_ = l_Lean_Lsp_instToJsonInitializationOptions_toJson___closed__1;
                        v___x_2682_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializationOptions_fromJson_spec__1(v_json_2659_, v___x_2681_);
                        if lean_obj_tag(v___x_2682_) == 0 {
                            lean_dec(v_a_2680_);
                            v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
                            v_isSharedCheck_2692_ = (!lean_is_exclusive(v___x_2682_)) as u8;
                            if v_isSharedCheck_2692_ == 0 {
                                v___x_2685_ = v___x_2682_;
                                v_isShared_2686_ = v_isSharedCheck_2692_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_2683_);
                                lean_dec(v___x_2682_);
                                v___x_2685_ = lean_box(0);
                                v_isShared_2686_ = v_isSharedCheck_2692_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_2682_) == 0 {
                                lean_dec(v_a_2680_);
                                v_a_2693_ = lean_ctor_get(v___x_2682_, 0);
                                v_isSharedCheck_2700_ = (!lean_is_exclusive(v___x_2682_)) as u8;
                                if v_isSharedCheck_2700_ == 0 {
                                    v___x_2695_ = v___x_2682_;
                                    v_isShared_2696_ = v_isSharedCheck_2700_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_2693_);
                                    lean_dec(v___x_2682_);
                                    v___x_2695_ = lean_box(0);
                                    v_isShared_2696_ = v_isSharedCheck_2700_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_2701_ = lean_ctor_get(v___x_2682_, 0);
                                v_isSharedCheck_2709_ = (!lean_is_exclusive(v___x_2682_)) as u8;
                                if v_isSharedCheck_2709_ == 0 {
                                    v___x_2703_ = v___x_2682_;
                                    v_isShared_2704_ = v_isSharedCheck_2709_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_2701_);
                                    lean_dec(v___x_2682_);
                                    v___x_2703_ = lean_box(0);
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
                v___x_2666_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__8,
                );
                v___x_2667_ = lean_string_append(v___x_2666_, v_a_2662_);
                lean_dec(v_a_2662_);
                if v_isShared_2665_ == 0 {
                    lean_ctor_set(v___x_2664_, 0, v___x_2667_);
                    v___x_2669_ = v___x_2664_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2667_);
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
                    lean_ctor_set_tag(v___x_2674_, 0);
                    v___x_2677_ = v___x_2674_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
                    v___x_2677_ = v_reuseFailAlloc_2678_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2677_;
            }
            5 => {
                v___x_2687_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonInitializationOptions_fromJson___closed__13,
                );
                v___x_2688_ = lean_string_append(v___x_2687_, v_a_2683_);
                lean_dec(v_a_2683_);
                if v_isShared_2686_ == 0 {
                    lean_ctor_set(v___x_2685_, 0, v___x_2688_);
                    v___x_2690_ = v___x_2685_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2688_);
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
                    lean_ctor_set_tag(v___x_2695_, 0);
                    v___x_2698_ = v___x_2695_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
                    v___x_2698_ = v_reuseFailAlloc_2699_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2698_;
            }
            9 => {
                v___x_2705_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2705_, 0, v_a_2680_);
                lean_ctor_set(v___x_2705_, 1, v_a_2701_);
                if v_isShared_2704_ == 0 {
                    lean_ctor_set(v___x_2703_, 0, v___x_2705_);
                    v___x_2707_ = v___x_2703_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2705_);
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
    mut v_k_2712_: *mut LeanObject,
    mut v_x_2713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2718_: u8 = 0;
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2726_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2713_) == 0 {
                    lean_dec_ref(v_k_2712_);
                    v___x_2714_ = lean_box(0);
                    return v___x_2714_;
                } else {
                    v_val_2715_ = lean_ctor_get(v_x_2713_, 0);
                    v_isSharedCheck_2726_ = (!lean_is_exclusive(v_x_2713_)) as u8;
                    if v_isSharedCheck_2726_ == 0 {
                        v___x_2717_ = v_x_2713_;
                        v_isShared_2718_ = v_isSharedCheck_2726_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2715_);
                        lean_dec(v_x_2713_);
                        v___x_2717_ = lean_box(0);
                        v_isShared_2718_ = v_isSharedCheck_2726_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2719_ = l_Lean_JsonNumber_fromInt(v_val_2715_);
                if v_isShared_2718_ == 0 {
                    lean_ctor_set_tag(v___x_2717_, 2);
                    lean_ctor_set(v___x_2717_, 0, v___x_2719_);
                    v___x_2721_ = v___x_2717_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2725_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2719_);
                    v___x_2721_ = v_reuseFailAlloc_2725_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2722_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2722_, 0, v_k_2712_);
                lean_ctor_set(v___x_2722_, 1, v___x_2721_);
                v___x_2723_ = lean_box(0);
                v___x_2724_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2724_, 0, v___x_2722_);
                lean_ctor_set(v___x_2724_, 1, v___x_2723_);
                return v___x_2724_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__1(
    mut v_k_2727_: *mut LeanObject,
    mut v_x_2728_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2728_) == 0 {
        let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_k_2727_);
        v___x_2729_ = lean_box(0);
        return v___x_2729_;
    } else {
        let mut v_val_2730_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
        v_val_2730_ = lean_ctor_get(v_x_2728_, 0);
        lean_inc(v_val_2730_);
        lean_dec_ref_known(v_x_2728_, 1);
        v___x_2731_ = l_Lean_Lsp_instToJsonClientInfo_toJson(v_val_2730_);
        v___x_2732_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2732_, 0, v_k_2727_);
        lean_ctor_set(v___x_2732_, 1, v___x_2731_);
        v___x_2733_ = lean_box(0);
        v___x_2734_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2734_, 0, v___x_2732_);
        lean_ctor_set(v___x_2734_, 1, v___x_2733_);
        return v___x_2734_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__2(
    mut v_k_2735_: *mut LeanObject,
    mut v_x_2736_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2736_) == 0 {
        let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_k_2735_);
        v___x_2737_ = lean_box(0);
        return v___x_2737_;
    } else {
        let mut v_val_2738_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
        v_val_2738_ = lean_ctor_get(v_x_2736_, 0);
        lean_inc(v_val_2738_);
        lean_dec_ref_known(v_x_2736_, 1);
        v___x_2739_ = l_Lean_Lsp_instToJsonInitializationOptions_toJson(v_val_2738_);
        v___x_2740_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2740_, 0, v_k_2735_);
        lean_ctor_set(v___x_2740_, 1, v___x_2739_);
        v___x_2741_ = lean_box(0);
        v___x_2742_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2742_, 0, v___x_2740_);
        lean_ctor_set(v___x_2742_, 1, v___x_2741_);
        return v___x_2742_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4(
    mut v_sz_2743_: usize,
    mut v_i_2744_: usize,
    mut v_bs_2745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2746_: u8 = 0;
    let mut v_v_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: usize = 0;
    let mut v___x_2752_: usize = 0;
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2746_ = lean_usize_dec_lt(v_i_2744_, v_sz_2743_);
                if v___x_2746_ == 0 {
                    return v_bs_2745_;
                } else {
                    v_v_2747_ = lean_array_uget(v_bs_2745_, v_i_2744_);
                    v___x_2748_ = lean_unsigned_to_nat(0);
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
    mut v_sz_2755_: *mut LeanObject,
    mut v_i_2756_: *mut LeanObject,
    mut v_bs_2757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2758_: usize = 0;
    let mut v_i_boxed_2759_: usize = 0;
    let mut v_res_2760_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2758_ = lean_unbox_usize(v_sz_2755_);
    lean_dec(v_sz_2755_);
    v_i_boxed_2759_ = lean_unbox_usize(v_i_2756_);
    lean_dec(v_i_2756_);
    v_res_2760_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4(v_sz_boxed_2758_, v_i_boxed_2759_, v_bs_2757_);
    return v_res_2760_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3(
    mut v_a_2761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_2762_: usize = 0;
    let mut v___x_2763_: usize = 0;
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    v_sz_2762_ = lean_array_size(v_a_2761_);
    v___x_2763_ = 0usize;
    v___x_2764_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3_spec__4(v_sz_2762_, v___x_2763_, v_a_2761_);
    v___x_2765_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_2765_, 0, v___x_2764_);
    return v___x_2765_;
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3(
    mut v_k_2766_: *mut LeanObject,
    mut v_x_2767_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2767_) == 0 {
        let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_k_2766_);
        v___x_2768_ = lean_box(0);
        return v___x_2768_;
    } else {
        let mut v_val_2769_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
        v_val_2769_ = lean_ctor_get(v_x_2767_, 0);
        lean_inc(v_val_2769_);
        lean_dec_ref_known(v_x_2767_, 1);
        v___x_2770_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3_spec__3(v_val_2769_);
        v___x_2771_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2771_, 0, v_k_2766_);
        lean_ctor_set(v___x_2771_, 1, v___x_2770_);
        v___x_2772_ = lean_box(0);
        v___x_2773_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2773_, 0, v___x_2771_);
        lean_ctor_set(v___x_2773_, 1, v___x_2772_);
        return v___x_2773_;
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonInitializeParams_toJson(
    mut v_x_2781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_processId_x3f_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_clientInfo_x3f_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rootUri_x3f_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initializationOptions_x3f_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_capabilities_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trace_2787_: u8 = 0;
    let mut v_workspaceFolders_x3f_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_processId_x3f_2782_ = lean_ctor_get(v_x_2781_, 0);
                lean_inc(v_processId_x3f_2782_);
                v_clientInfo_x3f_2783_ = lean_ctor_get(v_x_2781_, 1);
                lean_inc(v_clientInfo_x3f_2783_);
                v_rootUri_x3f_2784_ = lean_ctor_get(v_x_2781_, 2);
                lean_inc(v_rootUri_x3f_2784_);
                v_initializationOptions_x3f_2785_ = lean_ctor_get(v_x_2781_, 3);
                lean_inc(v_initializationOptions_x3f_2785_);
                v_capabilities_2786_ = lean_ctor_get(v_x_2781_, 4);
                lean_inc_ref(v_capabilities_2786_);
                v_trace_2787_ = lean_ctor_get_uint8(
                    v_x_2781_,
                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                );
                v_workspaceFolders_x3f_2788_ = lean_ctor_get(v_x_2781_, 5);
                lean_inc(v_workspaceFolders_x3f_2788_);
                lean_dec_ref(v_x_2781_);
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
                v___x_2799_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2799_, 0, v___x_2797_);
                lean_ctor_set(v___x_2799_, 1, v___x_2798_);
                v___x_2800_ = lean_box(0);
                v___x_2801_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2801_, 0, v___x_2799_);
                lean_ctor_set(v___x_2801_, 1, v___x_2800_);
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
                lean_inc(v___y_2804_);
                v___x_2805_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2805_, 0, v___x_2802_);
                lean_ctor_set(v___x_2805_, 1, v___y_2804_);
                v___x_2806_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2806_, 0, v___x_2805_);
                lean_ctor_set(v___x_2806_, 1, v___x_2800_);
                v___x_2807_ = l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__6;
                v___x_2808_ =
                    l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeParams_toJson_spec__3(
                        v___x_2807_,
                        v_workspaceFolders_x3f_2788_,
                    );
                v___x_2809_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2809_, 0, v___x_2808_);
                lean_ctor_set(v___x_2809_, 1, v___x_2800_);
                v___x_2810_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2810_, 0, v___x_2806_);
                lean_ctor_set(v___x_2810_, 1, v___x_2809_);
                v___x_2811_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2811_, 0, v___x_2801_);
                lean_ctor_set(v___x_2811_, 1, v___x_2810_);
                v___x_2812_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2812_, 0, v___x_2796_);
                lean_ctor_set(v___x_2812_, 1, v___x_2811_);
                v___x_2813_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2813_, 0, v___x_2794_);
                lean_ctor_set(v___x_2813_, 1, v___x_2812_);
                v___x_2814_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2814_, 0, v___x_2792_);
                lean_ctor_set(v___x_2814_, 1, v___x_2813_);
                v___x_2815_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2815_, 0, v___x_2790_);
                lean_ctor_set(v___x_2815_, 1, v___x_2814_);
                v___x_2816_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2;
                v___x_2817_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_2815_, v___x_2816_);
                v___x_2818_ = l_Lean_Json_mkObj(v___x_2817_);
                lean_dec(v___x_2817_);
                return v___x_2818_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instFromJsonInitializeParams___lam__0(
    mut v___x_2824_: *mut LeanObject,
    mut v___x_2825_: *mut LeanObject,
    mut v___x_2826_: *mut LeanObject,
    mut v___x_2827_: *mut LeanObject,
    mut v___x_2828_: *mut LeanObject,
    mut v___x_2829_: *mut LeanObject,
    mut v___f_2830_: *mut LeanObject,
    mut v_j_2831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_processId_x3f_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_clientInfo_x3f_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rootUri_x3f_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initializationOptions_x3f_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2845_: u8 = 0;
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2849_: u8 = 0;
    let mut v_a_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2853_: u8 = 0;
    let mut v___y_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2859_: u8 = 0;
    let mut v___y_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2870_: u8 = 0;
    let mut v___y_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2876_: u8 = 0;
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2880_: u8 = 0;
    let mut v___y_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2885_: u8 = 0;
    let mut v___y_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2891_: u8 = 0;
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2895_: u8 = 0;
    let mut v___y_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2899_: u8 = 0;
    let mut v___y_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2905_: u8 = 0;
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2909_: u8 = 0;
    let mut v___y_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2912_: u8 = 0;
    let mut v___y_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2918_: u8 = 0;
    let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2922_: u8 = 0;
    let mut v___y_2924_: u8 = 0;
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2931_: u8 = 0;
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2935_: u8 = 0;
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: u8 = 0;
    let mut v_a_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: u8 = 0;
    let mut v_isSharedCheck_2941_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2832_ = l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__0;
                lean_inc_n(v_j_2831_, 5);
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
                if lean_obj_tag(v___x_2841_) == 0 {
                    lean_dec_ref(v_initializationOptions_x3f_2839_);
                    lean_dec_ref(v_rootUri_x3f_2837_);
                    lean_dec_ref(v_clientInfo_x3f_2835_);
                    lean_dec_ref(v_processId_x3f_2833_);
                    lean_dec(v_j_2831_);
                    lean_dec_ref(v___f_2830_);
                    lean_dec_ref(v___x_2829_);
                    v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
                    v_isSharedCheck_2849_ = (!lean_is_exclusive(v___x_2841_)) as u8;
                    if v_isSharedCheck_2849_ == 0 {
                        v___x_2844_ = v___x_2841_;
                        v_isShared_2845_ = v_isSharedCheck_2849_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2842_);
                        lean_dec(v___x_2841_);
                        v___x_2844_ = lean_box(0);
                        v_isShared_2845_ = v_isSharedCheck_2849_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2850_ = lean_ctor_get(v___x_2841_, 0);
                    v_isSharedCheck_2941_ = (!lean_is_exclusive(v___x_2841_)) as u8;
                    if v_isSharedCheck_2941_ == 0 {
                        v___x_2852_ = v___x_2841_;
                        v_isShared_2853_ = v_isSharedCheck_2941_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2850_);
                        lean_dec(v___x_2841_);
                        v___x_2852_ = lean_box(0);
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
                    v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
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
                lean_inc(v_j_2831_);
                v___x_2937_ =
                    l_Lean_Json_getObjValAs_x3f___redArg(v_j_2831_, v___f_2830_, v___x_2936_);
                if lean_obj_tag(v___x_2937_) == 0 {
                    lean_dec_ref_known(v___x_2937_, 1);
                    v___x_2938_ = 0;
                    v___y_2924_ = v___x_2938_;
                    state = 18;
                    continue;
                } else {
                    v_a_2939_ = lean_ctor_get(v___x_2937_, 0);
                    lean_inc(v_a_2939_);
                    lean_dec_ref_known(v___x_2937_, 1);
                    v___x_2940_ = (lean_unbox(v_a_2939_) as u8);
                    lean_dec(v_a_2939_);
                    v___y_2924_ = v___x_2940_;
                    state = 18;
                    continue;
                }
            }
            4 => {
                v___x_2861_ = lean_alloc_ctor(0, 6, (1) as u32);
                lean_ctor_set(v___x_2861_, 0, v___y_2857_);
                lean_ctor_set(v___x_2861_, 1, v___y_2858_);
                lean_ctor_set(v___x_2861_, 2, v___y_2856_);
                lean_ctor_set(v___x_2861_, 3, v___y_2855_);
                lean_ctor_set(v___x_2861_, 4, v_a_2850_);
                lean_ctor_set(v___x_2861_, 5, v___y_2860_);
                lean_ctor_set_uint8(
                    v___x_2861_,
                    (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                    v___y_2859_,
                );
                if v_isShared_2853_ == 0 {
                    lean_ctor_set(v___x_2852_, 0, v___x_2861_);
                    v___x_2863_ = v___x_2852_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2861_);
                    v___x_2863_ = v_reuseFailAlloc_2864_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2863_;
            }
            6 => {
                if lean_obj_tag(v___y_2866_) == 0 {
                    lean_dec_ref_known(v___y_2866_, 1);
                    v___x_2872_ = lean_box(0);
                    v___y_2855_ = v___y_2871_;
                    v___y_2856_ = v___y_2867_;
                    v___y_2857_ = v___y_2868_;
                    v___y_2858_ = v___y_2869_;
                    v___y_2859_ = v___y_2870_;
                    v___y_2860_ = v___x_2872_;
                    state = 4;
                    continue;
                } else {
                    v_a_2873_ = lean_ctor_get(v___y_2866_, 0);
                    v_isSharedCheck_2880_ = (!lean_is_exclusive(v___y_2866_)) as u8;
                    if v_isSharedCheck_2880_ == 0 {
                        v___x_2875_ = v___y_2866_;
                        v_isShared_2876_ = v_isSharedCheck_2880_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2873_);
                        lean_dec(v___y_2866_);
                        v___x_2875_ = lean_box(0);
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
                    v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
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
                if lean_obj_tag(v_initializationOptions_x3f_2839_) == 0 {
                    lean_dec_ref_known(v_initializationOptions_x3f_2839_, 1);
                    v___x_2887_ = lean_box(0);
                    v___y_2866_ = v___y_2882_;
                    v___y_2867_ = v___y_2886_;
                    v___y_2868_ = v___y_2883_;
                    v___y_2869_ = v___y_2884_;
                    v___y_2870_ = v___y_2885_;
                    v___y_2871_ = v___x_2887_;
                    state = 6;
                    continue;
                } else {
                    v_a_2888_ = lean_ctor_get(v_initializationOptions_x3f_2839_, 0);
                    v_isSharedCheck_2895_ =
                        (!lean_is_exclusive(v_initializationOptions_x3f_2839_)) as u8;
                    if v_isSharedCheck_2895_ == 0 {
                        v___x_2890_ = v_initializationOptions_x3f_2839_;
                        v_isShared_2891_ = v_isSharedCheck_2895_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_2888_);
                        lean_dec(v_initializationOptions_x3f_2839_);
                        v___x_2890_ = lean_box(0);
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
                    v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
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
                if lean_obj_tag(v_rootUri_x3f_2837_) == 0 {
                    lean_dec_ref_known(v_rootUri_x3f_2837_, 1);
                    v___x_2901_ = lean_box(0);
                    v___y_2882_ = v___y_2897_;
                    v___y_2883_ = v___y_2898_;
                    v___y_2884_ = v___y_2900_;
                    v___y_2885_ = v___y_2899_;
                    v___y_2886_ = v___x_2901_;
                    state = 9;
                    continue;
                } else {
                    v_a_2902_ = lean_ctor_get(v_rootUri_x3f_2837_, 0);
                    v_isSharedCheck_2909_ = (!lean_is_exclusive(v_rootUri_x3f_2837_)) as u8;
                    if v_isSharedCheck_2909_ == 0 {
                        v___x_2904_ = v_rootUri_x3f_2837_;
                        v_isShared_2905_ = v_isSharedCheck_2909_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_2902_);
                        lean_dec(v_rootUri_x3f_2837_);
                        v___x_2904_ = lean_box(0);
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
                    v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
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
                if lean_obj_tag(v_clientInfo_x3f_2835_) == 0 {
                    lean_dec_ref_known(v_clientInfo_x3f_2835_, 1);
                    v___x_2914_ = lean_box(0);
                    v___y_2897_ = v___y_2911_;
                    v___y_2898_ = v___y_2913_;
                    v___y_2899_ = v___y_2912_;
                    v___y_2900_ = v___x_2914_;
                    state = 12;
                    continue;
                } else {
                    v_a_2915_ = lean_ctor_get(v_clientInfo_x3f_2835_, 0);
                    v_isSharedCheck_2922_ = (!lean_is_exclusive(v_clientInfo_x3f_2835_)) as u8;
                    if v_isSharedCheck_2922_ == 0 {
                        v___x_2917_ = v_clientInfo_x3f_2835_;
                        v_isShared_2918_ = v_isSharedCheck_2922_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_2915_);
                        lean_dec(v_clientInfo_x3f_2835_);
                        v___x_2917_ = lean_box(0);
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
                    v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
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
                if lean_obj_tag(v_processId_x3f_2833_) == 0 {
                    lean_dec_ref_known(v_processId_x3f_2833_, 1);
                    v___x_2927_ = lean_box(0);
                    v___y_2911_ = v___x_2926_;
                    v___y_2912_ = v___y_2924_;
                    v___y_2913_ = v___x_2927_;
                    state = 15;
                    continue;
                } else {
                    v_a_2928_ = lean_ctor_get(v_processId_x3f_2833_, 0);
                    v_isSharedCheck_2935_ = (!lean_is_exclusive(v_processId_x3f_2833_)) as u8;
                    if v_isSharedCheck_2935_ == 0 {
                        v___x_2930_ = v_processId_x3f_2833_;
                        v_isShared_2931_ = v_isSharedCheck_2935_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_2928_);
                        lean_dec(v_processId_x3f_2833_);
                        v___x_2930_ = lean_box(0);
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
                    v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
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
    mut v_x_2957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    v___x_2958_ = lean_unsigned_to_nat(0);
    return v___x_2958_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonInitializedParams___lam__0(
    mut v_x_2961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    v___x_2962_ = l_Lean_Lsp_instFromJsonInitializedParams___lam__0___closed__0;
    return v___x_2962_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonInitializedParams___lam__0___boxed(
    mut v_x_2963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2964_: *mut LeanObject = core::ptr::null_mut();
    v_res_2964_ = l_Lean_Lsp_instFromJsonInitializedParams___lam__0(v_x_2963_);
    lean_dec(v_x_2963_);
    return v_res_2964_;
}
pub unsafe fn l_Lean_Lsp_instToJsonInitializedParams___lam__0(
    mut v_x_2967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    v___x_2968_ = lean_box(0);
    return v___x_2968_;
}
pub unsafe fn l_Lean_Lsp_instToJsonServerInfo_toJson(
    mut v_x_2971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_version_x3f_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2976_: u8 = 0;
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2991_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_2972_ = lean_ctor_get(v_x_2971_, 0);
                v_version_x3f_2973_ = lean_ctor_get(v_x_2971_, 1);
                v_isSharedCheck_2991_ = (!lean_is_exclusive(v_x_2971_)) as u8;
                if v_isSharedCheck_2991_ == 0 {
                    v___x_2975_ = v_x_2971_;
                    v_isShared_2976_ = v_isSharedCheck_2991_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_version_x3f_2973_);
                    lean_inc(v_name_2972_);
                    lean_dec(v_x_2971_);
                    v___x_2975_ = lean_box(0);
                    v_isShared_2976_ = v_isSharedCheck_2991_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2977_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0;
                v___x_2978_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2978_, 0, v_name_2972_);
                if v_isShared_2976_ == 0 {
                    lean_ctor_set(v___x_2975_, 1, v___x_2978_);
                    lean_ctor_set(v___x_2975_, 0, v___x_2977_);
                    v___x_2980_ = v___x_2975_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2977_);
                    lean_ctor_set(v_reuseFailAlloc_2990_, 1, v___x_2978_);
                    v___x_2980_ = v_reuseFailAlloc_2990_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2981_ = lean_box(0);
                v___x_2982_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2982_, 0, v___x_2980_);
                lean_ctor_set(v___x_2982_, 1, v___x_2981_);
                v___x_2983_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1;
                v___x_2984_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__0(
                    v___x_2983_,
                    v_version_x3f_2973_,
                );
                v___x_2985_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2985_, 0, v___x_2984_);
                lean_ctor_set(v___x_2985_, 1, v___x_2981_);
                v___x_2986_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2986_, 0, v___x_2982_);
                lean_ctor_set(v___x_2986_, 1, v___x_2985_);
                v___x_2987_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2;
                v___x_2988_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_2986_, v___x_2987_);
                v___x_2989_ = l_Lean_Json_mkObj(v___x_2988_);
                lean_dec(v___x_2988_);
                return v___x_2989_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2() -> *mut LeanObject {
    let mut v___x_2999_: u8 = 0;
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    v___x_2999_ = 1;
    v___x_3000_ = l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__1;
    v___x_3001_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3000_, v___x_2999_);
    return v___x_3001_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3() -> *mut LeanObject {
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    v___x_3002_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5;
    v___x_3003_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2_once),
        _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__2,
    );
    v___x_3004_ = lean_string_append(v___x_3003_, v___x_3002_);
    return v___x_3004_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4() -> *mut LeanObject {
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    v___x_3005_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8_once),
        _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__8,
    );
    v___x_3006_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3,
    );
    v___x_3007_ = lean_string_append(v___x_3006_, v___x_3005_);
    return v___x_3007_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5() -> *mut LeanObject {
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    v___x_3008_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10;
    v___x_3009_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__4,
    );
    v___x_3010_ = lean_string_append(v___x_3009_, v___x_3008_);
    return v___x_3010_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6() -> *mut LeanObject {
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    v___x_3011_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14_once),
        _init_l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__14,
    );
    v___x_3012_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__3,
    );
    v___x_3013_ = lean_string_append(v___x_3012_, v___x_3011_);
    return v___x_3013_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7() -> *mut LeanObject {
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    v___x_3014_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10;
    v___x_3015_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__6,
    );
    v___x_3016_ = lean_string_append(v___x_3015_, v___x_3014_);
    return v___x_3016_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonServerInfo_fromJson(
    mut v_json_3017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3023_: u8 = 0;
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3029_: u8 = 0;
    let mut v_a_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3033_: u8 = 0;
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3037_: u8 = 0;
    let mut v_a_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3044_: u8 = 0;
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3050_: u8 = 0;
    let mut v_a_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3054_: u8 = 0;
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3058_: u8 = 0;
    let mut v_a_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3062_: u8 = 0;
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3067_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3018_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__0;
                lean_inc(v_json_3017_);
                v___x_3019_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__0(v_json_3017_, v___x_3018_);
                if lean_obj_tag(v___x_3019_) == 0 {
                    lean_dec(v_json_3017_);
                    v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
                    v_isSharedCheck_3029_ = (!lean_is_exclusive(v___x_3019_)) as u8;
                    if v_isSharedCheck_3029_ == 0 {
                        v___x_3022_ = v___x_3019_;
                        v_isShared_3023_ = v_isSharedCheck_3029_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3020_);
                        lean_dec(v___x_3019_);
                        v___x_3022_ = lean_box(0);
                        v_isShared_3023_ = v_isSharedCheck_3029_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_3019_) == 0 {
                        lean_dec(v_json_3017_);
                        v_a_3030_ = lean_ctor_get(v___x_3019_, 0);
                        v_isSharedCheck_3037_ = (!lean_is_exclusive(v___x_3019_)) as u8;
                        if v_isSharedCheck_3037_ == 0 {
                            v___x_3032_ = v___x_3019_;
                            v_isShared_3033_ = v_isSharedCheck_3037_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3030_);
                            lean_dec(v___x_3019_);
                            v___x_3032_ = lean_box(0);
                            v_isShared_3033_ = v_isSharedCheck_3037_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3038_ = lean_ctor_get(v___x_3019_, 0);
                        lean_inc(v_a_3038_);
                        lean_dec_ref_known(v___x_3019_, 1);
                        v___x_3039_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__1;
                        v___x_3040_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientInfo_fromJson_spec__1(v_json_3017_, v___x_3039_);
                        if lean_obj_tag(v___x_3040_) == 0 {
                            lean_dec(v_a_3038_);
                            v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
                            v_isSharedCheck_3050_ = (!lean_is_exclusive(v___x_3040_)) as u8;
                            if v_isSharedCheck_3050_ == 0 {
                                v___x_3043_ = v___x_3040_;
                                v_isShared_3044_ = v_isSharedCheck_3050_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_3041_);
                                lean_dec(v___x_3040_);
                                v___x_3043_ = lean_box(0);
                                v_isShared_3044_ = v_isSharedCheck_3050_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_3040_) == 0 {
                                lean_dec(v_a_3038_);
                                v_a_3051_ = lean_ctor_get(v___x_3040_, 0);
                                v_isSharedCheck_3058_ = (!lean_is_exclusive(v___x_3040_)) as u8;
                                if v_isSharedCheck_3058_ == 0 {
                                    v___x_3053_ = v___x_3040_;
                                    v_isShared_3054_ = v_isSharedCheck_3058_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_3051_);
                                    lean_dec(v___x_3040_);
                                    v___x_3053_ = lean_box(0);
                                    v_isShared_3054_ = v_isSharedCheck_3058_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_3059_ = lean_ctor_get(v___x_3040_, 0);
                                v_isSharedCheck_3067_ = (!lean_is_exclusive(v___x_3040_)) as u8;
                                if v_isSharedCheck_3067_ == 0 {
                                    v___x_3061_ = v___x_3040_;
                                    v_isShared_3062_ = v_isSharedCheck_3067_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_3059_);
                                    lean_dec(v___x_3040_);
                                    v___x_3061_ = lean_box(0);
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
                v___x_3024_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__5,
                );
                v___x_3025_ = lean_string_append(v___x_3024_, v_a_3020_);
                lean_dec(v_a_3020_);
                if v_isShared_3023_ == 0 {
                    lean_ctor_set(v___x_3022_, 0, v___x_3025_);
                    v___x_3027_ = v___x_3022_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3025_);
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
                    lean_ctor_set_tag(v___x_3032_, 0);
                    v___x_3035_ = v___x_3032_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
                    v___x_3035_ = v_reuseFailAlloc_3036_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3035_;
            }
            5 => {
                v___x_3045_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonServerInfo_fromJson___closed__7,
                );
                v___x_3046_ = lean_string_append(v___x_3045_, v_a_3041_);
                lean_dec(v_a_3041_);
                if v_isShared_3044_ == 0 {
                    lean_ctor_set(v___x_3043_, 0, v___x_3046_);
                    v___x_3048_ = v___x_3043_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3046_);
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
                    lean_ctor_set_tag(v___x_3053_, 0);
                    v___x_3056_ = v___x_3053_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
                    v___x_3056_ = v_reuseFailAlloc_3057_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3056_;
            }
            9 => {
                v___x_3063_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3063_, 0, v_a_3038_);
                lean_ctor_set(v___x_3063_, 1, v_a_3059_);
                if v_isShared_3062_ == 0 {
                    lean_ctor_set(v___x_3061_, 0, v___x_3063_);
                    v___x_3065_ = v___x_3061_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3063_);
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
    mut v_k_3070_: *mut LeanObject,
    mut v_x_3071_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3071_) == 0 {
        let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_k_3070_);
        v___x_3072_ = lean_box(0);
        return v___x_3072_;
    } else {
        let mut v_val_3073_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
        v_val_3073_ = lean_ctor_get(v_x_3071_, 0);
        lean_inc(v_val_3073_);
        lean_dec_ref_known(v_x_3071_, 1);
        v___x_3074_ = l_Lean_Lsp_instToJsonServerInfo_toJson(v_val_3073_);
        v___x_3075_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3075_, 0, v_k_3070_);
        lean_ctor_set(v___x_3075_, 1, v___x_3074_);
        v___x_3076_ = lean_box(0);
        v___x_3077_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3077_, 0, v___x_3075_);
        lean_ctor_set(v___x_3077_, 1, v___x_3076_);
        return v___x_3077_;
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonInitializeResult_toJson(
    mut v_x_3079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_capabilities_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_serverInfo_x3f_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3084_: u8 = 0;
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3099_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_capabilities_3080_ = lean_ctor_get(v_x_3079_, 0);
                v_serverInfo_x3f_3081_ = lean_ctor_get(v_x_3079_, 1);
                v_isSharedCheck_3099_ = (!lean_is_exclusive(v_x_3079_)) as u8;
                if v_isSharedCheck_3099_ == 0 {
                    v___x_3083_ = v_x_3079_;
                    v_isShared_3084_ = v_isSharedCheck_3099_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_serverInfo_x3f_3081_);
                    lean_inc(v_capabilities_3080_);
                    lean_dec(v_x_3079_);
                    v___x_3083_ = lean_box(0);
                    v_isShared_3084_ = v_isSharedCheck_3099_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3085_ = l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4;
                v___x_3086_ = l_Lean_Lsp_instToJsonServerCapabilities_toJson(v_capabilities_3080_);
                if v_isShared_3084_ == 0 {
                    lean_ctor_set(v___x_3083_, 1, v___x_3086_);
                    lean_ctor_set(v___x_3083_, 0, v___x_3085_);
                    v___x_3088_ = v___x_3083_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3085_);
                    lean_ctor_set(v_reuseFailAlloc_3098_, 1, v___x_3086_);
                    v___x_3088_ = v_reuseFailAlloc_3098_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3089_ = lean_box(0);
                v___x_3090_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3090_, 0, v___x_3088_);
                lean_ctor_set(v___x_3090_, 1, v___x_3089_);
                v___x_3091_ = l_Lean_Lsp_instToJsonInitializeResult_toJson___closed__0;
                v___x_3092_ =
                    l_Lean_Json_opt___at___00Lean_Lsp_instToJsonInitializeResult_toJson_spec__0(
                        v___x_3091_,
                        v_serverInfo_x3f_3081_,
                    );
                v___x_3093_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3093_, 0, v___x_3092_);
                lean_ctor_set(v___x_3093_, 1, v___x_3089_);
                v___x_3094_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3094_, 0, v___x_3090_);
                lean_ctor_set(v___x_3094_, 1, v___x_3093_);
                v___x_3095_ = l_Lean_Lsp_instToJsonClientInfo_toJson___closed__2;
                v___x_3096_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonClientInfo_toJson_spec__1(v___x_3094_, v___x_3095_);
                v___x_3097_ = l_Lean_Json_mkObj(v___x_3096_);
                lean_dec(v___x_3096_);
                return v___x_3097_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0(
    mut v_j_3102_: *mut LeanObject,
    mut v_k_3103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    v___x_3104_ = l_Lean_Json_getObjValD(v_j_3102_, v_k_3103_);
    v___x_3105_ = l_Lean_Lsp_instFromJsonServerCapabilities_fromJson(v___x_3104_);
    return v___x_3105_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0___boxed(
    mut v_j_3106_: *mut LeanObject,
    mut v_k_3107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3108_: *mut LeanObject = core::ptr::null_mut();
    v_res_3108_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0(
            v_j_3106_, v_k_3107_,
        );
    lean_dec_ref(v_k_3107_);
    return v_res_3108_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1(
    mut v_x_3111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3117_: u8 = 0;
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3121_: u8 = 0;
    let mut v_a_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3125_: u8 = 0;
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3130_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3111_) == 0 {
                    v___x_3112_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1___closed__0;
                    return v___x_3112_;
                } else {
                    v___x_3113_ = l_Lean_Lsp_instFromJsonServerInfo_fromJson(v_x_3111_);
                    if lean_obj_tag(v___x_3113_) == 0 {
                        v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
                        v_isSharedCheck_3121_ = (!lean_is_exclusive(v___x_3113_)) as u8;
                        if v_isSharedCheck_3121_ == 0 {
                            v___x_3116_ = v___x_3113_;
                            v_isShared_3117_ = v_isSharedCheck_3121_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3114_);
                            lean_dec(v___x_3113_);
                            v___x_3116_ = lean_box(0);
                            v_isShared_3117_ = v_isSharedCheck_3121_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3122_ = lean_ctor_get(v___x_3113_, 0);
                        v_isSharedCheck_3130_ = (!lean_is_exclusive(v___x_3113_)) as u8;
                        if v_isSharedCheck_3130_ == 0 {
                            v___x_3124_ = v___x_3113_;
                            v_isShared_3125_ = v_isSharedCheck_3130_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3122_);
                            lean_dec(v___x_3113_);
                            v___x_3124_ = lean_box(0);
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
                    v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
                    v___x_3119_ = v_reuseFailAlloc_3120_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3119_;
            }
            3 => {
                v___x_3126_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3126_, 0, v_a_3122_);
                if v_isShared_3125_ == 0 {
                    lean_ctor_set(v___x_3124_, 0, v___x_3126_);
                    v___x_3128_ = v___x_3124_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3126_);
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
    mut v_j_3131_: *mut LeanObject,
    mut v_k_3132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    v___x_3133_ = l_Lean_Json_getObjValD(v_j_3131_, v_k_3132_);
    v___x_3134_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1_spec__1(v___x_3133_);
    return v___x_3134_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1___boxed(
    mut v_j_3135_: *mut LeanObject,
    mut v_k_3136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3137_: *mut LeanObject = core::ptr::null_mut();
    v_res_3137_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1(
            v_j_3135_, v_k_3136_,
        );
    lean_dec_ref(v_k_3136_);
    return v_res_3137_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2() -> *mut LeanObject
{
    let mut v___x_3143_: u8 = 0;
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    v___x_3143_ = 1;
    v___x_3144_ = l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__1;
    v___x_3145_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3144_, v___x_3143_);
    return v___x_3145_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3() -> *mut LeanObject
{
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    v___x_3146_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__5;
    v___x_3147_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2_once),
        _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__2,
    );
    v___x_3148_ = lean_string_append(v___x_3147_, v___x_3146_);
    return v___x_3148_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5() -> *mut LeanObject
{
    let mut v___x_3151_: u8 = 0;
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    v___x_3151_ = 1;
    v___x_3152_ = l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__4;
    v___x_3153_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3152_, v___x_3151_);
    return v___x_3153_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6() -> *mut LeanObject
{
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    v___x_3154_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5_once),
        _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__5,
    );
    v___x_3155_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3,
    );
    v___x_3156_ = lean_string_append(v___x_3155_, v___x_3154_);
    return v___x_3156_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7() -> *mut LeanObject
{
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    v___x_3157_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10;
    v___x_3158_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__6,
    );
    v___x_3159_ = lean_string_append(v___x_3158_, v___x_3157_);
    return v___x_3159_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10()
-> *mut LeanObject {
    let mut v___x_3163_: u8 = 0;
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    v___x_3163_ = 1;
    v___x_3164_ = l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__9;
    v___x_3165_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3164_, v___x_3163_);
    return v___x_3165_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11()
-> *mut LeanObject {
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    v___x_3166_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10_once),
        _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__10,
    );
    v___x_3167_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__3,
    );
    v___x_3168_ = lean_string_append(v___x_3167_, v___x_3166_);
    return v___x_3168_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12()
-> *mut LeanObject {
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    v___x_3169_ = l_Lean_Lsp_instFromJsonClientInfo_fromJson___closed__10;
    v___x_3170_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11_once),
        _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__11,
    );
    v___x_3171_ = lean_string_append(v___x_3170_, v___x_3169_);
    return v___x_3171_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonInitializeResult_fromJson(
    mut v_json_3172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3178_: u8 = 0;
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3184_: u8 = 0;
    let mut v_a_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3188_: u8 = 0;
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3192_: u8 = 0;
    let mut v_a_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3199_: u8 = 0;
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3205_: u8 = 0;
    let mut v_a_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3209_: u8 = 0;
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3213_: u8 = 0;
    let mut v_a_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3217_: u8 = 0;
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3222_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3173_ = l_Lean_Lsp_instToJsonInitializeParams_toJson___closed__4;
                lean_inc(v_json_3172_);
                v___x_3174_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__0(v_json_3172_, v___x_3173_);
                if lean_obj_tag(v___x_3174_) == 0 {
                    lean_dec(v_json_3172_);
                    v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
                    v_isSharedCheck_3184_ = (!lean_is_exclusive(v___x_3174_)) as u8;
                    if v_isSharedCheck_3184_ == 0 {
                        v___x_3177_ = v___x_3174_;
                        v_isShared_3178_ = v_isSharedCheck_3184_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3175_);
                        lean_dec(v___x_3174_);
                        v___x_3177_ = lean_box(0);
                        v_isShared_3178_ = v_isSharedCheck_3184_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_3174_) == 0 {
                        lean_dec(v_json_3172_);
                        v_a_3185_ = lean_ctor_get(v___x_3174_, 0);
                        v_isSharedCheck_3192_ = (!lean_is_exclusive(v___x_3174_)) as u8;
                        if v_isSharedCheck_3192_ == 0 {
                            v___x_3187_ = v___x_3174_;
                            v_isShared_3188_ = v_isSharedCheck_3192_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3185_);
                            lean_dec(v___x_3174_);
                            v___x_3187_ = lean_box(0);
                            v_isShared_3188_ = v_isSharedCheck_3192_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3193_ = lean_ctor_get(v___x_3174_, 0);
                        lean_inc(v_a_3193_);
                        lean_dec_ref_known(v___x_3174_, 1);
                        v___x_3194_ = l_Lean_Lsp_instToJsonInitializeResult_toJson___closed__0;
                        v___x_3195_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonInitializeResult_fromJson_spec__1(v_json_3172_, v___x_3194_);
                        if lean_obj_tag(v___x_3195_) == 0 {
                            lean_dec(v_a_3193_);
                            v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
                            v_isSharedCheck_3205_ = (!lean_is_exclusive(v___x_3195_)) as u8;
                            if v_isSharedCheck_3205_ == 0 {
                                v___x_3198_ = v___x_3195_;
                                v_isShared_3199_ = v_isSharedCheck_3205_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_3196_);
                                lean_dec(v___x_3195_);
                                v___x_3198_ = lean_box(0);
                                v_isShared_3199_ = v_isSharedCheck_3205_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_3195_) == 0 {
                                lean_dec(v_a_3193_);
                                v_a_3206_ = lean_ctor_get(v___x_3195_, 0);
                                v_isSharedCheck_3213_ = (!lean_is_exclusive(v___x_3195_)) as u8;
                                if v_isSharedCheck_3213_ == 0 {
                                    v___x_3208_ = v___x_3195_;
                                    v_isShared_3209_ = v_isSharedCheck_3213_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_3206_);
                                    lean_dec(v___x_3195_);
                                    v___x_3208_ = lean_box(0);
                                    v_isShared_3209_ = v_isSharedCheck_3213_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_3214_ = lean_ctor_get(v___x_3195_, 0);
                                v_isSharedCheck_3222_ = (!lean_is_exclusive(v___x_3195_)) as u8;
                                if v_isSharedCheck_3222_ == 0 {
                                    v___x_3216_ = v___x_3195_;
                                    v_isShared_3217_ = v_isSharedCheck_3222_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_3214_);
                                    lean_dec(v___x_3195_);
                                    v___x_3216_ = lean_box(0);
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
                v___x_3179_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__7,
                );
                v___x_3180_ = lean_string_append(v___x_3179_, v_a_3175_);
                lean_dec(v_a_3175_);
                if v_isShared_3178_ == 0 {
                    lean_ctor_set(v___x_3177_, 0, v___x_3180_);
                    v___x_3182_ = v___x_3177_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3180_);
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
                    lean_ctor_set_tag(v___x_3187_, 0);
                    v___x_3190_ = v___x_3187_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_a_3185_);
                    v___x_3190_ = v_reuseFailAlloc_3191_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3190_;
            }
            5 => {
                v___x_3200_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonInitializeResult_fromJson___closed__12,
                );
                v___x_3201_ = lean_string_append(v___x_3200_, v_a_3196_);
                lean_dec(v_a_3196_);
                if v_isShared_3199_ == 0 {
                    lean_ctor_set(v___x_3198_, 0, v___x_3201_);
                    v___x_3203_ = v___x_3198_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3204_, 0, v___x_3201_);
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
                    lean_ctor_set_tag(v___x_3208_, 0);
                    v___x_3211_ = v___x_3208_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
                    v___x_3211_ = v_reuseFailAlloc_3212_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3211_;
            }
            9 => {
                v___x_3218_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3218_, 0, v_a_3193_);
                lean_ctor_set(v___x_3218_, 1, v_a_3214_);
                if v_isShared_3217_ == 0 {
                    lean_ctor_set(v___x_3216_, 0, v___x_3218_);
                    v___x_3220_ = v___x_3216_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3218_);
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
pub unsafe fn runtime_initialize_Lean_Data_Lsp_InitShutdown(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Lsp_Capabilities(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Workspace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Lsp_InitShutdown(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Lsp_InitShutdown(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Lsp_Capabilities(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_Lsp_Workspace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_InitShutdown(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Lsp_InitShutdown(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_Lsp_InitShutdown(builtin);
}
