// Lean compiler output
// Module: Lean.Server.Rpc.Basic
// Imports: Init.Dynamic Lean.Data.Json.FromToJson.Basic
use crate::r#gen::Init::Control::Except::{
    l_ExceptT_bind, l_ExceptT_instMonad___redArg___lam__1, l_ExceptT_instMonad___redArg___lam__4,
    l_ExceptT_instMonad___redArg___lam__7, l_ExceptT_instMonad___redArg___lam__9, l_ExceptT_map,
    l_ExceptT_pure, l_ExceptT_tryCatch, l_instMonadExceptOfExceptTOfMonad___redArg___lam__0,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::State::{
    l_StateT_bind, l_StateT_instMonad___redArg___lam__1, l_StateT_instMonad___redArg___lam__4,
    l_StateT_instMonad___redArg___lam__7, l_StateT_instMonad___redArg___lam__9, l_StateT_map,
    l_StateT_pure,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_eraseIdx___redArg,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Data::UInt::Basic::l_USize_toUInt64___boxed;
use crate::r#gen::Init::Dynamic::{
    initialize_Init_Dynamic, l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg,
    l___private_Init_Dynamic_0__Dynamic_typeNameImpl, runtime_initialize_Init_Dynamic,
};
use crate::r#gen::Init::Prelude::{
    l_MonadExcept_ofExcept___redArg, l_ReaderT_instMonad___redArg, l_id___boxed,
    l_instBEqOfDecidableEq___redArg___lam__0___boxed, l_instDecidableEqUSize___boxed,
    l_instMonadExceptOfMonadExceptOf___redArg, l_panic___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::Json::Basic::l_Lean_Json_mkObj;
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::{
    initialize_Lean_Data_Json_FromToJson_Basic, l_Array_fromJson_x3f___redArg,
    l_Array_toJson___redArg, l_Lean_Json_getObjValAs_x3f___redArg, l_Lean_Json_getTag_x3f,
    l_Lean_bignumToJson, l_Lean_instFromJsonJson___lam__0, l_Option_fromJson_x3f___redArg,
    l_Option_toJson___redArg, l_Prod_fromJson_x3f___redArg, l_Prod_toJson___redArg,
    l_USize_fromJson_x3f, runtime_initialize_Lean_Data_Json_FromToJson_Basic,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_find_x3f___redArg,
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_insert___redArg, l_Lean_PersistentHashMap_isUnaryNode___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_size;
use crate::lean_imports_rs::Init::Data::Array::Set::{lean_array_fset, lean_array_set};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_to_uint64,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
    lean_nat_sub, lean_string_dec_eq, lean_uint64_mix_hash, lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_mk_ref, lean_st_ref_set, lean_st_ref_take};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_box_uint64, lean_box_usize, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_get_usize, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_get_value,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
    lean_usize_once,
};
static mut l_Lean_Lsp_instInhabitedRpcRef_default___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instInhabitedRpcRef_default___closed__0: usize = 0;
pub static mut l_Lean_Lsp_instInhabitedRpcRef_default: usize = 0;
pub static mut l_Lean_Lsp_instInhabitedRpcRef: usize = 0;
pub static l_Lean_Lsp_instBEqRpcRef___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instBEqRpcRef_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instBEqRpcRef___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqRpcRef___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instBEqRpcRef: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqRpcRef___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instHashableRpcRef___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instHashableRpcRef_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instHashableRpcRef___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instHashableRpcRef___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instHashableRpcRef: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instHashableRpcRef___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instToStringRpcRef___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToStringRpcRef___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToStringRpcRef___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToStringRpcRef___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToStringRpcRef: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToStringRpcRef___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__0_value: LeanStringObject<23> =
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
            110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 97, 103, 32, 102,
            111, 117, 110, 100, 0,
        ],
    };
static mut l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__1_value: LeanCtorObject<1> =
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
            l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__2_value: LeanStringObject<3> =
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
        m_data: [118, 49, 0],
    };
static mut l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__3_value: LeanStringObject<3> =
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
        m_data: [118, 48, 0],
    };
static mut l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__4_value: LeanStringObject<33> =
    LeanStringObject {
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
            110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 99, 111, 110, 115, 116,
            114, 117, 99, 116, 111, 114, 32, 109, 97, 116, 99, 104, 101, 100, 0,
        ],
    };
static mut l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__5_value: LeanCtorObject<1> =
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
            l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__4_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__6_value: LeanCtorObject<1> =
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
static mut l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__7_value: LeanCtorObject<1> =
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
static mut l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonRpcWireFormat___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonRpcWireFormat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcWireFormat___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonRpcWireFormat: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonRpcWireFormat___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonRpcWireFormat_toJson___closed__0_value: LeanCtorObject<1> =
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
            l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__3_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Lsp_instToJsonRpcWireFormat_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRpcWireFormat_toJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonRpcWireFormat_toJson___closed__1_value: LeanCtorObject<1> =
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
            l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__2_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Lsp_instToJsonRpcWireFormat_toJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRpcWireFormat_toJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonRpcWireFormat___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonRpcWireFormat_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonRpcWireFormat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRpcWireFormat___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonRpcWireFormat: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonRpcWireFormat___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_RpcWireFormat_refFieldName___closed__0_value: LeanStringObject<2> =
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
        m_data: [112, 0],
    };
static mut l_Lean_Lsp_RpcWireFormat_refFieldName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_RpcWireFormat_refFieldName___closed__1_value: LeanStringObject<9> =
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
        m_data: [95, 95, 114, 112, 99, 114, 101, 102, 0],
    };
static mut l_Lean_Lsp_RpcWireFormat_refFieldName___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn___boxed__const__1_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + core::mem::size_of::<usize>()*1) as u16, other: 1, tag: 0 }, m_objs: [(1 as *mut LeanObject)] };
pub static mut l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn___boxed__const__1_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn___boxed__const__1_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l_Lean_Server_rpcStoreRef___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_USize_toUInt64___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Server_rpcStoreRef___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_rpcStoreRef___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_Server_rpcStoreRef___redArg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_rpcStoreRef___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_rpcStoreRef___redArg___closed__2_value: LeanStringObject<22> =
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
            76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 82, 112, 99, 46, 66, 97, 115,
            105, 99, 0,
        ],
    };
static mut l_Lean_Server_rpcStoreRef___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_rpcStoreRef___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_Server_rpcStoreRef___redArg___closed__3_value: LeanStringObject<24> =
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
            76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 114, 112, 99, 83, 116, 111, 114,
            101, 82, 101, 102, 0,
        ],
    };
static mut l_Lean_Server_rpcStoreRef___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_rpcStoreRef___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lean_Server_rpcStoreRef___redArg___closed__4_value: LeanStringObject<54> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 54,
        m_capacity: 54,
        m_length: 53,
        m_data: [
            70, 111, 117, 110, 100, 32, 111, 98, 106, 101, 99, 116, 32, 73, 68, 32, 105, 110, 32,
            96, 114, 101, 102, 115, 66, 121, 73, 100, 96, 32, 98, 117, 116, 32, 110, 111, 116, 32,
            105, 110, 32, 96, 97, 108, 105, 118, 101, 82, 101, 102, 115, 96, 46, 0,
        ],
    };
static mut l_Lean_Server_rpcStoreRef___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_rpcStoreRef___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_Server_rpcStoreRef___redArg___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_rpcStoreRef___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Server_rpcStoreRef___redArg___boxed__const__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_rpcGetRef___redArg___closed__0_value: LeanStringObject<38> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 38,
        m_capacity: 38,
        m_length: 37,
        m_data: [
            82, 80, 67, 32, 99, 97, 108, 108, 32, 116, 121, 112, 101, 32, 109, 105, 115, 109, 97,
            116, 99, 104, 32, 105, 110, 32, 114, 101, 102, 101, 114, 101, 110, 99, 101, 32, 39, 0,
        ],
    };
static mut l_Lean_Server_rpcGetRef___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_rpcGetRef___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Server_rpcGetRef___redArg___closed__1_value: LeanStringObject<13> =
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
        m_data: [39, 10, 101, 120, 112, 101, 99, 116, 101, 100, 32, 39, 0],
    };
static mut l_Lean_Server_rpcGetRef___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_rpcGetRef___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_Server_rpcGetRef___redArg___closed__2_value: LeanStringObject<4> =
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
        m_data: [39, 44, 32, 0],
    };
static mut l_Lean_Server_rpcGetRef___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_rpcGetRef___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_Server_rpcGetRef___redArg___closed__3_value: LeanStringObject<6> =
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
        m_data: [103, 111, 116, 32, 39, 0],
    };
static mut l_Lean_Server_rpcGetRef___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_rpcGetRef___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lean_Server_rpcGetRef___redArg___closed__4_value: LeanStringObject<2> =
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
        m_data: [39, 0],
    };
static mut l_Lean_Server_rpcGetRef___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_rpcGetRef___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lean_Server_rpcGetRef___redArg___closed__5_value: LeanStringObject<16> =
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
            82, 80, 67, 32, 114, 101, 102, 101, 114, 101, 110, 99, 101, 32, 39, 0,
        ],
    };
static mut l_Lean_Server_rpcGetRef___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_rpcGetRef___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lean_Server_rpcGetRef___redArg___closed__6_value: LeanStringObject<15> =
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
            39, 32, 105, 115, 32, 110, 111, 116, 32, 118, 97, 108, 105, 100, 0,
        ],
    };
static mut l_Lean_Server_rpcGetRef___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_rpcGetRef___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__7_value:
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
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__1_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__8_value:
    LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__7_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__2_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__4_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__5_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9_value:
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
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__8_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__6_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9_value)
        as *mut LeanObject;
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_instRpcEncodableOption___redArg___lam__1___closed__0_value:
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
static mut l_Lean_Server_instRpcEncodableOption___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instRpcEncodableOption___redArg___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Server_instRpcEncodableOption___redArg___closed__0_value: LeanClosureObject<1> =
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
        m_fun: l_id___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Server_instRpcEncodableOption___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instRpcEncodableOption___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Server_instRpcEncodableOption___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instFromJsonJson___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Server_instRpcEncodableOption___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instRpcEncodableOption___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Server_instRpcEncodableArray___redArg___closed__0_value: LeanClosureObject<1> =
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
        m_fun: l_StateT_instMonad___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [core::ptr::addr_of!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Server_instRpcEncodableArray___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instRpcEncodableArray___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Server_instRpcEncodableArray___redArg___closed__1_value: LeanClosureObject<1> =
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
        m_fun: l_StateT_instMonad___redArg___lam__4 as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [core::ptr::addr_of!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Server_instRpcEncodableArray___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instRpcEncodableArray___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Server_instRpcEncodableArray___redArg___closed__2_value: LeanClosureObject<1> =
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
        m_fun: l_StateT_instMonad___redArg___lam__7 as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [core::ptr::addr_of!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Server_instRpcEncodableArray___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instRpcEncodableArray___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Server_instRpcEncodableArray___redArg___closed__3_value: LeanClosureObject<1> =
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
        m_fun: l_StateT_instMonad___redArg___lam__9 as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [core::ptr::addr_of!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Server_instRpcEncodableArray___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instRpcEncodableArray___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Server_instRpcEncodableArray___redArg___closed__4_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_StateT_map as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9_value
            ) as *mut LeanObject,
        ],
    };
static mut l_Lean_Server_instRpcEncodableArray___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instRpcEncodableArray___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Server_instRpcEncodableArray___redArg___closed__5_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Server_instRpcEncodableArray___redArg___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Server_instRpcEncodableArray___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Server_instRpcEncodableArray___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instRpcEncodableArray___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Server_instRpcEncodableArray___redArg___closed__6_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_StateT_pure as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9_value
            ) as *mut LeanObject,
        ],
    };
static mut l_Lean_Server_instRpcEncodableArray___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instRpcEncodableArray___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Server_instRpcEncodableArray___redArg___closed__7_value: LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Lean_Server_instRpcEncodableArray___redArg___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Server_instRpcEncodableArray___redArg___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Server_instRpcEncodableArray___redArg___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Server_instRpcEncodableArray___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Server_instRpcEncodableArray___redArg___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Server_instRpcEncodableArray___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instRpcEncodableArray___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Server_instRpcEncodableArray___redArg___closed__8_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_StateT_bind as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9_value
            ) as *mut LeanObject,
        ],
    };
static mut l_Lean_Server_instRpcEncodableArray___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instRpcEncodableArray___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Server_instRpcEncodableArray___redArg___closed__9_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Server_instRpcEncodableArray___redArg___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Server_instRpcEncodableArray___redArg___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Server_instRpcEncodableArray___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instRpcEncodableArray___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_USize_fromJson_x3f as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg___closed__0_value
) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Lsp_instInhabitedRpcRef_default___closed__0() -> usize {
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: usize = 0;
    v___x_1487_ = lean_unsigned_to_nat(0);
    v___x_1488_ = lean_usize_of_nat(v___x_1487_);
    return v___x_1488_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedRpcRef_default() -> usize {
    let mut v___x_1489_: usize = 0;
    v___x_1489_ = lean_usize_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instInhabitedRpcRef_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instInhabitedRpcRef_default___closed__0_once),
        _init_l_Lean_Lsp_instInhabitedRpcRef_default___closed__0,
    );
    return v___x_1489_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedRpcRef() -> usize {
    let mut v___x_1490_: usize = 0;
    v___x_1490_ = l_Lean_Lsp_instInhabitedRpcRef_default;
    return v___x_1490_;
}
pub unsafe fn l_Lean_Lsp_instBEqRpcRef_beq(mut v_x_1491_: usize, mut v_x_1492_: usize) -> u8 {
    let mut v___x_1493_: u8 = 0;
    v___x_1493_ = lean_usize_dec_eq(v_x_1491_, v_x_1492_);
    return v___x_1493_;
}
pub unsafe fn l_Lean_Lsp_instBEqRpcRef_beq___boxed(
    mut v_x_1494_: *mut LeanObject,
    mut v_x_1495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_26__boxed_1496_: usize = 0;
    let mut v_x_27__boxed_1497_: usize = 0;
    let mut v_res_1498_: u8 = 0;
    let mut v_r_1499_: *mut LeanObject = core::ptr::null_mut();
    v_x_26__boxed_1496_ = lean_unbox_usize(v_x_1494_);
    lean_dec(v_x_1494_);
    v_x_27__boxed_1497_ = lean_unbox_usize(v_x_1495_);
    lean_dec(v_x_1495_);
    v_res_1498_ = l_Lean_Lsp_instBEqRpcRef_beq(v_x_26__boxed_1496_, v_x_27__boxed_1497_);
    v_r_1499_ = lean_box((v_res_1498_) as usize);
    return v_r_1499_;
}
pub unsafe fn l_Lean_Lsp_instHashableRpcRef_hash(mut v_x_1502_: usize) -> u64 {
    let mut v___x_1503_: u64 = 0;
    let mut v___x_1504_: u64 = 0;
    let mut v___x_1505_: u64 = 0;
    v___x_1503_ = 0u64;
    v___x_1504_ = lean_usize_to_uint64(v_x_1502_);
    v___x_1505_ = lean_uint64_mix_hash(v___x_1503_, v___x_1504_);
    return v___x_1505_;
}
pub unsafe fn l_Lean_Lsp_instHashableRpcRef_hash___boxed(
    mut v_x_1506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_26__boxed_1507_: usize = 0;
    let mut v_res_1508_: u64 = 0;
    let mut v_r_1509_: *mut LeanObject = core::ptr::null_mut();
    v_x_26__boxed_1507_ = lean_unbox_usize(v_x_1506_);
    lean_dec(v_x_1506_);
    v_res_1508_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_26__boxed_1507_);
    v_r_1509_ = lean_box_uint64(v_res_1508_);
    return v_r_1509_;
}
pub unsafe fn l_Lean_Lsp_instToStringRpcRef___lam__0(mut v_r_1512_: usize) -> *mut LeanObject {
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    v___x_1513_ = lean_usize_to_nat(v_r_1512_);
    v___x_1514_ = l_Nat_reprFast(v___x_1513_);
    return v___x_1514_;
}
pub unsafe fn l_Lean_Lsp_instToStringRpcRef___lam__0___boxed(
    mut v_r_1515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_boxed_1516_: usize = 0;
    let mut v_res_1517_: *mut LeanObject = core::ptr::null_mut();
    v_r_boxed_1516_ = lean_unbox_usize(v_r_1515_);
    lean_dec(v_r_1515_);
    v_res_1517_ = l_Lean_Lsp_instToStringRpcRef___lam__0(v_r_boxed_1516_);
    return v_res_1517_;
}
pub unsafe fn l_Lean_Lsp_RpcWireFormat_ctorIdx(mut v_x_1520_: u8) -> *mut LeanObject {
    if v_x_1520_ == 0 {
        let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
        v___x_1521_ = lean_unsigned_to_nat(0);
        return v___x_1521_;
    } else {
        let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
        v___x_1522_ = lean_unsigned_to_nat(1);
        return v___x_1522_;
    }
}
pub unsafe fn l_Lean_Lsp_RpcWireFormat_ctorIdx___boxed(
    mut v_x_1523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_1524_: u8 = 0;
    let mut v_res_1525_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_1524_ = (lean_unbox(v_x_1523_) as u8);
    v_res_1525_ = l_Lean_Lsp_RpcWireFormat_ctorIdx(v_x_boxed_1524_);
    return v_res_1525_;
}
pub unsafe fn l_Lean_Lsp_RpcWireFormat_toCtorIdx(mut v_x_1526_: u8) -> *mut LeanObject {
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    v___x_1527_ = l_Lean_Lsp_RpcWireFormat_ctorIdx(v_x_1526_);
    return v___x_1527_;
}
pub unsafe fn l_Lean_Lsp_RpcWireFormat_toCtorIdx___boxed(
    mut v_x_1528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_1529_: u8 = 0;
    let mut v_res_1530_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1529_ = (lean_unbox(v_x_1528_) as u8);
    v_res_1530_ = l_Lean_Lsp_RpcWireFormat_toCtorIdx(v_x_4__boxed_1529_);
    return v_res_1530_;
}
pub unsafe fn l_Lean_Lsp_RpcWireFormat_ctorElim___redArg(
    mut v_k_1531_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_1531_);
    return v_k_1531_;
}
pub unsafe fn l_Lean_Lsp_RpcWireFormat_ctorElim___redArg___boxed(
    mut v_k_1532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1533_: *mut LeanObject = core::ptr::null_mut();
    v_res_1533_ = l_Lean_Lsp_RpcWireFormat_ctorElim___redArg(v_k_1532_);
    lean_dec(v_k_1532_);
    return v_res_1533_;
}
pub unsafe fn l_Lean_Lsp_RpcWireFormat_ctorElim(
    mut v_motive_1534_: *mut LeanObject,
    mut v_ctorIdx_1535_: *mut LeanObject,
    mut v_t_1536_: u8,
    mut v_h_1537_: *mut LeanObject,
    mut v_k_1538_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_1538_);
    return v_k_1538_;
}
pub unsafe fn l_Lean_Lsp_RpcWireFormat_ctorElim___boxed(
    mut v_motive_1539_: *mut LeanObject,
    mut v_ctorIdx_1540_: *mut LeanObject,
    mut v_t_1541_: *mut LeanObject,
    mut v_h_1542_: *mut LeanObject,
    mut v_k_1543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1544_: u8 = 0;
    let mut v_res_1545_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1544_ = (lean_unbox(v_t_1541_) as u8);
    v_res_1545_ = l_Lean_Lsp_RpcWireFormat_ctorElim(
        v_motive_1539_,
        v_ctorIdx_1540_,
        v_t_boxed_1544_,
        v_h_1542_,
        v_k_1543_,
    );
    lean_dec(v_k_1543_);
    lean_dec(v_ctorIdx_1540_);
    return v_res_1545_;
}
pub unsafe fn l_Lean_Lsp_RpcWireFormat_v0_elim___redArg(
    mut v_v0_1546_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_v0_1546_);
    return v_v0_1546_;
}
pub unsafe fn l_Lean_Lsp_RpcWireFormat_v0_elim___redArg___boxed(
    mut v_v0_1547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1548_: *mut LeanObject = core::ptr::null_mut();
    v_res_1548_ = l_Lean_Lsp_RpcWireFormat_v0_elim___redArg(v_v0_1547_);
    lean_dec(v_v0_1547_);
    return v_res_1548_;
}
pub unsafe fn l_Lean_Lsp_RpcWireFormat_v0_elim(
    mut v_motive_1549_: *mut LeanObject,
    mut v_t_1550_: u8,
    mut v_h_1551_: *mut LeanObject,
    mut v_v0_1552_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_v0_1552_);
    return v_v0_1552_;
}
pub unsafe fn l_Lean_Lsp_RpcWireFormat_v0_elim___boxed(
    mut v_motive_1553_: *mut LeanObject,
    mut v_t_1554_: *mut LeanObject,
    mut v_h_1555_: *mut LeanObject,
    mut v_v0_1556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1557_: u8 = 0;
    let mut v_res_1558_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1557_ = (lean_unbox(v_t_1554_) as u8);
    v_res_1558_ =
        l_Lean_Lsp_RpcWireFormat_v0_elim(v_motive_1553_, v_t_boxed_1557_, v_h_1555_, v_v0_1556_);
    lean_dec(v_v0_1556_);
    return v_res_1558_;
}
pub unsafe fn l_Lean_Lsp_RpcWireFormat_v1_elim___redArg(
    mut v_v1_1559_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_v1_1559_);
    return v_v1_1559_;
}
pub unsafe fn l_Lean_Lsp_RpcWireFormat_v1_elim___redArg___boxed(
    mut v_v1_1560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1561_: *mut LeanObject = core::ptr::null_mut();
    v_res_1561_ = l_Lean_Lsp_RpcWireFormat_v1_elim___redArg(v_v1_1560_);
    lean_dec(v_v1_1560_);
    return v_res_1561_;
}
pub unsafe fn l_Lean_Lsp_RpcWireFormat_v1_elim(
    mut v_motive_1562_: *mut LeanObject,
    mut v_t_1563_: u8,
    mut v_h_1564_: *mut LeanObject,
    mut v_v1_1565_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_v1_1565_);
    return v_v1_1565_;
}
pub unsafe fn l_Lean_Lsp_RpcWireFormat_v1_elim___boxed(
    mut v_motive_1566_: *mut LeanObject,
    mut v_t_1567_: *mut LeanObject,
    mut v_h_1568_: *mut LeanObject,
    mut v_v1_1569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1570_: u8 = 0;
    let mut v_res_1571_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1570_ = (lean_unbox(v_t_1567_) as u8);
    v_res_1571_ =
        l_Lean_Lsp_RpcWireFormat_v1_elim(v_motive_1566_, v_t_boxed_1570_, v_h_1568_, v_v1_1569_);
    lean_dec(v_v1_1569_);
    return v_res_1571_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson(
    mut v_json_1586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    v___x_1587_ = l_Lean_Json_getTag_x3f(v_json_1586_);
    if lean_obj_tag(v___x_1587_) == 0 {
        let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
        v___x_1588_ = l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__1;
        return v___x_1588_;
    } else {
        let mut v_val_1589_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1591_: u8 = 0;
        v_val_1589_ = lean_ctor_get(v___x_1587_, 0);
        lean_inc(v_val_1589_);
        lean_dec_ref_known(v___x_1587_, 1);
        v___x_1590_ = l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__2;
        v___x_1591_ = lean_string_dec_eq(v_val_1589_, v___x_1590_);
        if v___x_1591_ == 0 {
            let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1593_: u8 = 0;
            v___x_1592_ = l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__3;
            v___x_1593_ = lean_string_dec_eq(v_val_1589_, v___x_1592_);
            lean_dec(v_val_1589_);
            if v___x_1593_ == 0 {
                let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
                v___x_1594_ = l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__5;
                return v___x_1594_;
            } else {
                let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
                v___x_1595_ = l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__6;
                return v___x_1595_;
            }
        } else {
            let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_val_1589_);
            v___x_1596_ = l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__7;
            return v___x_1596_;
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonRpcWireFormat_toJson(mut v_x_1603_: u8) -> *mut LeanObject {
    if v_x_1603_ == 0 {
        let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
        v___x_1604_ = l_Lean_Lsp_instToJsonRpcWireFormat_toJson___closed__0;
        return v___x_1604_;
    } else {
        let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
        v___x_1605_ = l_Lean_Lsp_instToJsonRpcWireFormat_toJson___closed__1;
        return v___x_1605_;
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonRpcWireFormat_toJson___boxed(
    mut v_x_1606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_44__boxed_1607_: u8 = 0;
    let mut v_res_1608_: *mut LeanObject = core::ptr::null_mut();
    v_x_44__boxed_1607_ = (lean_unbox(v_x_1606_) as u8);
    v_res_1608_ = l_Lean_Lsp_instToJsonRpcWireFormat_toJson(v_x_44__boxed_1607_);
    return v_res_1608_;
}
pub unsafe fn l_Lean_Lsp_RpcWireFormat_refFieldName(mut v_x_1613_: u8) -> *mut LeanObject {
    if v_x_1613_ == 0 {
        let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
        v___x_1614_ = l_Lean_Lsp_RpcWireFormat_refFieldName___closed__0;
        return v___x_1614_;
    } else {
        let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
        v___x_1615_ = l_Lean_Lsp_RpcWireFormat_refFieldName___closed__1;
        return v___x_1615_;
    }
}
pub unsafe fn l_Lean_Lsp_RpcWireFormat_refFieldName___boxed(
    mut v_x_1616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_22__boxed_1617_: u8 = 0;
    let mut v_res_1618_: *mut LeanObject = core::ptr::null_mut();
    v_x_22__boxed_1617_ = (lean_unbox(v_x_1616_) as u8);
    v_res_1618_ = l_Lean_Lsp_RpcWireFormat_refFieldName(v_x_22__boxed_1617_);
    return v_res_1618_;
}
pub unsafe fn l_Lean_Server_instInhabitedWithRpcRef_default___redArg(
    mut v_inst_1619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1620_: usize = 0;
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    v___x_1620_ = lean_usize_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instInhabitedRpcRef_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instInhabitedRpcRef_default___closed__0_once),
        _init_l_Lean_Lsp_instInhabitedRpcRef_default___closed__0,
    );
    v___x_1621_ = lean_alloc_ctor(0, 1, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1621_, 0, v_inst_1619_);
    lean_ctor_set_usize(v___x_1621_, 1, v___x_1620_);
    return v___x_1621_;
}
pub unsafe fn l_Lean_Server_instInhabitedWithRpcRef_default(
    mut v_00_u03b1_1622_: *mut LeanObject,
    mut v_inst_1623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    v___x_1624_ = l_Lean_Server_instInhabitedWithRpcRef_default___redArg(v_inst_1623_);
    return v___x_1624_;
}
pub unsafe fn l_Lean_Server_instInhabitedWithRpcRef___redArg(
    mut v_inst_1625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    v___x_1626_ = l_Lean_Server_instInhabitedWithRpcRef_default___redArg(v_inst_1625_);
    return v___x_1626_;
}
pub unsafe fn l_Lean_Server_instInhabitedWithRpcRef(
    mut v_a_1627_: *mut LeanObject,
    mut v_inst_1628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    v___x_1629_ = l_Lean_Server_instInhabitedWithRpcRef_default___redArg(v_inst_1628_);
    return v___x_1629_;
}
pub unsafe fn l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    v___x_1633_ = l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn___boxed__const__1_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_;
    v___x_1634_ = lean_st_mk_ref(v___x_1633_);
    v___x_1635_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1635_, 0, v___x_1634_);
    return v___x_1635_;
}
pub unsafe fn l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2____boxed(
    mut v_a_1636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1637_: *mut LeanObject = core::ptr::null_mut();
    v_res_1637_ = l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_();
    return v_res_1637_;
}
pub unsafe fn l_Lean_Server_WithRpcRef_mk___redArg(
    mut v_val_1638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: usize = 0;
    let mut v___x_1643_: usize = 0;
    let mut v___x_1644_: usize = 0;
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: usize = 0;
    v___x_1640_ = l_Lean_Server_freshWithRpcRefId;
    v___x_1641_ = lean_st_ref_take(v___x_1640_);
    v___x_1642_ = 1usize;
    v___x_1643_ = lean_unbox_usize(v___x_1641_);
    v___x_1644_ = lean_usize_add(v___x_1643_, v___x_1642_);
    v___x_1645_ = lean_box_usize(v___x_1644_);
    v___x_1646_ = lean_st_ref_set(v___x_1640_, v___x_1645_);
    v___x_1647_ = lean_alloc_ctor(0, 1, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1647_, 0, v_val_1638_);
    v___x_1648_ = lean_unbox_usize(v___x_1641_);
    lean_dec(v___x_1641_);
    lean_ctor_set_usize(v___x_1647_, 1, v___x_1648_);
    return v___x_1647_;
}
pub unsafe fn l_Lean_Server_WithRpcRef_mk___redArg___boxed(
    mut v_val_1649_: *mut LeanObject,
    mut v_a_1650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1651_: *mut LeanObject = core::ptr::null_mut();
    v_res_1651_ = l_Lean_Server_WithRpcRef_mk___redArg(v_val_1649_);
    return v_res_1651_;
}
pub unsafe fn l_Lean_Server_WithRpcRef_mk(
    mut v_00_u03b1_1652_: *mut LeanObject,
    mut v_val_1653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    v___x_1655_ = l_Lean_Server_WithRpcRef_mk___redArg(v_val_1653_);
    return v___x_1655_;
}
pub unsafe fn l_Lean_Server_WithRpcRef_mk___boxed(
    mut v_00_u03b1_1656_: *mut LeanObject,
    mut v_val_1657_: *mut LeanObject,
    mut v_a_1658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1659_: *mut LeanObject = core::ptr::null_mut();
    v_res_1659_ = l_Lean_Server_WithRpcRef_mk(v_00_u03b1_1656_, v_val_1657_);
    return v_res_1659_;
}
pub unsafe fn _init_l_Lean_Server_rpcStoreRef___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1662_: *mut LeanObject = core::ptr::null_mut();
    v___x_1661_ = lean_alloc_closure(
        l_instDecidableEqUSize___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_1662_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1662_, 0, v___x_1661_);
    return v___f_1662_;
}
pub unsafe fn _init_l_Lean_Server_rpcStoreRef___redArg___closed__5() -> *mut LeanObject {
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    v___x_1666_ = l_Lean_Server_rpcStoreRef___redArg___closed__4;
    v___x_1667_ = lean_unsigned_to_nat(15);
    v___x_1668_ = lean_unsigned_to_nat(132);
    v___x_1669_ = l_Lean_Server_rpcStoreRef___redArg___closed__3;
    v___x_1670_ = l_Lean_Server_rpcStoreRef___redArg___closed__2;
    v___x_1671_ = l_mkPanicMessageWithDecl(
        v___x_1670_,
        v___x_1669_,
        v___x_1668_,
        v___x_1667_,
        v___x_1666_,
    );
    return v___x_1671_;
}
pub unsafe fn _init_l_Lean_Server_rpcStoreRef___redArg___boxed__const__1() -> *mut LeanObject {
    let mut v___x_1672_: usize = 0;
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    v___x_1672_ = l_Lean_Lsp_instInhabitedRpcRef_default;
    v___x_1673_ = lean_box_usize(v___x_1672_);
    return v___x_1673_;
}
pub unsafe fn l_Lean_Server_rpcStoreRef___redArg(
    mut v_inst_1674_: *mut LeanObject,
    mut v_obj_1675_: *mut LeanObject,
    mut v_a_1676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_aliveRefs_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_refsById_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextRef_1679_: usize = 0;
    let mut v_wireFormat_1680_: u8 = 0;
    let mut v_val_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_1682_: usize = 0;
    let mut v___f_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1691_: u8 = 0;
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: usize = 0;
    let mut v___x_1701_: usize = 0;
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1707_: u8 = 0;
    let mut v_unused_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1714_: u8 = 0;
    let mut v_val_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_obj_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_1717_: usize = 0;
    let mut v_rc_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1721_: u8 = 0;
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1732_: u8 = 0;
    let mut v_isSharedCheck_1733_: u8 = 0;
    let mut v_unused_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_aliveRefs_1677_ = lean_ctor_get(v_a_1676_, 0);
                v_refsById_1678_ = lean_ctor_get(v_a_1676_, 1);
                v_nextRef_1679_ = lean_ctor_get_usize(v_a_1676_, 2);
                v_wireFormat_1680_ = lean_ctor_get_uint8(
                    v_a_1676_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_val_1681_ = lean_ctor_get(v_obj_1675_, 0);
                v_id_1682_ = lean_ctor_get_usize(v_obj_1675_, 1);
                v___f_1683_ = l_Lean_Server_rpcStoreRef___redArg___closed__0;
                v___x_1684_ = l_Lean_Lsp_instBEqRpcRef___closed__0;
                v___x_1685_ = l_Lean_Lsp_instHashableRpcRef___closed__0;
                v___f_1686_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Server_rpcStoreRef___redArg___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Server_rpcStoreRef___redArg___closed__1_once),
                    _init_l_Lean_Server_rpcStoreRef___redArg___closed__1,
                );
                v___x_1687_ = lean_box_usize(v_id_1682_);
                v___x_1688_ = l_Lean_PersistentHashMap_find_x3f___redArg(
                    v___f_1686_,
                    v___f_1683_,
                    v_refsById_1678_,
                    v___x_1687_,
                );
                if lean_obj_tag(v___x_1688_) == 0 {
                    lean_inc_ref(v_refsById_1678_);
                    lean_inc_ref(v_aliveRefs_1677_);
                    v_isSharedCheck_1707_ = (!lean_is_exclusive(v_a_1676_)) as u8;
                    if v_isSharedCheck_1707_ == 0 {
                        v_unused_1708_ = lean_ctor_get(v_a_1676_, 1);
                        lean_dec(v_unused_1708_);
                        v_unused_1709_ = lean_ctor_get(v_a_1676_, 0);
                        lean_dec(v_unused_1709_);
                        v___x_1690_ = v_a_1676_;
                        v_isShared_1691_ = v_isSharedCheck_1707_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_a_1676_);
                        v___x_1690_ = lean_box(0);
                        v_isShared_1691_ = v_isSharedCheck_1707_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_inst_1674_);
                    v_val_1710_ = lean_ctor_get(v___x_1688_, 0);
                    lean_inc_n(v_val_1710_, 2);
                    lean_dec_ref_known(v___x_1688_, 1);
                    v___x_1711_ = l_Lean_PersistentHashMap_find_x3f___redArg(
                        v___x_1684_,
                        v___x_1685_,
                        v_aliveRefs_1677_,
                        v_val_1710_,
                    );
                    if lean_obj_tag(v___x_1711_) == 1 {
                        lean_inc_ref(v_refsById_1678_);
                        lean_inc_ref(v_aliveRefs_1677_);
                        v_isSharedCheck_1733_ = (!lean_is_exclusive(v_a_1676_)) as u8;
                        if v_isSharedCheck_1733_ == 0 {
                            v_unused_1734_ = lean_ctor_get(v_a_1676_, 1);
                            lean_dec(v_unused_1734_);
                            v_unused_1735_ = lean_ctor_get(v_a_1676_, 0);
                            lean_dec(v_unused_1735_);
                            v___x_1713_ = v_a_1676_;
                            v_isShared_1714_ = v_isSharedCheck_1733_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v_a_1676_);
                            v___x_1713_ = lean_box(0);
                            v_isShared_1714_ = v_isSharedCheck_1733_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1711_);
                        lean_dec(v_val_1710_);
                        v___x_1736_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Server_rpcStoreRef___redArg___closed__5),
                            core::ptr::addr_of_mut!(
                                l_Lean_Server_rpcStoreRef___redArg___closed__5_once
                            ),
                            _init_l_Lean_Server_rpcStoreRef___redArg___closed__5,
                        );
                        v___x_1737_ = l_Lean_Server_rpcStoreRef___redArg___boxed__const__1;
                        v___x_1738_ = l_panic___redArg(v___x_1737_, v___x_1736_);
                        v___x_1739_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1739_, 0, v___x_1738_);
                        lean_ctor_set(v___x_1739_, 1, v_a_1676_);
                        return v___x_1739_;
                    }
                }
            }
            1 => {
                lean_inc(v_val_1681_);
                v___x_1692_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1692_, 0, v_inst_1674_);
                lean_ctor_set(v___x_1692_, 1, v_val_1681_);
                v___x_1693_ = lean_unsigned_to_nat(1);
                v___x_1694_ = lean_alloc_ctor(0, 2, (core::mem::size_of::<usize>() * 1) as u32);
                lean_ctor_set(v___x_1694_, 0, v___x_1692_);
                lean_ctor_set(v___x_1694_, 1, v___x_1693_);
                lean_ctor_set_usize(v___x_1694_, 2, v_id_1682_);
                v___x_1695_ = lean_box_usize(v_nextRef_1679_);
                v___x_1696_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___x_1684_,
                    v___x_1685_,
                    v_aliveRefs_1677_,
                    v___x_1695_,
                    v___x_1694_,
                );
                v___x_1697_ = lean_box_usize(v_id_1682_);
                v___x_1698_ = lean_box_usize(v_nextRef_1679_);
                v___x_1699_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___f_1686_,
                    v___f_1683_,
                    v_refsById_1678_,
                    v___x_1697_,
                    v___x_1698_,
                );
                v___x_1700_ = 1usize;
                v___x_1701_ = lean_usize_add(v_nextRef_1679_, v___x_1700_);
                if v_isShared_1691_ == 0 {
                    lean_ctor_set(v___x_1690_, 1, v___x_1699_);
                    lean_ctor_set(v___x_1690_, 0, v___x_1696_);
                    v___x_1703_ = v___x_1690_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1706_ =
                        lean_alloc_ctor(0, 2, (core::mem::size_of::<usize>() * 1 + 1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1696_);
                    lean_ctor_set(v_reuseFailAlloc_1706_, 1, v___x_1699_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1706_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_wireFormat_1680_,
                    );
                    v___x_1703_ = v_reuseFailAlloc_1706_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_usize(v___x_1703_, 2, v___x_1701_);
                v___x_1704_ = lean_box_usize(v_nextRef_1679_);
                v___x_1705_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1705_, 0, v___x_1704_);
                lean_ctor_set(v___x_1705_, 1, v___x_1703_);
                return v___x_1705_;
            }
            3 => {
                v_val_1715_ = lean_ctor_get(v___x_1711_, 0);
                lean_inc(v_val_1715_);
                lean_dec_ref_known(v___x_1711_, 1);
                v_obj_1716_ = lean_ctor_get(v_val_1715_, 0);
                v_id_1717_ = lean_ctor_get_usize(v_val_1715_, 2);
                v_rc_1718_ = lean_ctor_get(v_val_1715_, 1);
                v_isSharedCheck_1732_ = (!lean_is_exclusive(v_val_1715_)) as u8;
                if v_isSharedCheck_1732_ == 0 {
                    v___x_1720_ = v_val_1715_;
                    v_isShared_1721_ = v_isSharedCheck_1732_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_rc_1718_);
                    lean_inc(v_obj_1716_);
                    lean_dec(v_val_1715_);
                    v___x_1720_ = lean_box(0);
                    v_isShared_1721_ = v_isSharedCheck_1732_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1722_ = lean_unsigned_to_nat(1);
                v___x_1723_ = lean_nat_add(v_rc_1718_, v___x_1722_);
                lean_dec(v_rc_1718_);
                if v_isShared_1721_ == 0 {
                    lean_ctor_set(v___x_1720_, 1, v___x_1723_);
                    v___x_1725_ = v___x_1720_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1731_ =
                        lean_alloc_ctor(0, 2, (core::mem::size_of::<usize>() * 1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_obj_1716_);
                    lean_ctor_set(v_reuseFailAlloc_1731_, 1, v___x_1723_);
                    lean_ctor_set_usize(v_reuseFailAlloc_1731_, 2, v_id_1717_);
                    v___x_1725_ = v_reuseFailAlloc_1731_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc(v_val_1710_);
                v___x_1726_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___x_1684_,
                    v___x_1685_,
                    v_aliveRefs_1677_,
                    v_val_1710_,
                    v___x_1725_,
                );
                if v_isShared_1714_ == 0 {
                    lean_ctor_set(v___x_1713_, 0, v___x_1726_);
                    v___x_1728_ = v___x_1713_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1730_ =
                        lean_alloc_ctor(0, 2, (core::mem::size_of::<usize>() * 1 + 1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1726_);
                    lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_refsById_1678_);
                    lean_ctor_set_usize(v_reuseFailAlloc_1730_, 2, v_nextRef_1679_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1730_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_wireFormat_1680_,
                    );
                    v___x_1728_ = v_reuseFailAlloc_1730_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1729_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1729_, 0, v_val_1710_);
                lean_ctor_set(v___x_1729_, 1, v___x_1728_);
                return v___x_1729_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_rpcStoreRef___redArg___boxed(
    mut v_inst_1740_: *mut LeanObject,
    mut v_obj_1741_: *mut LeanObject,
    mut v_a_1742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1743_: *mut LeanObject = core::ptr::null_mut();
    v_res_1743_ = l_Lean_Server_rpcStoreRef___redArg(v_inst_1740_, v_obj_1741_, v_a_1742_);
    lean_dec_ref(v_obj_1741_);
    return v_res_1743_;
}
pub unsafe fn l_Lean_Server_rpcStoreRef(
    mut v_00_u03b1_1744_: *mut LeanObject,
    mut v_inst_1745_: *mut LeanObject,
    mut v_obj_1746_: *mut LeanObject,
    mut v_a_1747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    v___x_1748_ = l_Lean_Server_rpcStoreRef___redArg(v_inst_1745_, v_obj_1746_, v_a_1747_);
    return v___x_1748_;
}
pub unsafe fn l_Lean_Server_rpcStoreRef___boxed(
    mut v_00_u03b1_1749_: *mut LeanObject,
    mut v_inst_1750_: *mut LeanObject,
    mut v_obj_1751_: *mut LeanObject,
    mut v_a_1752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1753_: *mut LeanObject = core::ptr::null_mut();
    v_res_1753_ = l_Lean_Server_rpcStoreRef(v_00_u03b1_1749_, v_inst_1750_, v_obj_1751_, v_a_1752_);
    lean_dec_ref(v_obj_1751_);
    return v_res_1753_;
}
pub unsafe fn l_Lean_Server_rpcGetRef___redArg(
    mut v_inst_1761_: *mut LeanObject,
    mut v_r_1762_: usize,
    mut v_a_1763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_aliveRefs_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1772_: u8 = 0;
    let mut v_obj_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_1774_: usize = 0;
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1779_: u8 = 0;
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1784_: u8 = 0;
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: u8 = 0;
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1806_: u8 = 0;
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_aliveRefs_1764_ = lean_ctor_get(v_a_1763_, 0);
                v___x_1765_ = l_Lean_Lsp_instBEqRpcRef___closed__0;
                v___x_1766_ = l_Lean_Lsp_instHashableRpcRef___closed__0;
                v___x_1767_ = lean_box_usize(v_r_1762_);
                v___x_1768_ = l_Lean_PersistentHashMap_find_x3f___redArg(
                    v___x_1765_,
                    v___x_1766_,
                    v_aliveRefs_1764_,
                    v___x_1767_,
                );
                if lean_obj_tag(v___x_1768_) == 1 {
                    v_val_1769_ = lean_ctor_get(v___x_1768_, 0);
                    v_isSharedCheck_1806_ = (!lean_is_exclusive(v___x_1768_)) as u8;
                    if v_isSharedCheck_1806_ == 0 {
                        v___x_1771_ = v___x_1768_;
                        v_isShared_1772_ = v_isSharedCheck_1806_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1769_);
                        lean_dec(v___x_1768_);
                        v___x_1771_ = lean_box(0);
                        v_isShared_1772_ = v_isSharedCheck_1806_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1768_);
                    lean_dec(v_inst_1761_);
                    v___x_1807_ = l_Lean_Server_rpcGetRef___redArg___closed__5;
                    v___x_1808_ = lean_usize_to_nat(v_r_1762_);
                    v___x_1809_ = l_Nat_reprFast(v___x_1808_);
                    v___x_1810_ = lean_string_append(v___x_1807_, v___x_1809_);
                    lean_dec_ref(v___x_1809_);
                    v___x_1811_ = l_Lean_Server_rpcGetRef___redArg___closed__6;
                    v___x_1812_ = lean_string_append(v___x_1810_, v___x_1811_);
                    v___x_1813_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1813_, 0, v___x_1812_);
                    return v___x_1813_;
                }
            }
            1 => {
                v_obj_1773_ = lean_ctor_get(v_val_1769_, 0);
                lean_inc(v_obj_1773_);
                v_id_1774_ = lean_ctor_get_usize(v_val_1769_, 2);
                lean_dec(v_val_1769_);
                v___x_1775_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(
                    v_obj_1773_,
                    v_inst_1761_,
                );
                if lean_obj_tag(v___x_1775_) == 1 {
                    lean_dec(v_obj_1773_);
                    lean_del_object(v___x_1771_);
                    lean_dec(v_inst_1761_);
                    v_val_1776_ = lean_ctor_get(v___x_1775_, 0);
                    v_isSharedCheck_1784_ = (!lean_is_exclusive(v___x_1775_)) as u8;
                    if v_isSharedCheck_1784_ == 0 {
                        v___x_1778_ = v___x_1775_;
                        v_isShared_1779_ = v_isSharedCheck_1784_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_1776_);
                        lean_dec(v___x_1775_);
                        v___x_1778_ = lean_box(0);
                        v_isShared_1779_ = v_isSharedCheck_1784_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1775_);
                    v___x_1785_ = l_Lean_Server_rpcGetRef___redArg___closed__0;
                    v___x_1786_ = lean_usize_to_nat(v_r_1762_);
                    v___x_1787_ = l_Nat_reprFast(v___x_1786_);
                    v___x_1788_ = lean_string_append(v___x_1785_, v___x_1787_);
                    lean_dec_ref(v___x_1787_);
                    v___x_1789_ = l_Lean_Server_rpcGetRef___redArg___closed__1;
                    v___x_1790_ = lean_string_append(v___x_1788_, v___x_1789_);
                    v___x_1791_ = 1;
                    v___x_1792_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_inst_1761_,
                        v___x_1791_,
                    );
                    v___x_1793_ = lean_string_append(v___x_1790_, v___x_1792_);
                    lean_dec_ref(v___x_1792_);
                    v___x_1794_ = l_Lean_Server_rpcGetRef___redArg___closed__2;
                    v___x_1795_ = lean_string_append(v___x_1793_, v___x_1794_);
                    v___x_1796_ = l_Lean_Server_rpcGetRef___redArg___closed__3;
                    v___x_1797_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_obj_1773_);
                    lean_dec(v_obj_1773_);
                    v___x_1798_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v___x_1797_,
                        v___x_1791_,
                    );
                    v___x_1799_ = lean_string_append(v___x_1796_, v___x_1798_);
                    lean_dec_ref(v___x_1798_);
                    v___x_1800_ = l_Lean_Server_rpcGetRef___redArg___closed__4;
                    v___x_1801_ = lean_string_append(v___x_1799_, v___x_1800_);
                    v___x_1802_ = lean_string_append(v___x_1795_, v___x_1801_);
                    lean_dec_ref(v___x_1801_);
                    if v_isShared_1772_ == 0 {
                        lean_ctor_set_tag(v___x_1771_, 0);
                        lean_ctor_set(v___x_1771_, 0, v___x_1802_);
                        v___x_1804_ = v___x_1771_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
                        v___x_1804_ = v_reuseFailAlloc_1805_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1780_ = lean_alloc_ctor(0, 1, (core::mem::size_of::<usize>() * 1) as u32);
                lean_ctor_set(v___x_1780_, 0, v_val_1776_);
                lean_ctor_set_usize(v___x_1780_, 1, v_id_1774_);
                if v_isShared_1779_ == 0 {
                    lean_ctor_set(v___x_1778_, 0, v___x_1780_);
                    v___x_1782_ = v___x_1778_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1780_);
                    v___x_1782_ = v_reuseFailAlloc_1783_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1782_;
            }
            4 => {
                return v___x_1804_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_rpcGetRef___redArg___boxed(
    mut v_inst_1814_: *mut LeanObject,
    mut v_r_1815_: *mut LeanObject,
    mut v_a_1816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_boxed_1817_: usize = 0;
    let mut v_res_1818_: *mut LeanObject = core::ptr::null_mut();
    v_r_boxed_1817_ = lean_unbox_usize(v_r_1815_);
    lean_dec(v_r_1815_);
    v_res_1818_ = l_Lean_Server_rpcGetRef___redArg(v_inst_1814_, v_r_boxed_1817_, v_a_1816_);
    lean_dec_ref(v_a_1816_);
    return v_res_1818_;
}
pub unsafe fn l_Lean_Server_rpcGetRef(
    mut v_00_u03b1_1819_: *mut LeanObject,
    mut v_inst_1820_: *mut LeanObject,
    mut v_r_1821_: usize,
    mut v_a_1822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    v___x_1823_ = l_Lean_Server_rpcGetRef___redArg(v_inst_1820_, v_r_1821_, v_a_1822_);
    return v___x_1823_;
}
pub unsafe fn l_Lean_Server_rpcGetRef___boxed(
    mut v_00_u03b1_1824_: *mut LeanObject,
    mut v_inst_1825_: *mut LeanObject,
    mut v_r_1826_: *mut LeanObject,
    mut v_a_1827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_boxed_1828_: usize = 0;
    let mut v_res_1829_: *mut LeanObject = core::ptr::null_mut();
    v_r_boxed_1828_ = lean_unbox_usize(v_r_1826_);
    lean_dec(v_r_1826_);
    v_res_1829_ =
        l_Lean_Server_rpcGetRef(v_00_u03b1_1824_, v_inst_1825_, v_r_boxed_1828_, v_a_1827_);
    lean_dec_ref(v_a_1827_);
    return v_res_1829_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11(
    mut v_xs_1830_: *mut LeanObject,
    mut v_v_1831_: usize,
    mut v_i_1832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: u8 = 0;
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: usize = 0;
    let mut v___x_1838_: u8 = 0;
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1833_ = lean_array_get_size(v_xs_1830_);
                v___x_1834_ = lean_nat_dec_lt(v_i_1832_, v___x_1833_);
                if v___x_1834_ == 0 {
                    lean_dec(v_i_1832_);
                    v___x_1835_ = lean_box(0);
                    return v___x_1835_;
                } else {
                    v___x_1836_ = lean_array_fget_borrowed(v_xs_1830_, v_i_1832_);
                    v___x_1837_ = lean_unbox_usize(v___x_1836_);
                    v___x_1838_ = lean_usize_dec_eq(v___x_1837_, v_v_1831_);
                    if v___x_1838_ == 0 {
                        v___x_1839_ = lean_unsigned_to_nat(1);
                        v___x_1840_ = lean_nat_add(v_i_1832_, v___x_1839_);
                        lean_dec(v_i_1832_);
                        v_i_1832_ = v___x_1840_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1842_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1842_, 0, v_i_1832_);
                        return v___x_1842_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11___boxed(
    mut v_xs_1843_: *mut LeanObject,
    mut v_v_1844_: *mut LeanObject,
    mut v_i_1845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_1846_: usize = 0;
    let mut v_res_1847_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_1846_ = lean_unbox_usize(v_v_1844_);
    lean_dec(v_v_1844_);
    v_res_1847_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11(v_xs_1843_, v_v_boxed_1846_, v_i_1845_);
    lean_dec_ref(v_xs_1843_);
    return v_res_1847_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8(
    mut v_xs_1848_: *mut LeanObject,
    mut v_v_1849_: usize,
) -> *mut LeanObject {
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    v___x_1850_ = lean_unsigned_to_nat(0);
    v___x_1851_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11(v_xs_1848_, v_v_1849_, v___x_1850_);
    return v___x_1851_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8___boxed(
    mut v_xs_1852_: *mut LeanObject,
    mut v_v_1853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_1854_: usize = 0;
    let mut v_res_1855_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_1854_ = lean_unbox_usize(v_v_1853_);
    lean_dec(v_v_1853_);
    v_res_1855_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8(v_xs_1852_, v_v_boxed_1854_);
    lean_dec_ref(v_xs_1852_);
    return v_res_1855_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_1856_: usize = 0;
    let mut v___x_1857_: usize = 0;
    let mut v___x_1858_: usize = 0;
    v___x_1856_ = 5usize;
    v___x_1857_ = 1usize;
    v___x_1858_ = lean_usize_shift_left(v___x_1857_, v___x_1856_);
    return v___x_1858_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_1859_: usize = 0;
    let mut v___x_1860_: usize = 0;
    let mut v___x_1861_: usize = 0;
    v___x_1859_ = 1usize;
    v___x_1860_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__0);
    v___x_1861_ = lean_usize_sub(v___x_1860_, v___x_1859_);
    return v___x_1861_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(
    mut v_x_1862_: *mut LeanObject,
    mut v_x_1863_: usize,
    mut v_x_1864_: usize,
) -> *mut LeanObject {
    let mut v_es_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: usize = 0;
    let mut v___x_1868_: usize = 0;
    let mut v___x_1869_: usize = 0;
    let mut v_j_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entry_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: usize = 0;
    let mut v___x_1874_: u8 = 0;
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1877_: u8 = 0;
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1882_: u8 = 0;
    let mut v_unused_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1886_: u8 = 0;
    let mut v_node_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1890_: u8 = 0;
    let mut v_entries_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: usize = 0;
    let mut v_newNode_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1907_: u8 = 0;
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1915_: u8 = 0;
    let mut v_isSharedCheck_1916_: u8 = 0;
    let mut v_isSharedCheck_1917_: u8 = 0;
    let mut v_unused_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1923_: u8 = 0;
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keys_x27_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vals_x27_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1862_) == 0 {
                    v_es_1865_ = lean_ctor_get(v_x_1862_, 0);
                    v___x_1866_ = lean_box(2);
                    v___x_1867_ = 5usize;
                    v___x_1868_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1);
                    v___x_1869_ = lean_usize_land(v_x_1863_, v___x_1868_);
                    v_j_1870_ = lean_usize_to_nat(v___x_1869_);
                    v_entry_1871_ = lean_array_get(v___x_1866_, v_es_1865_, v_j_1870_);
                    match lean_obj_tag(v_entry_1871_) {
                        0 => {
                            v_key_1872_ = lean_ctor_get(v_entry_1871_, 0);
                            lean_inc(v_key_1872_);
                            lean_dec_ref_known(v_entry_1871_, 2);
                            v___x_1873_ = lean_unbox_usize(v_key_1872_);
                            lean_dec(v_key_1872_);
                            v___x_1874_ = lean_usize_dec_eq(v_x_1864_, v___x_1873_);
                            if v___x_1874_ == 0 {
                                lean_dec(v_j_1870_);
                                return v_x_1862_;
                            } else {
                                lean_inc_ref(v_es_1865_);
                                v_isSharedCheck_1882_ = (!lean_is_exclusive(v_x_1862_)) as u8;
                                if v_isSharedCheck_1882_ == 0 {
                                    v_unused_1883_ = lean_ctor_get(v_x_1862_, 0);
                                    lean_dec(v_unused_1883_);
                                    v___x_1876_ = v_x_1862_;
                                    v_isShared_1877_ = v_isSharedCheck_1882_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_x_1862_);
                                    v___x_1876_ = lean_box(0);
                                    v_isShared_1877_ = v_isSharedCheck_1882_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                        1 => {
                            lean_inc_ref(v_es_1865_);
                            v_isSharedCheck_1917_ = (!lean_is_exclusive(v_x_1862_)) as u8;
                            if v_isSharedCheck_1917_ == 0 {
                                v_unused_1918_ = lean_ctor_get(v_x_1862_, 0);
                                lean_dec(v_unused_1918_);
                                v___x_1885_ = v_x_1862_;
                                v_isShared_1886_ = v_isSharedCheck_1917_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v_x_1862_);
                                v___x_1885_ = lean_box(0);
                                v_isShared_1886_ = v_isSharedCheck_1917_;
                                state = 3;
                                continue;
                            }
                        }
                        _ => {
                            lean_dec(v_j_1870_);
                            return v_x_1862_;
                        }
                    }
                } else {
                    v_ks_1919_ = lean_ctor_get(v_x_1862_, 0);
                    v_vs_1920_ = lean_ctor_get(v_x_1862_, 1);
                    v_isSharedCheck_1934_ = (!lean_is_exclusive(v_x_1862_)) as u8;
                    if v_isSharedCheck_1934_ == 0 {
                        v___x_1922_ = v_x_1862_;
                        v_isShared_1923_ = v_isSharedCheck_1934_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_vs_1920_);
                        lean_inc(v_ks_1919_);
                        lean_dec(v_x_1862_);
                        v___x_1922_ = lean_box(0);
                        v_isShared_1923_ = v_isSharedCheck_1934_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1878_ = lean_array_set(v_es_1865_, v_j_1870_, v___x_1866_);
                lean_dec(v_j_1870_);
                if v_isShared_1877_ == 0 {
                    lean_ctor_set(v___x_1876_, 0, v___x_1878_);
                    v___x_1880_ = v___x_1876_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1878_);
                    v___x_1880_ = v_reuseFailAlloc_1881_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1880_;
            }
            3 => {
                v_node_1887_ = lean_ctor_get(v_entry_1871_, 0);
                v_isSharedCheck_1916_ = (!lean_is_exclusive(v_entry_1871_)) as u8;
                if v_isSharedCheck_1916_ == 0 {
                    v___x_1889_ = v_entry_1871_;
                    v_isShared_1890_ = v_isSharedCheck_1916_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_node_1887_);
                    lean_dec(v_entry_1871_);
                    v___x_1889_ = lean_box(0);
                    v_isShared_1890_ = v_isSharedCheck_1916_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_entries_1891_ = lean_array_set(v_es_1865_, v_j_1870_, v___x_1866_);
                v___x_1892_ = lean_usize_shift_right(v_x_1863_, v___x_1867_);
                v_newNode_1893_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_node_1887_, v___x_1892_, v_x_1864_);
                lean_inc_ref(v_newNode_1893_);
                v___x_1894_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_1893_);
                if lean_obj_tag(v___x_1894_) == 0 {
                    if v_isShared_1890_ == 0 {
                        lean_ctor_set(v___x_1889_, 0, v_newNode_1893_);
                        v___x_1896_ = v___x_1889_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_newNode_1893_);
                        v___x_1896_ = v_reuseFailAlloc_1901_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_newNode_1893_);
                    lean_del_object(v___x_1889_);
                    v_val_1902_ = lean_ctor_get(v___x_1894_, 0);
                    lean_inc(v_val_1902_);
                    lean_dec_ref_known(v___x_1894_, 1);
                    v_fst_1903_ = lean_ctor_get(v_val_1902_, 0);
                    v_snd_1904_ = lean_ctor_get(v_val_1902_, 1);
                    v_isSharedCheck_1915_ = (!lean_is_exclusive(v_val_1902_)) as u8;
                    if v_isSharedCheck_1915_ == 0 {
                        v___x_1906_ = v_val_1902_;
                        v_isShared_1907_ = v_isSharedCheck_1915_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_snd_1904_);
                        lean_inc(v_fst_1903_);
                        lean_dec(v_val_1902_);
                        v___x_1906_ = lean_box(0);
                        v_isShared_1907_ = v_isSharedCheck_1915_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1897_ = lean_array_set(v_entries_1891_, v_j_1870_, v___x_1896_);
                lean_dec(v_j_1870_);
                if v_isShared_1886_ == 0 {
                    lean_ctor_set(v___x_1885_, 0, v___x_1897_);
                    v___x_1899_ = v___x_1885_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1897_);
                    v___x_1899_ = v_reuseFailAlloc_1900_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1899_;
            }
            7 => {
                if v_isShared_1907_ == 0 {
                    v___x_1909_ = v___x_1906_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_fst_1903_);
                    lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_snd_1904_);
                    v___x_1909_ = v_reuseFailAlloc_1914_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1910_ = lean_array_set(v_entries_1891_, v_j_1870_, v___x_1909_);
                lean_dec(v_j_1870_);
                if v_isShared_1886_ == 0 {
                    lean_ctor_set(v___x_1885_, 0, v___x_1910_);
                    v___x_1912_ = v___x_1885_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1910_);
                    v___x_1912_ = v_reuseFailAlloc_1913_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1912_;
            }
            10 => {
                v___x_1924_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8(v_ks_1919_, v_x_1864_);
                if lean_obj_tag(v___x_1924_) == 0 {
                    if v_isShared_1923_ == 0 {
                        v___x_1926_ = v___x_1922_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_ks_1919_);
                        lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_vs_1920_);
                        v___x_1926_ = v_reuseFailAlloc_1927_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_val_1928_ = lean_ctor_get(v___x_1924_, 0);
                    lean_inc_n(v_val_1928_, 2);
                    lean_dec_ref_known(v___x_1924_, 1);
                    v_keys_x27_1929_ = l_Array_eraseIdx___redArg(v_ks_1919_, v_val_1928_);
                    v_vals_x27_1930_ = l_Array_eraseIdx___redArg(v_vs_1920_, v_val_1928_);
                    if v_isShared_1923_ == 0 {
                        lean_ctor_set(v___x_1922_, 1, v_vals_x27_1930_);
                        lean_ctor_set(v___x_1922_, 0, v_keys_x27_1929_);
                        v___x_1932_ = v___x_1922_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_keys_x27_1929_);
                        lean_ctor_set(v_reuseFailAlloc_1933_, 1, v_vals_x27_1930_);
                        v___x_1932_ = v_reuseFailAlloc_1933_;
                        state = 12;
                        continue;
                    }
                }
            }
            11 => {
                return v___x_1926_;
            }
            12 => {
                return v___x_1932_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___boxed(
    mut v_x_1935_: *mut LeanObject,
    mut v_x_1936_: *mut LeanObject,
    mut v_x_1937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1722__boxed_1938_: usize = 0;
    let mut v_x_1723__boxed_1939_: usize = 0;
    let mut v_res_1940_: *mut LeanObject = core::ptr::null_mut();
    v_x_1722__boxed_1938_ = lean_unbox_usize(v_x_1936_);
    lean_dec(v_x_1936_);
    v_x_1723__boxed_1939_ = lean_unbox_usize(v_x_1937_);
    lean_dec(v_x_1937_);
    v_res_1940_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_x_1935_, v_x_1722__boxed_1938_, v_x_1723__boxed_1939_);
    return v_res_1940_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(
    mut v_x_1941_: *mut LeanObject,
    mut v_x_1942_: usize,
) -> *mut LeanObject {
    let mut v___x_1943_: u64 = 0;
    let mut v_h_1944_: usize = 0;
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    v___x_1943_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_1942_);
    v_h_1944_ = lean_uint64_to_usize(v___x_1943_);
    v___x_1945_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_x_1941_, v_h_1944_, v_x_1942_);
    return v___x_1945_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg___boxed(
    mut v_x_1946_: *mut LeanObject,
    mut v_x_1947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1866__boxed_1948_: usize = 0;
    let mut v_res_1949_: *mut LeanObject = core::ptr::null_mut();
    v_x_1866__boxed_1948_ = lean_unbox_usize(v_x_1947_);
    lean_dec(v_x_1947_);
    v_res_1949_ =
        l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(
            v_x_1946_,
            v_x_1866__boxed_1948_,
        );
    return v_res_1949_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(
    mut v_keys_1950_: *mut LeanObject,
    mut v_vals_1951_: *mut LeanObject,
    mut v_i_1952_: *mut LeanObject,
    mut v_k_1953_: usize,
) -> *mut LeanObject {
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: u8 = 0;
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: usize = 0;
    let mut v___x_1959_: u8 = 0;
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1954_ = lean_array_get_size(v_keys_1950_);
                v___x_1955_ = lean_nat_dec_lt(v_i_1952_, v___x_1954_);
                if v___x_1955_ == 0 {
                    lean_dec(v_i_1952_);
                    v___x_1956_ = lean_box(0);
                    return v___x_1956_;
                } else {
                    v_k_x27_1957_ = lean_array_fget_borrowed(v_keys_1950_, v_i_1952_);
                    v___x_1958_ = lean_unbox_usize(v_k_x27_1957_);
                    v___x_1959_ = lean_usize_dec_eq(v_k_1953_, v___x_1958_);
                    if v___x_1959_ == 0 {
                        v___x_1960_ = lean_unsigned_to_nat(1);
                        v___x_1961_ = lean_nat_add(v_i_1952_, v___x_1960_);
                        lean_dec(v_i_1952_);
                        v_i_1952_ = v___x_1961_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1963_ = lean_array_fget_borrowed(v_vals_1951_, v_i_1952_);
                        lean_dec(v_i_1952_);
                        lean_inc(v___x_1963_);
                        v___x_1964_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1964_, 0, v___x_1963_);
                        return v___x_1964_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_1965_: *mut LeanObject,
    mut v_vals_1966_: *mut LeanObject,
    mut v_i_1967_: *mut LeanObject,
    mut v_k_1968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_boxed_1969_: usize = 0;
    let mut v_res_1970_: *mut LeanObject = core::ptr::null_mut();
    v_k_boxed_1969_ = lean_unbox_usize(v_k_1968_);
    lean_dec(v_k_1968_);
    v_res_1970_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(v_keys_1965_, v_vals_1966_, v_i_1967_, v_k_boxed_1969_);
    lean_dec_ref(v_vals_1966_);
    lean_dec_ref(v_keys_1965_);
    return v_res_1970_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(
    mut v_x_1971_: *mut LeanObject,
    mut v_x_1972_: usize,
    mut v_x_1973_: usize,
) -> *mut LeanObject {
    let mut v_es_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: usize = 0;
    let mut v___x_1977_: usize = 0;
    let mut v___x_1978_: usize = 0;
    let mut v_j_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: usize = 0;
    let mut v___x_1984_: u8 = 0;
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: usize = 0;
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1971_) == 0 {
                    v_es_1974_ = lean_ctor_get(v_x_1971_, 0);
                    v___x_1975_ = lean_box(2);
                    v___x_1976_ = 5usize;
                    v___x_1977_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1);
                    v___x_1978_ = lean_usize_land(v_x_1972_, v___x_1977_);
                    v_j_1979_ = lean_usize_to_nat(v___x_1978_);
                    v___x_1980_ = lean_array_get_borrowed(v___x_1975_, v_es_1974_, v_j_1979_);
                    lean_dec(v_j_1979_);
                    match lean_obj_tag(v___x_1980_) {
                        0 => {
                            v_key_1981_ = lean_ctor_get(v___x_1980_, 0);
                            v_val_1982_ = lean_ctor_get(v___x_1980_, 1);
                            v___x_1983_ = lean_unbox_usize(v_key_1981_);
                            v___x_1984_ = lean_usize_dec_eq(v_x_1973_, v___x_1983_);
                            if v___x_1984_ == 0 {
                                v___x_1985_ = lean_box(0);
                                return v___x_1985_;
                            } else {
                                lean_inc(v_val_1982_);
                                v___x_1986_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_1986_, 0, v_val_1982_);
                                return v___x_1986_;
                            }
                        }
                        1 => {
                            v_node_1987_ = lean_ctor_get(v___x_1980_, 0);
                            v___x_1988_ = lean_usize_shift_right(v_x_1972_, v___x_1976_);
                            v_x_1971_ = v_node_1987_;
                            v_x_1972_ = v___x_1988_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1990_ = lean_box(0);
                            return v___x_1990_;
                        }
                    }
                } else {
                    v_ks_1991_ = lean_ctor_get(v_x_1971_, 0);
                    v_vs_1992_ = lean_ctor_get(v_x_1971_, 1);
                    v___x_1993_ = lean_unsigned_to_nat(0);
                    v___x_1994_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(v_ks_1991_, v_vs_1992_, v___x_1993_, v_x_1973_);
                    return v___x_1994_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg___boxed(
    mut v_x_1995_: *mut LeanObject,
    mut v_x_1996_: *mut LeanObject,
    mut v_x_1997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1902__boxed_1998_: usize = 0;
    let mut v_x_1903__boxed_1999_: usize = 0;
    let mut v_res_2000_: *mut LeanObject = core::ptr::null_mut();
    v_x_1902__boxed_1998_ = lean_unbox_usize(v_x_1996_);
    lean_dec(v_x_1996_);
    v_x_1903__boxed_1999_ = lean_unbox_usize(v_x_1997_);
    lean_dec(v_x_1997_);
    v_res_2000_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(v_x_1995_, v_x_1902__boxed_1998_, v_x_1903__boxed_1999_);
    lean_dec_ref(v_x_1995_);
    return v_res_2000_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(
    mut v_x_2001_: *mut LeanObject,
    mut v_x_2002_: usize,
) -> *mut LeanObject {
    let mut v___x_2003_: u64 = 0;
    let mut v___x_2004_: usize = 0;
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    v___x_2003_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_2002_);
    v___x_2004_ = lean_uint64_to_usize(v___x_2003_);
    v___x_2005_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(v_x_2001_, v___x_2004_, v_x_2002_);
    return v___x_2005_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg___boxed(
    mut v_x_2006_: *mut LeanObject,
    mut v_x_2007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1953__boxed_2008_: usize = 0;
    let mut v_res_2009_: *mut LeanObject = core::ptr::null_mut();
    v_x_1953__boxed_2008_ = lean_unbox_usize(v_x_2007_);
    lean_dec(v_x_2007_);
    v_res_2009_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(
            v_x_2006_,
            v_x_1953__boxed_2008_,
        );
    lean_dec_ref(v_x_2006_);
    return v_res_2009_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14(
    mut v_xs_2010_: *mut LeanObject,
    mut v_v_2011_: usize,
    mut v_i_2012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: u8 = 0;
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: usize = 0;
    let mut v___x_2018_: u8 = 0;
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2013_ = lean_array_get_size(v_xs_2010_);
                v___x_2014_ = lean_nat_dec_lt(v_i_2012_, v___x_2013_);
                if v___x_2014_ == 0 {
                    lean_dec(v_i_2012_);
                    v___x_2015_ = lean_box(0);
                    return v___x_2015_;
                } else {
                    v___x_2016_ = lean_array_fget_borrowed(v_xs_2010_, v_i_2012_);
                    v___x_2017_ = lean_unbox_usize(v___x_2016_);
                    v___x_2018_ = lean_usize_dec_eq(v___x_2017_, v_v_2011_);
                    if v___x_2018_ == 0 {
                        v___x_2019_ = lean_unsigned_to_nat(1);
                        v___x_2020_ = lean_nat_add(v_i_2012_, v___x_2019_);
                        lean_dec(v_i_2012_);
                        v_i_2012_ = v___x_2020_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2022_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2022_, 0, v_i_2012_);
                        return v___x_2022_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14___boxed(
    mut v_xs_2023_: *mut LeanObject,
    mut v_v_2024_: *mut LeanObject,
    mut v_i_2025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_2026_: usize = 0;
    let mut v_res_2027_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_2026_ = lean_unbox_usize(v_v_2024_);
    lean_dec(v_v_2024_);
    v_res_2027_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14(v_xs_2023_, v_v_boxed_2026_, v_i_2025_);
    lean_dec_ref(v_xs_2023_);
    return v_res_2027_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11(
    mut v_xs_2028_: *mut LeanObject,
    mut v_v_2029_: usize,
) -> *mut LeanObject {
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    v___x_2030_ = lean_unsigned_to_nat(0);
    v___x_2031_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14(v_xs_2028_, v_v_2029_, v___x_2030_);
    return v___x_2031_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11___boxed(
    mut v_xs_2032_: *mut LeanObject,
    mut v_v_2033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_2034_: usize = 0;
    let mut v_res_2035_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_2034_ = lean_unbox_usize(v_v_2033_);
    lean_dec(v_v_2033_);
    v_res_2035_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11(v_xs_2032_, v_v_boxed_2034_);
    lean_dec_ref(v_xs_2032_);
    return v_res_2035_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(
    mut v_x_2036_: *mut LeanObject,
    mut v_x_2037_: usize,
    mut v_x_2038_: usize,
) -> *mut LeanObject {
    let mut v_es_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: usize = 0;
    let mut v___x_2042_: usize = 0;
    let mut v___x_2043_: usize = 0;
    let mut v_j_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entry_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: usize = 0;
    let mut v___x_2048_: u8 = 0;
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2056_: u8 = 0;
    let mut v_unused_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2060_: u8 = 0;
    let mut v_node_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2064_: u8 = 0;
    let mut v_entries_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: usize = 0;
    let mut v_newNode_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2081_: u8 = 0;
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2089_: u8 = 0;
    let mut v_isSharedCheck_2090_: u8 = 0;
    let mut v_isSharedCheck_2091_: u8 = 0;
    let mut v_unused_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2097_: u8 = 0;
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keys_x27_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vals_x27_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2108_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2036_) == 0 {
                    v_es_2039_ = lean_ctor_get(v_x_2036_, 0);
                    v___x_2040_ = lean_box(2);
                    v___x_2041_ = 5usize;
                    v___x_2042_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1);
                    v___x_2043_ = lean_usize_land(v_x_2037_, v___x_2042_);
                    v_j_2044_ = lean_usize_to_nat(v___x_2043_);
                    v_entry_2045_ = lean_array_get(v___x_2040_, v_es_2039_, v_j_2044_);
                    match lean_obj_tag(v_entry_2045_) {
                        0 => {
                            v_key_2046_ = lean_ctor_get(v_entry_2045_, 0);
                            lean_inc(v_key_2046_);
                            lean_dec_ref_known(v_entry_2045_, 2);
                            v___x_2047_ = lean_unbox_usize(v_key_2046_);
                            lean_dec(v_key_2046_);
                            v___x_2048_ = lean_usize_dec_eq(v_x_2038_, v___x_2047_);
                            if v___x_2048_ == 0 {
                                lean_dec(v_j_2044_);
                                return v_x_2036_;
                            } else {
                                lean_inc_ref(v_es_2039_);
                                v_isSharedCheck_2056_ = (!lean_is_exclusive(v_x_2036_)) as u8;
                                if v_isSharedCheck_2056_ == 0 {
                                    v_unused_2057_ = lean_ctor_get(v_x_2036_, 0);
                                    lean_dec(v_unused_2057_);
                                    v___x_2050_ = v_x_2036_;
                                    v_isShared_2051_ = v_isSharedCheck_2056_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_x_2036_);
                                    v___x_2050_ = lean_box(0);
                                    v_isShared_2051_ = v_isSharedCheck_2056_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                        1 => {
                            lean_inc_ref(v_es_2039_);
                            v_isSharedCheck_2091_ = (!lean_is_exclusive(v_x_2036_)) as u8;
                            if v_isSharedCheck_2091_ == 0 {
                                v_unused_2092_ = lean_ctor_get(v_x_2036_, 0);
                                lean_dec(v_unused_2092_);
                                v___x_2059_ = v_x_2036_;
                                v_isShared_2060_ = v_isSharedCheck_2091_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v_x_2036_);
                                v___x_2059_ = lean_box(0);
                                v_isShared_2060_ = v_isSharedCheck_2091_;
                                state = 3;
                                continue;
                            }
                        }
                        _ => {
                            lean_dec(v_j_2044_);
                            return v_x_2036_;
                        }
                    }
                } else {
                    v_ks_2093_ = lean_ctor_get(v_x_2036_, 0);
                    v_vs_2094_ = lean_ctor_get(v_x_2036_, 1);
                    v_isSharedCheck_2108_ = (!lean_is_exclusive(v_x_2036_)) as u8;
                    if v_isSharedCheck_2108_ == 0 {
                        v___x_2096_ = v_x_2036_;
                        v_isShared_2097_ = v_isSharedCheck_2108_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_vs_2094_);
                        lean_inc(v_ks_2093_);
                        lean_dec(v_x_2036_);
                        v___x_2096_ = lean_box(0);
                        v_isShared_2097_ = v_isSharedCheck_2108_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2052_ = lean_array_set(v_es_2039_, v_j_2044_, v___x_2040_);
                lean_dec(v_j_2044_);
                if v_isShared_2051_ == 0 {
                    lean_ctor_set(v___x_2050_, 0, v___x_2052_);
                    v___x_2054_ = v___x_2050_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
                    v___x_2054_ = v_reuseFailAlloc_2055_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2054_;
            }
            3 => {
                v_node_2061_ = lean_ctor_get(v_entry_2045_, 0);
                v_isSharedCheck_2090_ = (!lean_is_exclusive(v_entry_2045_)) as u8;
                if v_isSharedCheck_2090_ == 0 {
                    v___x_2063_ = v_entry_2045_;
                    v_isShared_2064_ = v_isSharedCheck_2090_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_node_2061_);
                    lean_dec(v_entry_2045_);
                    v___x_2063_ = lean_box(0);
                    v_isShared_2064_ = v_isSharedCheck_2090_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_entries_2065_ = lean_array_set(v_es_2039_, v_j_2044_, v___x_2040_);
                v___x_2066_ = lean_usize_shift_right(v_x_2037_, v___x_2041_);
                v_newNode_2067_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_node_2061_, v___x_2066_, v_x_2038_);
                lean_inc_ref(v_newNode_2067_);
                v___x_2068_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2067_);
                if lean_obj_tag(v___x_2068_) == 0 {
                    if v_isShared_2064_ == 0 {
                        lean_ctor_set(v___x_2063_, 0, v_newNode_2067_);
                        v___x_2070_ = v___x_2063_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_newNode_2067_);
                        v___x_2070_ = v_reuseFailAlloc_2075_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_newNode_2067_);
                    lean_del_object(v___x_2063_);
                    v_val_2076_ = lean_ctor_get(v___x_2068_, 0);
                    lean_inc(v_val_2076_);
                    lean_dec_ref_known(v___x_2068_, 1);
                    v_fst_2077_ = lean_ctor_get(v_val_2076_, 0);
                    v_snd_2078_ = lean_ctor_get(v_val_2076_, 1);
                    v_isSharedCheck_2089_ = (!lean_is_exclusive(v_val_2076_)) as u8;
                    if v_isSharedCheck_2089_ == 0 {
                        v___x_2080_ = v_val_2076_;
                        v_isShared_2081_ = v_isSharedCheck_2089_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_snd_2078_);
                        lean_inc(v_fst_2077_);
                        lean_dec(v_val_2076_);
                        v___x_2080_ = lean_box(0);
                        v_isShared_2081_ = v_isSharedCheck_2089_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2071_ = lean_array_set(v_entries_2065_, v_j_2044_, v___x_2070_);
                lean_dec(v_j_2044_);
                if v_isShared_2060_ == 0 {
                    lean_ctor_set(v___x_2059_, 0, v___x_2071_);
                    v___x_2073_ = v___x_2059_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
                    v___x_2073_ = v_reuseFailAlloc_2074_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2073_;
            }
            7 => {
                if v_isShared_2081_ == 0 {
                    v___x_2083_ = v___x_2080_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_fst_2077_);
                    lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_snd_2078_);
                    v___x_2083_ = v_reuseFailAlloc_2088_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2084_ = lean_array_set(v_entries_2065_, v_j_2044_, v___x_2083_);
                lean_dec(v_j_2044_);
                if v_isShared_2060_ == 0 {
                    lean_ctor_set(v___x_2059_, 0, v___x_2084_);
                    v___x_2086_ = v___x_2059_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
                    v___x_2086_ = v_reuseFailAlloc_2087_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2086_;
            }
            10 => {
                v___x_2098_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11(v_ks_2093_, v_x_2038_);
                if lean_obj_tag(v___x_2098_) == 0 {
                    if v_isShared_2097_ == 0 {
                        v___x_2100_ = v___x_2096_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_ks_2093_);
                        lean_ctor_set(v_reuseFailAlloc_2101_, 1, v_vs_2094_);
                        v___x_2100_ = v_reuseFailAlloc_2101_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_val_2102_ = lean_ctor_get(v___x_2098_, 0);
                    lean_inc_n(v_val_2102_, 2);
                    lean_dec_ref_known(v___x_2098_, 1);
                    v_keys_x27_2103_ = l_Array_eraseIdx___redArg(v_ks_2093_, v_val_2102_);
                    v_vals_x27_2104_ = l_Array_eraseIdx___redArg(v_vs_2094_, v_val_2102_);
                    if v_isShared_2097_ == 0 {
                        lean_ctor_set(v___x_2096_, 1, v_vals_x27_2104_);
                        lean_ctor_set(v___x_2096_, 0, v_keys_x27_2103_);
                        v___x_2106_ = v___x_2096_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_keys_x27_2103_);
                        lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_vals_x27_2104_);
                        v___x_2106_ = v_reuseFailAlloc_2107_;
                        state = 12;
                        continue;
                    }
                }
            }
            11 => {
                return v___x_2100_;
            }
            12 => {
                return v___x_2106_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg___boxed(
    mut v_x_2109_: *mut LeanObject,
    mut v_x_2110_: *mut LeanObject,
    mut v_x_2111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1995__boxed_2112_: usize = 0;
    let mut v_x_1996__boxed_2113_: usize = 0;
    let mut v_res_2114_: *mut LeanObject = core::ptr::null_mut();
    v_x_1995__boxed_2112_ = lean_unbox_usize(v_x_2110_);
    lean_dec(v_x_2110_);
    v_x_1996__boxed_2113_ = lean_unbox_usize(v_x_2111_);
    lean_dec(v_x_2111_);
    v_res_2114_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_x_2109_, v_x_1995__boxed_2112_, v_x_1996__boxed_2113_);
    return v_res_2114_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(
    mut v_x_2115_: *mut LeanObject,
    mut v_x_2116_: usize,
) -> *mut LeanObject {
    let mut v___x_2117_: u64 = 0;
    let mut v_h_2118_: usize = 0;
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    v___x_2117_ = lean_usize_to_uint64(v_x_2116_);
    v_h_2118_ = lean_uint64_to_usize(v___x_2117_);
    v___x_2119_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_x_2115_, v_h_2118_, v_x_2116_);
    return v___x_2119_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg___boxed(
    mut v_x_2120_: *mut LeanObject,
    mut v_x_2121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2135__boxed_2122_: usize = 0;
    let mut v_res_2123_: *mut LeanObject = core::ptr::null_mut();
    v_x_2135__boxed_2122_ = lean_unbox_usize(v_x_2121_);
    lean_dec(v_x_2121_);
    v_res_2123_ =
        l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(
            v_x_2120_,
            v_x_2135__boxed_2122_,
        );
    return v_res_2123_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(
    mut v_x_2124_: *mut LeanObject,
    mut v_x_2125_: *mut LeanObject,
    mut v_x_2126_: usize,
    mut v_x_2127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2132_: u8 = 0;
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: u8 = 0;
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: usize = 0;
    let mut v___x_2143_: u8 = 0;
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2156_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2128_ = lean_ctor_get(v_x_2124_, 0);
                v_vs_2129_ = lean_ctor_get(v_x_2124_, 1);
                v_isSharedCheck_2156_ = (!lean_is_exclusive(v_x_2124_)) as u8;
                if v_isSharedCheck_2156_ == 0 {
                    v___x_2131_ = v_x_2124_;
                    v_isShared_2132_ = v_isSharedCheck_2156_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_2129_);
                    lean_inc(v_ks_2128_);
                    lean_dec(v_x_2124_);
                    v___x_2131_ = lean_box(0);
                    v_isShared_2132_ = v_isSharedCheck_2156_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2133_ = lean_array_get_size(v_ks_2128_);
                v___x_2134_ = lean_nat_dec_lt(v_x_2125_, v___x_2133_);
                if v___x_2134_ == 0 {
                    lean_dec(v_x_2125_);
                    v___x_2135_ = lean_box_usize(v_x_2126_);
                    v___x_2136_ = lean_array_push(v_ks_2128_, v___x_2135_);
                    v___x_2137_ = lean_array_push(v_vs_2129_, v_x_2127_);
                    if v_isShared_2132_ == 0 {
                        lean_ctor_set(v___x_2131_, 1, v___x_2137_);
                        lean_ctor_set(v___x_2131_, 0, v___x_2136_);
                        v___x_2139_ = v___x_2131_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2136_);
                        lean_ctor_set(v_reuseFailAlloc_2140_, 1, v___x_2137_);
                        v___x_2139_ = v_reuseFailAlloc_2140_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2141_ = lean_array_fget_borrowed(v_ks_2128_, v_x_2125_);
                    v___x_2142_ = lean_unbox_usize(v_k_x27_2141_);
                    v___x_2143_ = lean_usize_dec_eq(v_x_2126_, v___x_2142_);
                    if v___x_2143_ == 0 {
                        if v_isShared_2132_ == 0 {
                            v___x_2145_ = v___x_2131_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_ks_2128_);
                            lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_vs_2129_);
                            v___x_2145_ = v_reuseFailAlloc_2149_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2150_ = lean_box_usize(v_x_2126_);
                        v___x_2151_ = lean_array_fset(v_ks_2128_, v_x_2125_, v___x_2150_);
                        v___x_2152_ = lean_array_fset(v_vs_2129_, v_x_2125_, v_x_2127_);
                        lean_dec(v_x_2125_);
                        if v_isShared_2132_ == 0 {
                            lean_ctor_set(v___x_2131_, 1, v___x_2152_);
                            lean_ctor_set(v___x_2131_, 0, v___x_2151_);
                            v___x_2154_ = v___x_2131_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2151_);
                            lean_ctor_set(v_reuseFailAlloc_2155_, 1, v___x_2152_);
                            v___x_2154_ = v_reuseFailAlloc_2155_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2139_;
            }
            3 => {
                v___x_2146_ = lean_unsigned_to_nat(1);
                v___x_2147_ = lean_nat_add(v_x_2125_, v___x_2146_);
                lean_dec(v_x_2125_);
                v_x_2124_ = v___x_2145_;
                v_x_2125_ = v___x_2147_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2154_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg___boxed(
    mut v_x_2157_: *mut LeanObject,
    mut v_x_2158_: *mut LeanObject,
    mut v_x_2159_: *mut LeanObject,
    mut v_x_2160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2146__boxed_2161_: usize = 0;
    let mut v_res_2162_: *mut LeanObject = core::ptr::null_mut();
    v_x_2146__boxed_2161_ = lean_unbox_usize(v_x_2159_);
    lean_dec(v_x_2159_);
    v_res_2162_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(v_x_2157_, v_x_2158_, v_x_2146__boxed_2161_, v_x_2160_);
    return v_res_2162_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(
    mut v_n_2163_: *mut LeanObject,
    mut v_k_2164_: usize,
    mut v_v_2165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    v___x_2166_ = lean_unsigned_to_nat(0);
    v___x_2167_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(v_n_2163_, v___x_2166_, v_k_2164_, v_v_2165_);
    return v___x_2167_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_n_2168_: *mut LeanObject,
    mut v_k_2169_: *mut LeanObject,
    mut v_v_2170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_boxed_2171_: usize = 0;
    let mut v_res_2172_: *mut LeanObject = core::ptr::null_mut();
    v_k_boxed_2171_ = lean_unbox_usize(v_k_2169_);
    lean_dec(v_k_2169_);
    v_res_2172_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(v_n_2168_, v_k_boxed_2171_, v_v_2170_);
    return v_res_2172_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    v___x_2173_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_2173_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(
    mut v_x_2174_: *mut LeanObject,
    mut v_x_2175_: usize,
    mut v_x_2176_: usize,
    mut v_x_2177_: usize,
    mut v_x_2178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: usize = 0;
    let mut v___x_2181_: usize = 0;
    let mut v___x_2182_: usize = 0;
    let mut v___x_2183_: usize = 0;
    let mut v_j_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: u8 = 0;
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2189_: u8 = 0;
    let mut v_v_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2203_: u8 = 0;
    let mut v___x_2204_: usize = 0;
    let mut v___x_2205_: u8 = 0;
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2213_: u8 = 0;
    let mut v_node_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2217_: u8 = 0;
    let mut v___x_2218_: usize = 0;
    let mut v___x_2219_: usize = 0;
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2224_: u8 = 0;
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2227_: u8 = 0;
    let mut v_unused_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2233_: u8 = 0;
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2238_: u8 = 0;
    let mut v_ks_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: usize = 0;
    let mut v___x_2245_: u8 = 0;
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: u8 = 0;
    let mut v_reuseFailAlloc_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2250_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2174_) == 0 {
                    v_es_2179_ = lean_ctor_get(v_x_2174_, 0);
                    v___x_2180_ = 5usize;
                    v___x_2181_ = 1usize;
                    v___x_2182_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___closed__1);
                    v___x_2183_ = lean_usize_land(v_x_2175_, v___x_2182_);
                    v_j_2184_ = lean_usize_to_nat(v___x_2183_);
                    v___x_2185_ = lean_array_get_size(v_es_2179_);
                    v___x_2186_ = lean_nat_dec_lt(v_j_2184_, v___x_2185_);
                    if v___x_2186_ == 0 {
                        lean_dec(v_j_2184_);
                        lean_dec(v_x_2178_);
                        return v_x_2174_;
                    } else {
                        lean_inc_ref(v_es_2179_);
                        v_isSharedCheck_2227_ = (!lean_is_exclusive(v_x_2174_)) as u8;
                        if v_isSharedCheck_2227_ == 0 {
                            v_unused_2228_ = lean_ctor_get(v_x_2174_, 0);
                            lean_dec(v_unused_2228_);
                            v___x_2188_ = v_x_2174_;
                            v_isShared_2189_ = v_isSharedCheck_2227_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_2174_);
                            v___x_2188_ = lean_box(0);
                            v_isShared_2189_ = v_isSharedCheck_2227_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2229_ = lean_ctor_get(v_x_2174_, 0);
                    v_vs_2230_ = lean_ctor_get(v_x_2174_, 1);
                    v_isSharedCheck_2250_ = (!lean_is_exclusive(v_x_2174_)) as u8;
                    if v_isSharedCheck_2250_ == 0 {
                        v___x_2232_ = v_x_2174_;
                        v_isShared_2233_ = v_isSharedCheck_2250_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_2230_);
                        lean_inc(v_ks_2229_);
                        lean_dec(v_x_2174_);
                        v___x_2232_ = lean_box(0);
                        v_isShared_2233_ = v_isSharedCheck_2250_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2190_ = lean_array_fget(v_es_2179_, v_j_2184_);
                v___x_2191_ = lean_box(0);
                v_xs_x27_2192_ = lean_array_fset(v_es_2179_, v_j_2184_, v___x_2191_);
                match lean_obj_tag(v_v_2190_) {
                    0 => {
                        v_key_2199_ = lean_ctor_get(v_v_2190_, 0);
                        v_val_2200_ = lean_ctor_get(v_v_2190_, 1);
                        v_isSharedCheck_2213_ = (!lean_is_exclusive(v_v_2190_)) as u8;
                        if v_isSharedCheck_2213_ == 0 {
                            v___x_2202_ = v_v_2190_;
                            v_isShared_2203_ = v_isSharedCheck_2213_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2200_);
                            lean_inc(v_key_2199_);
                            lean_dec(v_v_2190_);
                            v___x_2202_ = lean_box(0);
                            v_isShared_2203_ = v_isSharedCheck_2213_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2214_ = lean_ctor_get(v_v_2190_, 0);
                        v_isSharedCheck_2224_ = (!lean_is_exclusive(v_v_2190_)) as u8;
                        if v_isSharedCheck_2224_ == 0 {
                            v___x_2216_ = v_v_2190_;
                            v_isShared_2217_ = v_isSharedCheck_2224_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2214_);
                            lean_dec(v_v_2190_);
                            v___x_2216_ = lean_box(0);
                            v_isShared_2217_ = v_isSharedCheck_2224_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2225_ = lean_box_usize(v_x_2177_);
                        v___x_2226_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2226_, 0, v___x_2225_);
                        lean_ctor_set(v___x_2226_, 1, v_x_2178_);
                        v___y_2194_ = v___x_2226_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2195_ = lean_array_fset(v_xs_x27_2192_, v_j_2184_, v___y_2194_);
                lean_dec(v_j_2184_);
                if v_isShared_2189_ == 0 {
                    lean_ctor_set(v___x_2188_, 0, v___x_2195_);
                    v___x_2197_ = v___x_2188_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2195_);
                    v___x_2197_ = v_reuseFailAlloc_2198_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2197_;
            }
            4 => {
                v___x_2204_ = lean_unbox_usize(v_key_2199_);
                v___x_2205_ = lean_usize_dec_eq(v_x_2177_, v___x_2204_);
                if v___x_2205_ == 0 {
                    lean_del_object(v___x_2202_);
                    v___x_2206_ = lean_box_usize(v_x_2177_);
                    v___x_2207_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2199_,
                        v_val_2200_,
                        v___x_2206_,
                        v_x_2178_,
                    );
                    v___x_2208_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2208_, 0, v___x_2207_);
                    v___y_2194_ = v___x_2208_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_2200_);
                    lean_dec(v_key_2199_);
                    v___x_2209_ = lean_box_usize(v_x_2177_);
                    if v_isShared_2203_ == 0 {
                        lean_ctor_set(v___x_2202_, 1, v_x_2178_);
                        lean_ctor_set(v___x_2202_, 0, v___x_2209_);
                        v___x_2211_ = v___x_2202_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2209_);
                        lean_ctor_set(v_reuseFailAlloc_2212_, 1, v_x_2178_);
                        v___x_2211_ = v_reuseFailAlloc_2212_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2194_ = v___x_2211_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2218_ = lean_usize_shift_right(v_x_2175_, v___x_2180_);
                v___x_2219_ = lean_usize_add(v_x_2176_, v___x_2181_);
                v___x_2220_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_node_2214_, v___x_2218_, v___x_2219_, v_x_2177_, v_x_2178_);
                if v_isShared_2217_ == 0 {
                    lean_ctor_set(v___x_2216_, 0, v___x_2220_);
                    v___x_2222_ = v___x_2216_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2220_);
                    v___x_2222_ = v_reuseFailAlloc_2223_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2194_ = v___x_2222_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2233_ == 0 {
                    v___x_2235_ = v___x_2232_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_ks_2229_);
                    lean_ctor_set(v_reuseFailAlloc_2249_, 1, v_vs_2230_);
                    v___x_2235_ = v_reuseFailAlloc_2249_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2236_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(v___x_2235_, v_x_2177_, v_x_2178_);
                v___x_2244_ = 7usize;
                v___x_2245_ = lean_usize_dec_le(v___x_2244_, v_x_2176_);
                if v___x_2245_ == 0 {
                    v___x_2246_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2236_);
                    v___x_2247_ = lean_unsigned_to_nat(4);
                    v___x_2248_ = lean_nat_dec_lt(v___x_2246_, v___x_2247_);
                    lean_dec(v___x_2246_);
                    v___y_2238_ = v___x_2248_;
                    state = 10;
                    continue;
                } else {
                    v___y_2238_ = v___x_2245_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2238_ == 0 {
                    v_ks_2239_ = lean_ctor_get(v_newNode_2236_, 0);
                    lean_inc_ref(v_ks_2239_);
                    v_vs_2240_ = lean_ctor_get(v_newNode_2236_, 1);
                    lean_inc_ref(v_vs_2240_);
                    lean_dec_ref(v_newNode_2236_);
                    v___x_2241_ = lean_unsigned_to_nat(0);
                    v___x_2242_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0);
                    v___x_2243_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(v_x_2176_, v_ks_2239_, v_vs_2240_, v___x_2241_, v___x_2242_);
                    lean_dec_ref(v_vs_2240_);
                    lean_dec_ref(v_ks_2239_);
                    return v___x_2243_;
                } else {
                    return v_newNode_2236_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(
    mut v_depth_2251_: usize,
    mut v_keys_2252_: *mut LeanObject,
    mut v_vals_2253_: *mut LeanObject,
    mut v_i_2254_: *mut LeanObject,
    mut v_entries_2255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: u8 = 0;
    let mut v_k_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: usize = 0;
    let mut v___x_2261_: u64 = 0;
    let mut v_h_2262_: usize = 0;
    let mut v___x_2263_: usize = 0;
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: usize = 0;
    let mut v___x_2266_: usize = 0;
    let mut v___x_2267_: usize = 0;
    let mut v_h_2268_: usize = 0;
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: usize = 0;
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2256_ = lean_array_get_size(v_keys_2252_);
                v___x_2257_ = lean_nat_dec_lt(v_i_2254_, v___x_2256_);
                if v___x_2257_ == 0 {
                    lean_dec(v_i_2254_);
                    return v_entries_2255_;
                } else {
                    v_k_2258_ = lean_array_fget_borrowed(v_keys_2252_, v_i_2254_);
                    v_v_2259_ = lean_array_fget_borrowed(v_vals_2253_, v_i_2254_);
                    v___x_2260_ = lean_unbox_usize(v_k_2258_);
                    v___x_2261_ = l_Lean_Lsp_instHashableRpcRef_hash(v___x_2260_);
                    v_h_2262_ = lean_uint64_to_usize(v___x_2261_);
                    v___x_2263_ = 5usize;
                    v___x_2264_ = lean_unsigned_to_nat(1);
                    v___x_2265_ = 1usize;
                    v___x_2266_ = lean_usize_sub(v_depth_2251_, v___x_2265_);
                    v___x_2267_ = lean_usize_mul(v___x_2263_, v___x_2266_);
                    v_h_2268_ = lean_usize_shift_right(v_h_2262_, v___x_2267_);
                    v___x_2269_ = lean_nat_add(v_i_2254_, v___x_2264_);
                    lean_dec(v_i_2254_);
                    v___x_2270_ = lean_unbox_usize(v_k_2258_);
                    lean_inc(v_v_2259_);
                    v___x_2271_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_entries_2255_, v_h_2268_, v_depth_2251_, v___x_2270_, v_v_2259_);
                    v_i_2254_ = v___x_2269_;
                    v_entries_2255_ = v___x_2271_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_depth_2273_: *mut LeanObject,
    mut v_keys_2274_: *mut LeanObject,
    mut v_vals_2275_: *mut LeanObject,
    mut v_i_2276_: *mut LeanObject,
    mut v_entries_2277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2278_: usize = 0;
    let mut v_res_2279_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2278_ = lean_unbox_usize(v_depth_2273_);
    lean_dec(v_depth_2273_);
    v_res_2279_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(v_depth_boxed_2278_, v_keys_2274_, v_vals_2275_, v_i_2276_, v_entries_2277_);
    lean_dec_ref(v_vals_2275_);
    lean_dec_ref(v_keys_2274_);
    return v_res_2279_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___boxed(
    mut v_x_2280_: *mut LeanObject,
    mut v_x_2281_: *mut LeanObject,
    mut v_x_2282_: *mut LeanObject,
    mut v_x_2283_: *mut LeanObject,
    mut v_x_2284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2237__boxed_2285_: usize = 0;
    let mut v_x_2238__boxed_2286_: usize = 0;
    let mut v_x_2239__boxed_2287_: usize = 0;
    let mut v_res_2288_: *mut LeanObject = core::ptr::null_mut();
    v_x_2237__boxed_2285_ = lean_unbox_usize(v_x_2281_);
    lean_dec(v_x_2281_);
    v_x_2238__boxed_2286_ = lean_unbox_usize(v_x_2282_);
    lean_dec(v_x_2282_);
    v_x_2239__boxed_2287_ = lean_unbox_usize(v_x_2283_);
    lean_dec(v_x_2283_);
    v_res_2288_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_x_2280_, v_x_2237__boxed_2285_, v_x_2238__boxed_2286_, v_x_2239__boxed_2287_, v_x_2284_);
    return v_res_2288_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(
    mut v_x_2289_: *mut LeanObject,
    mut v_x_2290_: usize,
    mut v_x_2291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2292_: u64 = 0;
    let mut v___x_2293_: usize = 0;
    let mut v___x_2294_: usize = 0;
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    v___x_2292_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_2290_);
    v___x_2293_ = lean_uint64_to_usize(v___x_2292_);
    v___x_2294_ = 1usize;
    v___x_2295_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_x_2289_, v___x_2293_, v___x_2294_, v_x_2290_, v_x_2291_);
    return v___x_2295_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg___boxed(
    mut v_x_2296_: *mut LeanObject,
    mut v_x_2297_: *mut LeanObject,
    mut v_x_2298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2405__boxed_2299_: usize = 0;
    let mut v_res_2300_: *mut LeanObject = core::ptr::null_mut();
    v_x_2405__boxed_2299_ = lean_unbox_usize(v_x_2297_);
    lean_dec(v_x_2297_);
    v_res_2300_ =
        l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(
            v_x_2296_,
            v_x_2405__boxed_2299_,
            v_x_2298_,
        );
    return v_res_2300_;
}
pub unsafe fn l_Lean_Server_rpcReleaseRef(
    mut v_r_2301_: usize,
    mut v_a_2302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: u8 = 0;
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aliveRefs_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_refsById_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextRef_2310_: usize = 0;
    let mut v_wireFormat_2311_: u8 = 0;
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2315_: u8 = 0;
    let mut v_val_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_obj_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_2318_: usize = 0;
    let mut v_rc_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2322_: u8 = 0;
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: u8 = 0;
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2339_: u8 = 0;
    let mut v_isSharedCheck_2340_: u8 = 0;
    let mut v_unused_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: u8 = 0;
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_aliveRefs_2308_ = lean_ctor_get(v_a_2302_, 0);
                v_refsById_2309_ = lean_ctor_get(v_a_2302_, 1);
                v_nextRef_2310_ = lean_ctor_get_usize(v_a_2302_, 2);
                v_wireFormat_2311_ = lean_ctor_get_uint8(
                    v_a_2302_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v___x_2312_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(v_aliveRefs_2308_, v_r_2301_);
                if lean_obj_tag(v___x_2312_) == 1 {
                    lean_inc_ref(v_refsById_2309_);
                    lean_inc_ref(v_aliveRefs_2308_);
                    v_isSharedCheck_2340_ = (!lean_is_exclusive(v_a_2302_)) as u8;
                    if v_isSharedCheck_2340_ == 0 {
                        v_unused_2341_ = lean_ctor_get(v_a_2302_, 1);
                        lean_dec(v_unused_2341_);
                        v_unused_2342_ = lean_ctor_get(v_a_2302_, 0);
                        lean_dec(v_unused_2342_);
                        v___x_2314_ = v_a_2302_;
                        v_isShared_2315_ = v_isSharedCheck_2340_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_a_2302_);
                        v___x_2314_ = lean_box(0);
                        v_isShared_2315_ = v_isSharedCheck_2340_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2312_);
                    v___x_2343_ = 0;
                    v___x_2344_ = lean_box((v___x_2343_) as usize);
                    v___x_2345_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2345_, 0, v___x_2344_);
                    lean_ctor_set(v___x_2345_, 1, v_a_2302_);
                    return v___x_2345_;
                }
            }
            1 => {
                v___x_2305_ = 1;
                v___x_2306_ = lean_box((v___x_2305_) as usize);
                v___x_2307_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2307_, 0, v___x_2306_);
                lean_ctor_set(v___x_2307_, 1, v___y_2304_);
                return v___x_2307_;
            }
            2 => {
                v_val_2316_ = lean_ctor_get(v___x_2312_, 0);
                lean_inc(v_val_2316_);
                lean_dec_ref_known(v___x_2312_, 1);
                v_obj_2317_ = lean_ctor_get(v_val_2316_, 0);
                v_id_2318_ = lean_ctor_get_usize(v_val_2316_, 2);
                v_rc_2319_ = lean_ctor_get(v_val_2316_, 1);
                v_isSharedCheck_2339_ = (!lean_is_exclusive(v_val_2316_)) as u8;
                if v_isSharedCheck_2339_ == 0 {
                    v___x_2321_ = v_val_2316_;
                    v_isShared_2322_ = v_isSharedCheck_2339_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_rc_2319_);
                    lean_inc(v_obj_2317_);
                    lean_dec(v_val_2316_);
                    v___x_2321_ = lean_box(0);
                    v_isShared_2322_ = v_isSharedCheck_2339_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2323_ = lean_unsigned_to_nat(1);
                v___x_2324_ = lean_nat_sub(v_rc_2319_, v___x_2323_);
                lean_dec(v_rc_2319_);
                v___x_2325_ = lean_unsigned_to_nat(0);
                v___x_2326_ = lean_nat_dec_eq(v___x_2324_, v___x_2325_);
                if v___x_2326_ == 0 {
                    if v_isShared_2322_ == 0 {
                        lean_ctor_set(v___x_2321_, 1, v___x_2324_);
                        v___x_2328_ = v___x_2321_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2333_ =
                            lean_alloc_ctor(0, 2, (core::mem::size_of::<usize>() * 1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_obj_2317_);
                        lean_ctor_set(v_reuseFailAlloc_2333_, 1, v___x_2324_);
                        lean_ctor_set_usize(v_reuseFailAlloc_2333_, 2, v_id_2318_);
                        v___x_2328_ = v_reuseFailAlloc_2333_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2324_);
                    lean_del_object(v___x_2321_);
                    lean_dec(v_obj_2317_);
                    v___x_2334_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(v_aliveRefs_2308_, v_r_2301_);
                    v___x_2335_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(v_refsById_2309_, v_id_2318_);
                    if v_isShared_2315_ == 0 {
                        lean_ctor_set(v___x_2314_, 1, v___x_2335_);
                        lean_ctor_set(v___x_2314_, 0, v___x_2334_);
                        v___x_2337_ = v___x_2314_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2338_ =
                            lean_alloc_ctor(0, 2, (core::mem::size_of::<usize>() * 1 + 1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2334_);
                        lean_ctor_set(v_reuseFailAlloc_2338_, 1, v___x_2335_);
                        lean_ctor_set_usize(v_reuseFailAlloc_2338_, 2, v_nextRef_2310_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2338_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v_wireFormat_2311_,
                        );
                        v___x_2337_ = v_reuseFailAlloc_2338_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2329_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(v_aliveRefs_2308_, v_r_2301_, v___x_2328_);
                if v_isShared_2315_ == 0 {
                    lean_ctor_set(v___x_2314_, 0, v___x_2329_);
                    v___x_2331_ = v___x_2314_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2332_ =
                        lean_alloc_ctor(0, 2, (core::mem::size_of::<usize>() * 1 + 1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
                    lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_refsById_2309_);
                    lean_ctor_set_usize(v_reuseFailAlloc_2332_, 2, v_nextRef_2310_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2332_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_wireFormat_2311_,
                    );
                    v___x_2331_ = v_reuseFailAlloc_2332_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_2304_ = v___x_2331_;
                state = 1;
                continue;
            }
            6 => {
                v___y_2304_ = v___x_2337_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_rpcReleaseRef___boxed(
    mut v_r_2346_: *mut LeanObject,
    mut v_a_2347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_boxed_2348_: usize = 0;
    let mut v_res_2349_: *mut LeanObject = core::ptr::null_mut();
    v_r_boxed_2348_ = lean_unbox_usize(v_r_2346_);
    lean_dec(v_r_2346_);
    v_res_2349_ = l_Lean_Server_rpcReleaseRef(v_r_boxed_2348_, v_a_2347_);
    return v_res_2349_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0(
    mut v_00_u03b2_2350_: *mut LeanObject,
    mut v_x_2351_: *mut LeanObject,
    mut v_x_2352_: usize,
) -> *mut LeanObject {
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    v___x_2353_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(
            v_x_2351_, v_x_2352_,
        );
    return v___x_2353_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___boxed(
    mut v_00_u03b2_2354_: *mut LeanObject,
    mut v_x_2355_: *mut LeanObject,
    mut v_x_2356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2497__boxed_2357_: usize = 0;
    let mut v_res_2358_: *mut LeanObject = core::ptr::null_mut();
    v_x_2497__boxed_2357_ = lean_unbox_usize(v_x_2356_);
    lean_dec(v_x_2356_);
    v_res_2358_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0(
        v_00_u03b2_2354_,
        v_x_2355_,
        v_x_2497__boxed_2357_,
    );
    lean_dec_ref(v_x_2355_);
    return v_res_2358_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1(
    mut v_00_u03b2_2359_: *mut LeanObject,
    mut v_x_2360_: *mut LeanObject,
    mut v_x_2361_: usize,
    mut v_x_2362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    v___x_2363_ =
        l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(
            v_x_2360_, v_x_2361_, v_x_2362_,
        );
    return v___x_2363_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___boxed(
    mut v_00_u03b2_2364_: *mut LeanObject,
    mut v_x_2365_: *mut LeanObject,
    mut v_x_2366_: *mut LeanObject,
    mut v_x_2367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2505__boxed_2368_: usize = 0;
    let mut v_res_2369_: *mut LeanObject = core::ptr::null_mut();
    v_x_2505__boxed_2368_ = lean_unbox_usize(v_x_2366_);
    lean_dec(v_x_2366_);
    v_res_2369_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1(
        v_00_u03b2_2364_,
        v_x_2365_,
        v_x_2505__boxed_2368_,
        v_x_2367_,
    );
    return v_res_2369_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2(
    mut v_00_u03b2_2370_: *mut LeanObject,
    mut v_x_2371_: *mut LeanObject,
    mut v_x_2372_: usize,
) -> *mut LeanObject {
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    v___x_2373_ =
        l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(
            v_x_2371_, v_x_2372_,
        );
    return v___x_2373_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___boxed(
    mut v_00_u03b2_2374_: *mut LeanObject,
    mut v_x_2375_: *mut LeanObject,
    mut v_x_2376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2516__boxed_2377_: usize = 0;
    let mut v_res_2378_: *mut LeanObject = core::ptr::null_mut();
    v_x_2516__boxed_2377_ = lean_unbox_usize(v_x_2376_);
    lean_dec(v_x_2376_);
    v_res_2378_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2(
        v_00_u03b2_2374_,
        v_x_2375_,
        v_x_2516__boxed_2377_,
    );
    return v_res_2378_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3(
    mut v_00_u03b2_2379_: *mut LeanObject,
    mut v_x_2380_: *mut LeanObject,
    mut v_x_2381_: usize,
) -> *mut LeanObject {
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    v___x_2382_ =
        l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(
            v_x_2380_, v_x_2381_,
        );
    return v___x_2382_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___boxed(
    mut v_00_u03b2_2383_: *mut LeanObject,
    mut v_x_2384_: *mut LeanObject,
    mut v_x_2385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2524__boxed_2386_: usize = 0;
    let mut v_res_2387_: *mut LeanObject = core::ptr::null_mut();
    v_x_2524__boxed_2386_ = lean_unbox_usize(v_x_2385_);
    lean_dec(v_x_2385_);
    v_res_2387_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3(
        v_00_u03b2_2383_,
        v_x_2384_,
        v_x_2524__boxed_2386_,
    );
    return v_res_2387_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0(
    mut v_00_u03b2_2388_: *mut LeanObject,
    mut v_x_2389_: *mut LeanObject,
    mut v_x_2390_: usize,
    mut v_x_2391_: usize,
) -> *mut LeanObject {
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    v___x_2392_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(v_x_2389_, v_x_2390_, v_x_2391_);
    return v___x_2392_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___boxed(
    mut v_00_u03b2_2393_: *mut LeanObject,
    mut v_x_2394_: *mut LeanObject,
    mut v_x_2395_: *mut LeanObject,
    mut v_x_2396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2532__boxed_2397_: usize = 0;
    let mut v_x_2533__boxed_2398_: usize = 0;
    let mut v_res_2399_: *mut LeanObject = core::ptr::null_mut();
    v_x_2532__boxed_2397_ = lean_unbox_usize(v_x_2395_);
    lean_dec(v_x_2395_);
    v_x_2533__boxed_2398_ = lean_unbox_usize(v_x_2396_);
    lean_dec(v_x_2396_);
    v_res_2399_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0(v_00_u03b2_2393_, v_x_2394_, v_x_2532__boxed_2397_, v_x_2533__boxed_2398_);
    lean_dec_ref(v_x_2394_);
    return v_res_2399_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2(
    mut v_00_u03b2_2400_: *mut LeanObject,
    mut v_x_2401_: *mut LeanObject,
    mut v_x_2402_: usize,
    mut v_x_2403_: usize,
    mut v_x_2404_: usize,
    mut v_x_2405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    v___x_2406_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_x_2401_, v_x_2402_, v_x_2403_, v_x_2404_, v_x_2405_);
    return v___x_2406_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___boxed(
    mut v_00_u03b2_2407_: *mut LeanObject,
    mut v_x_2408_: *mut LeanObject,
    mut v_x_2409_: *mut LeanObject,
    mut v_x_2410_: *mut LeanObject,
    mut v_x_2411_: *mut LeanObject,
    mut v_x_2412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2543__boxed_2413_: usize = 0;
    let mut v_x_2544__boxed_2414_: usize = 0;
    let mut v_x_2545__boxed_2415_: usize = 0;
    let mut v_res_2416_: *mut LeanObject = core::ptr::null_mut();
    v_x_2543__boxed_2413_ = lean_unbox_usize(v_x_2409_);
    lean_dec(v_x_2409_);
    v_x_2544__boxed_2414_ = lean_unbox_usize(v_x_2410_);
    lean_dec(v_x_2410_);
    v_x_2545__boxed_2415_ = lean_unbox_usize(v_x_2411_);
    lean_dec(v_x_2411_);
    v_res_2416_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2(v_00_u03b2_2407_, v_x_2408_, v_x_2543__boxed_2413_, v_x_2544__boxed_2414_, v_x_2545__boxed_2415_, v_x_2412_);
    return v_res_2416_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4(
    mut v_00_u03b2_2417_: *mut LeanObject,
    mut v_x_2418_: *mut LeanObject,
    mut v_x_2419_: usize,
    mut v_x_2420_: usize,
) -> *mut LeanObject {
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    v___x_2421_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_x_2418_, v_x_2419_, v_x_2420_);
    return v___x_2421_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___boxed(
    mut v_00_u03b2_2422_: *mut LeanObject,
    mut v_x_2423_: *mut LeanObject,
    mut v_x_2424_: *mut LeanObject,
    mut v_x_2425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2560__boxed_2426_: usize = 0;
    let mut v_x_2561__boxed_2427_: usize = 0;
    let mut v_res_2428_: *mut LeanObject = core::ptr::null_mut();
    v_x_2560__boxed_2426_ = lean_unbox_usize(v_x_2424_);
    lean_dec(v_x_2424_);
    v_x_2561__boxed_2427_ = lean_unbox_usize(v_x_2425_);
    lean_dec(v_x_2425_);
    v_res_2428_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4(v_00_u03b2_2422_, v_x_2423_, v_x_2560__boxed_2426_, v_x_2561__boxed_2427_);
    return v_res_2428_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6(
    mut v_00_u03b2_2429_: *mut LeanObject,
    mut v_x_2430_: *mut LeanObject,
    mut v_x_2431_: usize,
    mut v_x_2432_: usize,
) -> *mut LeanObject {
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    v___x_2433_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_x_2430_, v_x_2431_, v_x_2432_);
    return v___x_2433_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___boxed(
    mut v_00_u03b2_2434_: *mut LeanObject,
    mut v_x_2435_: *mut LeanObject,
    mut v_x_2436_: *mut LeanObject,
    mut v_x_2437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2571__boxed_2438_: usize = 0;
    let mut v_x_2572__boxed_2439_: usize = 0;
    let mut v_res_2440_: *mut LeanObject = core::ptr::null_mut();
    v_x_2571__boxed_2438_ = lean_unbox_usize(v_x_2436_);
    lean_dec(v_x_2436_);
    v_x_2572__boxed_2439_ = lean_unbox_usize(v_x_2437_);
    lean_dec(v_x_2437_);
    v_res_2440_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6(v_00_u03b2_2434_, v_x_2435_, v_x_2571__boxed_2438_, v_x_2572__boxed_2439_);
    return v_res_2440_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2441_: *mut LeanObject,
    mut v_keys_2442_: *mut LeanObject,
    mut v_vals_2443_: *mut LeanObject,
    mut v_heq_2444_: *mut LeanObject,
    mut v_i_2445_: *mut LeanObject,
    mut v_k_2446_: usize,
) -> *mut LeanObject {
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    v___x_2447_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(v_keys_2442_, v_vals_2443_, v_i_2445_, v_k_2446_);
    return v___x_2447_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2448_: *mut LeanObject,
    mut v_keys_2449_: *mut LeanObject,
    mut v_vals_2450_: *mut LeanObject,
    mut v_heq_2451_: *mut LeanObject,
    mut v_i_2452_: *mut LeanObject,
    mut v_k_2453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_boxed_2454_: usize = 0;
    let mut v_res_2455_: *mut LeanObject = core::ptr::null_mut();
    v_k_boxed_2454_ = lean_unbox_usize(v_k_2453_);
    lean_dec(v_k_2453_);
    v_res_2455_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1(v_00_u03b2_2448_, v_keys_2449_, v_vals_2450_, v_heq_2451_, v_i_2452_, v_k_boxed_2454_);
    lean_dec_ref(v_vals_2450_);
    lean_dec_ref(v_keys_2449_);
    return v_res_2455_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4(
    mut v_00_u03b2_2456_: *mut LeanObject,
    mut v_n_2457_: *mut LeanObject,
    mut v_k_2458_: usize,
    mut v_v_2459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    v___x_2460_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(v_n_2457_, v_k_2458_, v_v_2459_);
    return v___x_2460_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b2_2461_: *mut LeanObject,
    mut v_n_2462_: *mut LeanObject,
    mut v_k_2463_: *mut LeanObject,
    mut v_v_2464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_boxed_2465_: usize = 0;
    let mut v_res_2466_: *mut LeanObject = core::ptr::null_mut();
    v_k_boxed_2465_ = lean_unbox_usize(v_k_2463_);
    lean_dec(v_k_2463_);
    v_res_2466_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4(v_00_u03b2_2461_, v_n_2462_, v_k_boxed_2465_, v_v_2464_);
    return v_res_2466_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5(
    mut v_00_u03b2_2467_: *mut LeanObject,
    mut v_depth_2468_: usize,
    mut v_keys_2469_: *mut LeanObject,
    mut v_vals_2470_: *mut LeanObject,
    mut v_heq_2471_: *mut LeanObject,
    mut v_i_2472_: *mut LeanObject,
    mut v_entries_2473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    v___x_2474_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(v_depth_2468_, v_keys_2469_, v_vals_2470_, v_i_2472_, v_entries_2473_);
    return v___x_2474_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_2475_: *mut LeanObject,
    mut v_depth_2476_: *mut LeanObject,
    mut v_keys_2477_: *mut LeanObject,
    mut v_vals_2478_: *mut LeanObject,
    mut v_heq_2479_: *mut LeanObject,
    mut v_i_2480_: *mut LeanObject,
    mut v_entries_2481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2482_: usize = 0;
    let mut v_res_2483_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2482_ = lean_unbox_usize(v_depth_2476_);
    lean_dec(v_depth_2476_);
    v_res_2483_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5(v_00_u03b2_2475_, v_depth_boxed_2482_, v_keys_2477_, v_vals_2478_, v_heq_2479_, v_i_2480_, v_entries_2481_);
    lean_dec_ref(v_vals_2478_);
    lean_dec_ref(v_keys_2477_);
    return v_res_2483_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7(
    mut v_00_u03b2_2484_: *mut LeanObject,
    mut v_x_2485_: *mut LeanObject,
    mut v_x_2486_: *mut LeanObject,
    mut v_x_2487_: usize,
    mut v_x_2488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    v___x_2489_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(v_x_2485_, v_x_2486_, v_x_2487_, v_x_2488_);
    return v___x_2489_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___boxed(
    mut v_00_u03b2_2490_: *mut LeanObject,
    mut v_x_2491_: *mut LeanObject,
    mut v_x_2492_: *mut LeanObject,
    mut v_x_2493_: *mut LeanObject,
    mut v_x_2494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2589__boxed_2495_: usize = 0;
    let mut v_res_2496_: *mut LeanObject = core::ptr::null_mut();
    v_x_2589__boxed_2495_ = lean_unbox_usize(v_x_2493_);
    lean_dec(v_x_2493_);
    v_res_2496_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7(v_00_u03b2_2490_, v_x_2491_, v_x_2492_, v_x_2589__boxed_2495_, v_x_2494_);
    return v_res_2496_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__0(
    mut v_inst_2497_: *mut LeanObject,
    mut v_a_2498_: *mut LeanObject,
    mut v___y_2499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    v___x_2500_ = lean_apply_1(v_inst_2497_, v_a_2498_);
    v___x_2501_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2501_, 0, v___x_2500_);
    lean_ctor_set(v___x_2501_, 1, v___y_2499_);
    return v___x_2501_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1(
    mut v_inst_2502_: *mut LeanObject,
    mut v___x_2503_: *mut LeanObject,
    mut v___x_2504_: *mut LeanObject,
    mut v_j_2505_: *mut LeanObject,
    mut v___y_2506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_201__overap_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    v___x_2507_ = lean_apply_1(v_inst_2502_, v_j_2505_);
    v___x_201__overap_2508_ =
        l_MonadExcept_ofExcept___redArg(v___x_2503_, v___x_2504_, v___x_2507_);
    lean_inc_ref(v___y_2506_);
    v___x_2509_ = lean_apply_1(v___x_201__overap_2508_, v___y_2506_);
    return v___x_2509_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1___boxed(
    mut v_inst_2510_: *mut LeanObject,
    mut v___x_2511_: *mut LeanObject,
    mut v___x_2512_: *mut LeanObject,
    mut v_j_2513_: *mut LeanObject,
    mut v___y_2514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2515_: *mut LeanObject = core::ptr::null_mut();
    v_res_2515_ = l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1(
        v_inst_2510_,
        v___x_2511_,
        v___x_2512_,
        v_j_2513_,
        v___y_2514_,
    );
    lean_dec_ref(v___y_2514_);
    return v_res_2515_;
}
pub unsafe fn _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10()
-> *mut LeanObject {
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    v___x_2535_ = l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9;
    v___x_2536_ = l_ReaderT_instMonad___redArg(v___x_2535_);
    return v___x_2536_;
}
pub unsafe fn _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2538_: *mut LeanObject = core::ptr::null_mut();
    v___x_2537_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once
        ),
        _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10,
    );
    v___f_2538_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_2538_, 0, v___x_2537_);
    return v___f_2538_;
}
pub unsafe fn _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12()
-> *mut LeanObject {
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2540_: *mut LeanObject = core::ptr::null_mut();
    v___x_2539_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once
        ),
        _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10,
    );
    v___f_2540_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_2540_, 0, v___x_2539_);
    return v___f_2540_;
}
pub unsafe fn _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2542_: *mut LeanObject = core::ptr::null_mut();
    v___x_2541_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once
        ),
        _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10,
    );
    v___f_2542_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_2542_, 0, v___x_2541_);
    return v___f_2542_;
}
pub unsafe fn _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14()
-> *mut LeanObject {
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2544_: *mut LeanObject = core::ptr::null_mut();
    v___x_2543_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once
        ),
        _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10,
    );
    v___f_2544_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_2544_, 0, v___x_2543_);
    return v___f_2544_;
}
pub unsafe fn _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    v___x_2545_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once
        ),
        _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10,
    );
    v___x_2546_ = lean_alloc_closure(l_ExceptT_map as *mut core::ffi::c_void, 7, 3);
    lean_closure_set(v___x_2546_, 0, lean_box(0));
    lean_closure_set(v___x_2546_, 1, lean_box(0));
    lean_closure_set(v___x_2546_, 2, v___x_2545_);
    return v___x_2546_;
}
pub unsafe fn _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16()
-> *mut LeanObject {
    let mut v___f_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    v___f_2547_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11_once
        ),
        _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11,
    );
    v___x_2548_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15_once
        ),
        _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15,
    );
    v___x_2549_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2549_, 0, v___x_2548_);
    lean_ctor_set(v___x_2549_, 1, v___f_2547_);
    return v___x_2549_;
}
pub unsafe fn _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    v___x_2550_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once
        ),
        _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10,
    );
    v___x_2551_ = lean_alloc_closure(l_ExceptT_pure as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_2551_, 0, lean_box(0));
    lean_closure_set(v___x_2551_, 1, lean_box(0));
    lean_closure_set(v___x_2551_, 2, v___x_2550_);
    return v___x_2551_;
}
pub unsafe fn _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18()
-> *mut LeanObject {
    let mut v___f_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    v___f_2552_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14_once
        ),
        _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14,
    );
    v___f_2553_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13_once
        ),
        _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13,
    );
    v___f_2554_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12_once
        ),
        _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12,
    );
    v___x_2555_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17_once
        ),
        _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17,
    );
    v___x_2556_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16_once
        ),
        _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16,
    );
    v___x_2557_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_2557_, 0, v___x_2556_);
    lean_ctor_set(v___x_2557_, 1, v___x_2555_);
    lean_ctor_set(v___x_2557_, 2, v___f_2554_);
    lean_ctor_set(v___x_2557_, 3, v___f_2553_);
    lean_ctor_set(v___x_2557_, 4, v___f_2552_);
    return v___x_2557_;
}
pub unsafe fn _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    v___x_2558_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once
        ),
        _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10,
    );
    v___x_2559_ = lean_alloc_closure(l_ExceptT_bind as *mut core::ffi::c_void, 7, 3);
    lean_closure_set(v___x_2559_, 0, lean_box(0));
    lean_closure_set(v___x_2559_, 1, lean_box(0));
    lean_closure_set(v___x_2559_, 2, v___x_2558_);
    return v___x_2559_;
}
pub unsafe fn _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20()
-> *mut LeanObject {
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    v___x_2560_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19_once
        ),
        _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19,
    );
    v___x_2561_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18_once
        ),
        _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18,
    );
    v___x_2562_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2562_, 0, v___x_2561_);
    lean_ctor_set(v___x_2562_, 1, v___x_2560_);
    return v___x_2562_;
}
pub unsafe fn _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21()
-> *mut LeanObject {
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    v___x_2563_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once
        ),
        _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10,
    );
    v___x_2564_ = lean_alloc_closure(l_ExceptT_tryCatch as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_2564_, 0, lean_box(0));
    lean_closure_set(v___x_2564_, 1, lean_box(0));
    lean_closure_set(v___x_2564_, 2, v___x_2563_);
    return v___x_2564_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg(
    mut v_inst_2565_: *mut LeanObject,
    mut v_inst_2566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    v___x_2567_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once
        ),
        _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10,
    );
    v___x_2568_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20_once
        ),
        _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20,
    );
    v_toApplicative_2569_ = lean_ctor_get(v___x_2567_, 0);
    v_toPure_2570_ = lean_ctor_get(v_toApplicative_2569_, 1);
    v___f_2571_ = lean_alloc_closure(
        l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2571_, 0, v_inst_2566_);
    lean_inc(v_toPure_2570_);
    v___f_2572_ = lean_alloc_closure(
        l_instMonadExceptOfExceptTOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2572_, 0, v_toPure_2570_);
    v___x_2573_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21_once
        ),
        _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21,
    );
    v___x_2574_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2574_, 0, v___f_2572_);
    lean_ctor_set(v___x_2574_, 1, v___x_2573_);
    v___x_2575_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_2574_);
    v___f_2576_ = lean_alloc_closure(
        l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_2576_, 0, v_inst_2565_);
    lean_closure_set(v___f_2576_, 1, v___x_2568_);
    lean_closure_set(v___f_2576_, 2, v___x_2575_);
    v___x_2577_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2577_, 0, v___f_2571_);
    lean_ctor_set(v___x_2577_, 1, v___f_2576_);
    return v___x_2577_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableOfFromJsonOfToJson(
    mut v_00_u03b1_2578_: *mut LeanObject,
    mut v_inst_2579_: *mut LeanObject,
    mut v_inst_2580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    v___x_2581_ =
        l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg(v_inst_2579_, v_inst_2580_);
    return v___x_2581_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableOption___redArg___lam__0(
    mut v_inst_2582_: *mut LeanObject,
    mut v___x_2583_: *mut LeanObject,
    mut v_v_2584_: *mut LeanObject,
    mut v___y_2585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rpcEncode_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2596_: u8 = 0;
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_2584_) == 0 {
                    lean_dec_ref(v_inst_2582_);
                    v___x_2591_ = lean_box(0);
                    v_fst_2587_ = v___x_2591_;
                    v_snd_2588_ = v___y_2585_;
                    state = 1;
                    continue;
                } else {
                    v_rpcEncode_2592_ = lean_ctor_get(v_inst_2582_, 0);
                    lean_inc_ref(v_rpcEncode_2592_);
                    lean_dec_ref(v_inst_2582_);
                    v_val_2593_ = lean_ctor_get(v_v_2584_, 0);
                    v_isSharedCheck_2603_ = (!lean_is_exclusive(v_v_2584_)) as u8;
                    if v_isSharedCheck_2603_ == 0 {
                        v___x_2595_ = v_v_2584_;
                        v_isShared_2596_ = v_isSharedCheck_2603_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_2593_);
                        lean_dec(v_v_2584_);
                        v___x_2595_ = lean_box(0);
                        v_isShared_2596_ = v_isSharedCheck_2603_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2589_ = l_Option_toJson___redArg(v___x_2583_, v_fst_2587_);
                v___x_2590_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2590_, 0, v___x_2589_);
                lean_ctor_set(v___x_2590_, 1, v_snd_2588_);
                return v___x_2590_;
            }
            2 => {
                v___x_2597_ = lean_apply_2(v_rpcEncode_2592_, v_val_2593_, v___y_2585_);
                v_fst_2598_ = lean_ctor_get(v___x_2597_, 0);
                lean_inc(v_fst_2598_);
                v_snd_2599_ = lean_ctor_get(v___x_2597_, 1);
                lean_inc(v_snd_2599_);
                lean_dec_ref(v___x_2597_);
                if v_isShared_2596_ == 0 {
                    lean_ctor_set(v___x_2595_, 0, v_fst_2598_);
                    v___x_2601_ = v___x_2595_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_fst_2598_);
                    v___x_2601_ = v_reuseFailAlloc_2602_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_2587_ = v___x_2601_;
                v_snd_2588_ = v_snd_2599_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_instRpcEncodableOption___redArg___lam__1(
    mut v___f_2606_: *mut LeanObject,
    mut v_inst_2607_: *mut LeanObject,
    mut v_j_2608_: *mut LeanObject,
    mut v___y_2609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2614_: u8 = 0;
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2618_: u8 = 0;
    let mut v_a_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rpcDecode_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2625_: u8 = 0;
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2630_: u8 = 0;
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2634_: u8 = 0;
    let mut v_a_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2638_: u8 = 0;
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2645_: u8 = 0;
    let mut v_isSharedCheck_2646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2610_ = l_Option_fromJson_x3f___redArg(v___f_2606_, v_j_2608_);
                if lean_obj_tag(v___x_2610_) == 0 {
                    lean_dec_ref(v_inst_2607_);
                    v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
                    v_isSharedCheck_2618_ = (!lean_is_exclusive(v___x_2610_)) as u8;
                    if v_isSharedCheck_2618_ == 0 {
                        v___x_2613_ = v___x_2610_;
                        v_isShared_2614_ = v_isSharedCheck_2618_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2611_);
                        lean_dec(v___x_2610_);
                        v___x_2613_ = lean_box(0);
                        v_isShared_2614_ = v_isSharedCheck_2618_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2619_ = lean_ctor_get(v___x_2610_, 0);
                    lean_inc(v_a_2619_);
                    lean_dec_ref_known(v___x_2610_, 1);
                    if lean_obj_tag(v_a_2619_) == 0 {
                        lean_dec_ref(v_inst_2607_);
                        v___x_2620_ =
                            l_Lean_Server_instRpcEncodableOption___redArg___lam__1___closed__0;
                        return v___x_2620_;
                    } else {
                        v_rpcDecode_2621_ = lean_ctor_get(v_inst_2607_, 1);
                        lean_inc_ref(v_rpcDecode_2621_);
                        lean_dec_ref(v_inst_2607_);
                        v_val_2622_ = lean_ctor_get(v_a_2619_, 0);
                        v_isSharedCheck_2646_ = (!lean_is_exclusive(v_a_2619_)) as u8;
                        if v_isSharedCheck_2646_ == 0 {
                            v___x_2624_ = v_a_2619_;
                            v_isShared_2625_ = v_isSharedCheck_2646_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_2622_);
                            lean_dec(v_a_2619_);
                            v___x_2624_ = lean_box(0);
                            v_isShared_2625_ = v_isSharedCheck_2646_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2614_ == 0 {
                    v___x_2616_ = v___x_2613_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
                    v___x_2616_ = v_reuseFailAlloc_2617_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2616_;
            }
            3 => {
                lean_inc_ref(v___y_2609_);
                v___x_2626_ = lean_apply_2(v_rpcDecode_2621_, v_val_2622_, v___y_2609_);
                if lean_obj_tag(v___x_2626_) == 0 {
                    lean_del_object(v___x_2624_);
                    v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
                    v_isSharedCheck_2634_ = (!lean_is_exclusive(v___x_2626_)) as u8;
                    if v_isSharedCheck_2634_ == 0 {
                        v___x_2629_ = v___x_2626_;
                        v_isShared_2630_ = v_isSharedCheck_2634_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2627_);
                        lean_dec(v___x_2626_);
                        v___x_2629_ = lean_box(0);
                        v_isShared_2630_ = v_isSharedCheck_2634_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_2635_ = lean_ctor_get(v___x_2626_, 0);
                    v_isSharedCheck_2645_ = (!lean_is_exclusive(v___x_2626_)) as u8;
                    if v_isSharedCheck_2645_ == 0 {
                        v___x_2637_ = v___x_2626_;
                        v_isShared_2638_ = v_isSharedCheck_2645_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2635_);
                        lean_dec(v___x_2626_);
                        v___x_2637_ = lean_box(0);
                        v_isShared_2638_ = v_isSharedCheck_2645_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2630_ == 0 {
                    v___x_2632_ = v___x_2629_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
                    v___x_2632_ = v_reuseFailAlloc_2633_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2632_;
            }
            6 => {
                if v_isShared_2625_ == 0 {
                    lean_ctor_set(v___x_2624_, 0, v_a_2635_);
                    v___x_2640_ = v___x_2624_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2635_);
                    v___x_2640_ = v_reuseFailAlloc_2644_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2638_ == 0 {
                    lean_ctor_set(v___x_2637_, 0, v___x_2640_);
                    v___x_2642_ = v___x_2637_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2640_);
                    v___x_2642_ = v_reuseFailAlloc_2643_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2642_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_instRpcEncodableOption___redArg___lam__1___boxed(
    mut v___f_2647_: *mut LeanObject,
    mut v_inst_2648_: *mut LeanObject,
    mut v_j_2649_: *mut LeanObject,
    mut v___y_2650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2651_: *mut LeanObject = core::ptr::null_mut();
    v_res_2651_ = l_Lean_Server_instRpcEncodableOption___redArg___lam__1(
        v___f_2647_,
        v_inst_2648_,
        v_j_2649_,
        v___y_2650_,
    );
    lean_dec_ref(v___y_2650_);
    return v_res_2651_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableOption___redArg(
    mut v_inst_2654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    v___x_2655_ = l_Lean_Server_instRpcEncodableOption___redArg___closed__0;
    lean_inc_ref(v_inst_2654_);
    v___f_2656_ = lean_alloc_closure(
        l_Lean_Server_instRpcEncodableOption___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2656_, 0, v_inst_2654_);
    lean_closure_set(v___f_2656_, 1, v___x_2655_);
    v___f_2657_ = l_Lean_Server_instRpcEncodableOption___redArg___closed__1;
    v___f_2658_ = lean_alloc_closure(
        l_Lean_Server_instRpcEncodableOption___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2658_, 0, v___f_2657_);
    lean_closure_set(v___f_2658_, 1, v_inst_2654_);
    v___x_2659_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2659_, 0, v___f_2656_);
    lean_ctor_set(v___x_2659_, 1, v___f_2658_);
    return v___x_2659_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableOption(
    mut v_00_u03b1_2660_: *mut LeanObject,
    mut v_inst_2661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    v___x_2662_ = l_Lean_Server_instRpcEncodableOption___redArg(v_inst_2661_);
    return v___x_2662_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableArray___redArg___lam__0(
    mut v_inst_2663_: *mut LeanObject,
    mut v___x_2664_: *mut LeanObject,
    mut v___x_2665_: *mut LeanObject,
    mut v_a_2666_: *mut LeanObject,
    mut v___y_2667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_rpcEncode_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2669_: usize = 0;
    let mut v___x_2670_: usize = 0;
    let mut v___x_648__overap_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2677_: u8 = 0;
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2682_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rpcEncode_2668_ = lean_ctor_get(v_inst_2663_, 0);
                lean_inc_ref(v_rpcEncode_2668_);
                lean_dec_ref(v_inst_2663_);
                v_sz_2669_ = lean_array_size(v_a_2666_);
                v___x_2670_ = 0usize;
                v___x_648__overap_2671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_2664_,
                    v_rpcEncode_2668_,
                    v_sz_2669_,
                    v___x_2670_,
                    v_a_2666_,
                );
                v___x_2672_ = lean_apply_1(v___x_648__overap_2671_, v___y_2667_);
                v_fst_2673_ = lean_ctor_get(v___x_2672_, 0);
                v_snd_2674_ = lean_ctor_get(v___x_2672_, 1);
                v_isSharedCheck_2682_ = (!lean_is_exclusive(v___x_2672_)) as u8;
                if v_isSharedCheck_2682_ == 0 {
                    v___x_2676_ = v___x_2672_;
                    v_isShared_2677_ = v_isSharedCheck_2682_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2674_);
                    lean_inc(v_fst_2673_);
                    lean_dec(v___x_2672_);
                    v___x_2676_ = lean_box(0);
                    v_isShared_2677_ = v_isSharedCheck_2682_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2678_ = l_Array_toJson___redArg(v___x_2665_, v_fst_2673_);
                if v_isShared_2677_ == 0 {
                    lean_ctor_set(v___x_2676_, 0, v___x_2678_);
                    v___x_2680_ = v___x_2676_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2678_);
                    lean_ctor_set(v_reuseFailAlloc_2681_, 1, v_snd_2674_);
                    v___x_2680_ = v_reuseFailAlloc_2681_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2680_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_instRpcEncodableArray___redArg___lam__1(
    mut v___f_2683_: *mut LeanObject,
    mut v_inst_2684_: *mut LeanObject,
    mut v___x_2685_: *mut LeanObject,
    mut v_b_2686_: *mut LeanObject,
    mut v___y_2687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2692_: u8 = 0;
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2696_: u8 = 0;
    let mut v_a_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rpcDecode_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2699_: usize = 0;
    let mut v___x_2700_: usize = 0;
    let mut v___x_662__overap_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2688_ = l_Array_fromJson_x3f___redArg(v___f_2683_, v_b_2686_);
                if lean_obj_tag(v___x_2688_) == 0 {
                    lean_dec_ref(v___x_2685_);
                    lean_dec_ref(v_inst_2684_);
                    v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
                    v_isSharedCheck_2696_ = (!lean_is_exclusive(v___x_2688_)) as u8;
                    if v_isSharedCheck_2696_ == 0 {
                        v___x_2691_ = v___x_2688_;
                        v_isShared_2692_ = v_isSharedCheck_2696_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2689_);
                        lean_dec(v___x_2688_);
                        v___x_2691_ = lean_box(0);
                        v_isShared_2692_ = v_isSharedCheck_2696_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2697_ = lean_ctor_get(v___x_2688_, 0);
                    lean_inc(v_a_2697_);
                    lean_dec_ref_known(v___x_2688_, 1);
                    v_rpcDecode_2698_ = lean_ctor_get(v_inst_2684_, 1);
                    lean_inc_ref(v_rpcDecode_2698_);
                    lean_dec_ref(v_inst_2684_);
                    v_sz_2699_ = lean_array_size(v_a_2697_);
                    v___x_2700_ = 0usize;
                    v___x_662__overap_2701_ =
                        l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
                            v___x_2685_,
                            v_rpcDecode_2698_,
                            v_sz_2699_,
                            v___x_2700_,
                            v_a_2697_,
                        );
                    lean_inc_ref(v___y_2687_);
                    v___x_2702_ = lean_apply_1(v___x_662__overap_2701_, v___y_2687_);
                    return v___x_2702_;
                }
            }
            1 => {
                if v_isShared_2692_ == 0 {
                    v___x_2694_ = v___x_2691_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
                    v___x_2694_ = v_reuseFailAlloc_2695_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2694_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_instRpcEncodableArray___redArg___lam__1___boxed(
    mut v___f_2703_: *mut LeanObject,
    mut v_inst_2704_: *mut LeanObject,
    mut v___x_2705_: *mut LeanObject,
    mut v_b_2706_: *mut LeanObject,
    mut v___y_2707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2708_: *mut LeanObject = core::ptr::null_mut();
    v_res_2708_ = l_Lean_Server_instRpcEncodableArray___redArg___lam__1(
        v___f_2703_,
        v_inst_2704_,
        v___x_2705_,
        v_b_2706_,
        v___y_2707_,
    );
    lean_dec_ref(v___y_2707_);
    return v_res_2708_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableArray___redArg(
    mut v_inst_2735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    v___x_2736_ = l_Lean_Server_instRpcEncodableArray___redArg___closed__9;
    v___x_2737_ = l_Lean_Server_instRpcEncodableOption___redArg___closed__0;
    lean_inc_ref(v_inst_2735_);
    v___f_2738_ = lean_alloc_closure(
        l_Lean_Server_instRpcEncodableArray___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_2738_, 0, v_inst_2735_);
    lean_closure_set(v___f_2738_, 1, v___x_2736_);
    lean_closure_set(v___f_2738_, 2, v___x_2737_);
    v___x_2739_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20_once
        ),
        _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20,
    );
    v___f_2740_ = l_Lean_Server_instRpcEncodableOption___redArg___closed__1;
    v___f_2741_ = lean_alloc_closure(
        l_Lean_Server_instRpcEncodableArray___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_2741_, 0, v___f_2740_);
    lean_closure_set(v___f_2741_, 1, v_inst_2735_);
    lean_closure_set(v___f_2741_, 2, v___x_2739_);
    v___x_2742_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2742_, 0, v___f_2738_);
    lean_ctor_set(v___x_2742_, 1, v___f_2741_);
    return v___x_2742_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableArray(
    mut v_00_u03b1_2743_: *mut LeanObject,
    mut v_inst_2744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    v___x_2745_ = l_Lean_Server_instRpcEncodableArray___redArg(v_inst_2744_);
    return v___x_2745_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableProd___redArg___lam__0(
    mut v_inst_2746_: *mut LeanObject,
    mut v_inst_2747_: *mut LeanObject,
    mut v___x_2748_: *mut LeanObject,
    mut v_x_2749_: *mut LeanObject,
    mut v___y_2750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rpcEncode_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2759_: u8 = 0;
    let mut v_rpcEncode_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2766_: u8 = 0;
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2774_: u8 = 0;
    let mut v_isSharedCheck_2775_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2751_ = lean_ctor_get(v_x_2749_, 0);
                lean_inc(v_fst_2751_);
                v_snd_2752_ = lean_ctor_get(v_x_2749_, 1);
                lean_inc(v_snd_2752_);
                lean_dec_ref(v_x_2749_);
                v_rpcEncode_2753_ = lean_ctor_get(v_inst_2746_, 0);
                lean_inc_ref(v_rpcEncode_2753_);
                lean_dec_ref(v_inst_2746_);
                v___x_2754_ = lean_apply_2(v_rpcEncode_2753_, v_fst_2751_, v___y_2750_);
                v_fst_2755_ = lean_ctor_get(v___x_2754_, 0);
                v_snd_2756_ = lean_ctor_get(v___x_2754_, 1);
                v_isSharedCheck_2775_ = (!lean_is_exclusive(v___x_2754_)) as u8;
                if v_isSharedCheck_2775_ == 0 {
                    v___x_2758_ = v___x_2754_;
                    v_isShared_2759_ = v_isSharedCheck_2775_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2756_);
                    lean_inc(v_fst_2755_);
                    lean_dec(v___x_2754_);
                    v___x_2758_ = lean_box(0);
                    v_isShared_2759_ = v_isSharedCheck_2775_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_rpcEncode_2760_ = lean_ctor_get(v_inst_2747_, 0);
                lean_inc_ref(v_rpcEncode_2760_);
                lean_dec_ref(v_inst_2747_);
                v___x_2761_ = lean_apply_2(v_rpcEncode_2760_, v_snd_2752_, v_snd_2756_);
                v_fst_2762_ = lean_ctor_get(v___x_2761_, 0);
                v_snd_2763_ = lean_ctor_get(v___x_2761_, 1);
                v_isSharedCheck_2774_ = (!lean_is_exclusive(v___x_2761_)) as u8;
                if v_isSharedCheck_2774_ == 0 {
                    v___x_2765_ = v___x_2761_;
                    v_isShared_2766_ = v_isSharedCheck_2774_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_2763_);
                    lean_inc(v_fst_2762_);
                    lean_dec(v___x_2761_);
                    v___x_2765_ = lean_box(0);
                    v_isShared_2766_ = v_isSharedCheck_2774_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2766_ == 0 {
                    lean_ctor_set(v___x_2765_, 1, v_fst_2762_);
                    lean_ctor_set(v___x_2765_, 0, v_fst_2755_);
                    v___x_2768_ = v___x_2765_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_fst_2755_);
                    lean_ctor_set(v_reuseFailAlloc_2773_, 1, v_fst_2762_);
                    v___x_2768_ = v_reuseFailAlloc_2773_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___x_2748_);
                v___x_2769_ = l_Prod_toJson___redArg(v___x_2748_, v___x_2748_, v___x_2768_);
                if v_isShared_2759_ == 0 {
                    lean_ctor_set(v___x_2758_, 1, v_snd_2763_);
                    lean_ctor_set(v___x_2758_, 0, v___x_2769_);
                    v___x_2771_ = v___x_2758_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2769_);
                    lean_ctor_set(v_reuseFailAlloc_2772_, 1, v_snd_2763_);
                    v___x_2771_ = v_reuseFailAlloc_2772_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2771_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_instRpcEncodableProd___redArg___lam__1(
    mut v___f_2776_: *mut LeanObject,
    mut v_inst_2777_: *mut LeanObject,
    mut v_inst_2778_: *mut LeanObject,
    mut v_j_2779_: *mut LeanObject,
    mut v___y_2780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2785_: u8 = 0;
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2789_: u8 = 0;
    let mut v_a_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2795_: u8 = 0;
    let mut v_rpcDecode_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2801_: u8 = 0;
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2805_: u8 = 0;
    let mut v_a_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rpcDecode_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2812_: u8 = 0;
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2816_: u8 = 0;
    let mut v_a_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2820_: u8 = 0;
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2827_: u8 = 0;
    let mut v_isSharedCheck_2828_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v___f_2776_);
                v___x_2781_ = l_Prod_fromJson_x3f___redArg(v___f_2776_, v___f_2776_, v_j_2779_);
                if lean_obj_tag(v___x_2781_) == 0 {
                    lean_dec_ref(v_inst_2778_);
                    lean_dec_ref(v_inst_2777_);
                    v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
                    v_isSharedCheck_2789_ = (!lean_is_exclusive(v___x_2781_)) as u8;
                    if v_isSharedCheck_2789_ == 0 {
                        v___x_2784_ = v___x_2781_;
                        v_isShared_2785_ = v_isSharedCheck_2789_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2782_);
                        lean_dec(v___x_2781_);
                        v___x_2784_ = lean_box(0);
                        v_isShared_2785_ = v_isSharedCheck_2789_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2790_ = lean_ctor_get(v___x_2781_, 0);
                    lean_inc(v_a_2790_);
                    lean_dec_ref_known(v___x_2781_, 1);
                    v_fst_2791_ = lean_ctor_get(v_a_2790_, 0);
                    v_snd_2792_ = lean_ctor_get(v_a_2790_, 1);
                    v_isSharedCheck_2828_ = (!lean_is_exclusive(v_a_2790_)) as u8;
                    if v_isSharedCheck_2828_ == 0 {
                        v___x_2794_ = v_a_2790_;
                        v_isShared_2795_ = v_isSharedCheck_2828_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_snd_2792_);
                        lean_inc(v_fst_2791_);
                        lean_dec(v_a_2790_);
                        v___x_2794_ = lean_box(0);
                        v_isShared_2795_ = v_isSharedCheck_2828_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2785_ == 0 {
                    v___x_2787_ = v___x_2784_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
                    v___x_2787_ = v_reuseFailAlloc_2788_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2787_;
            }
            3 => {
                v_rpcDecode_2796_ = lean_ctor_get(v_inst_2777_, 1);
                lean_inc_ref(v_rpcDecode_2796_);
                lean_dec_ref(v_inst_2777_);
                lean_inc_ref(v___y_2780_);
                v___x_2797_ = lean_apply_2(v_rpcDecode_2796_, v_fst_2791_, v___y_2780_);
                if lean_obj_tag(v___x_2797_) == 0 {
                    lean_del_object(v___x_2794_);
                    lean_dec(v_snd_2792_);
                    lean_dec_ref(v_inst_2778_);
                    v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
                    v_isSharedCheck_2805_ = (!lean_is_exclusive(v___x_2797_)) as u8;
                    if v_isSharedCheck_2805_ == 0 {
                        v___x_2800_ = v___x_2797_;
                        v_isShared_2801_ = v_isSharedCheck_2805_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2798_);
                        lean_dec(v___x_2797_);
                        v___x_2800_ = lean_box(0);
                        v_isShared_2801_ = v_isSharedCheck_2805_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_2806_ = lean_ctor_get(v___x_2797_, 0);
                    lean_inc(v_a_2806_);
                    lean_dec_ref_known(v___x_2797_, 1);
                    v_rpcDecode_2807_ = lean_ctor_get(v_inst_2778_, 1);
                    lean_inc_ref(v_rpcDecode_2807_);
                    lean_dec_ref(v_inst_2778_);
                    lean_inc_ref(v___y_2780_);
                    v___x_2808_ = lean_apply_2(v_rpcDecode_2807_, v_snd_2792_, v___y_2780_);
                    if lean_obj_tag(v___x_2808_) == 0 {
                        lean_dec(v_a_2806_);
                        lean_del_object(v___x_2794_);
                        v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
                        v_isSharedCheck_2816_ = (!lean_is_exclusive(v___x_2808_)) as u8;
                        if v_isSharedCheck_2816_ == 0 {
                            v___x_2811_ = v___x_2808_;
                            v_isShared_2812_ = v_isSharedCheck_2816_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2809_);
                            lean_dec(v___x_2808_);
                            v___x_2811_ = lean_box(0);
                            v_isShared_2812_ = v_isSharedCheck_2816_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_2817_ = lean_ctor_get(v___x_2808_, 0);
                        v_isSharedCheck_2827_ = (!lean_is_exclusive(v___x_2808_)) as u8;
                        if v_isSharedCheck_2827_ == 0 {
                            v___x_2819_ = v___x_2808_;
                            v_isShared_2820_ = v_isSharedCheck_2827_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_2817_);
                            lean_dec(v___x_2808_);
                            v___x_2819_ = lean_box(0);
                            v_isShared_2820_ = v_isSharedCheck_2827_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_2801_ == 0 {
                    v___x_2803_ = v___x_2800_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2798_);
                    v___x_2803_ = v_reuseFailAlloc_2804_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2803_;
            }
            6 => {
                if v_isShared_2812_ == 0 {
                    v___x_2814_ = v___x_2811_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
                    v___x_2814_ = v_reuseFailAlloc_2815_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2814_;
            }
            8 => {
                if v_isShared_2795_ == 0 {
                    lean_ctor_set(v___x_2794_, 1, v_a_2817_);
                    lean_ctor_set(v___x_2794_, 0, v_a_2806_);
                    v___x_2822_ = v___x_2794_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2806_);
                    lean_ctor_set(v_reuseFailAlloc_2826_, 1, v_a_2817_);
                    v___x_2822_ = v_reuseFailAlloc_2826_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2820_ == 0 {
                    lean_ctor_set(v___x_2819_, 0, v___x_2822_);
                    v___x_2824_ = v___x_2819_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2822_);
                    v___x_2824_ = v_reuseFailAlloc_2825_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2824_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_instRpcEncodableProd___redArg___lam__1___boxed(
    mut v___f_2829_: *mut LeanObject,
    mut v_inst_2830_: *mut LeanObject,
    mut v_inst_2831_: *mut LeanObject,
    mut v_j_2832_: *mut LeanObject,
    mut v___y_2833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2834_: *mut LeanObject = core::ptr::null_mut();
    v_res_2834_ = l_Lean_Server_instRpcEncodableProd___redArg___lam__1(
        v___f_2829_,
        v_inst_2830_,
        v_inst_2831_,
        v_j_2832_,
        v___y_2833_,
    );
    lean_dec_ref(v___y_2833_);
    return v_res_2834_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableProd___redArg(
    mut v_inst_2835_: *mut LeanObject,
    mut v_inst_2836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    v___x_2837_ = l_Lean_Server_instRpcEncodableOption___redArg___closed__0;
    lean_inc_ref(v_inst_2836_);
    lean_inc_ref(v_inst_2835_);
    v___f_2838_ = lean_alloc_closure(
        l_Lean_Server_instRpcEncodableProd___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_2838_, 0, v_inst_2835_);
    lean_closure_set(v___f_2838_, 1, v_inst_2836_);
    lean_closure_set(v___f_2838_, 2, v___x_2837_);
    v___f_2839_ = l_Lean_Server_instRpcEncodableOption___redArg___closed__1;
    v___f_2840_ = lean_alloc_closure(
        l_Lean_Server_instRpcEncodableProd___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_2840_, 0, v___f_2839_);
    lean_closure_set(v___f_2840_, 1, v_inst_2835_);
    lean_closure_set(v___f_2840_, 2, v_inst_2836_);
    v___x_2841_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2841_, 0, v___f_2838_);
    lean_ctor_set(v___x_2841_, 1, v___f_2840_);
    return v___x_2841_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableProd(
    mut v_00_u03b1_2842_: *mut LeanObject,
    mut v_00_u03b2_2843_: *mut LeanObject,
    mut v_inst_2844_: *mut LeanObject,
    mut v_inst_2845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    v___x_2846_ = l_Lean_Server_instRpcEncodableProd___redArg(v_inst_2844_, v_inst_2845_);
    return v___x_2846_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__0(
    mut v_inst_2847_: *mut LeanObject,
    mut v_fn_2848_: *mut LeanObject,
    mut v___y_2849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_rpcEncode_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    v_rpcEncode_2850_ = lean_ctor_get(v_inst_2847_, 0);
    lean_inc_ref(v_rpcEncode_2850_);
    lean_dec_ref(v_inst_2847_);
    v___x_2851_ = lean_apply_1(v_fn_2848_, v___y_2849_);
    v_fst_2852_ = lean_ctor_get(v___x_2851_, 0);
    lean_inc(v_fst_2852_);
    v_snd_2853_ = lean_ctor_get(v___x_2851_, 1);
    lean_inc(v_snd_2853_);
    lean_dec_ref(v___x_2851_);
    v___x_2854_ = lean_apply_2(v_rpcEncode_2850_, v_fst_2852_, v_snd_2853_);
    return v___x_2854_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1(
    mut v_inst_2855_: *mut LeanObject,
    mut v___x_2856_: *mut LeanObject,
    mut v_j_2857_: *mut LeanObject,
    mut v___y_2858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_rpcDecode_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2864_: u8 = 0;
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2868_: u8 = 0;
    let mut v_a_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2872_: u8 = 0;
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2877_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rpcDecode_2859_ = lean_ctor_get(v_inst_2855_, 1);
                lean_inc_ref(v_rpcDecode_2859_);
                lean_dec_ref(v_inst_2855_);
                lean_inc_ref(v___y_2858_);
                v___x_2860_ = lean_apply_2(v_rpcDecode_2859_, v_j_2857_, v___y_2858_);
                if lean_obj_tag(v___x_2860_) == 0 {
                    lean_dec_ref(v___x_2856_);
                    v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
                    v_isSharedCheck_2868_ = (!lean_is_exclusive(v___x_2860_)) as u8;
                    if v_isSharedCheck_2868_ == 0 {
                        v___x_2863_ = v___x_2860_;
                        v_isShared_2864_ = v_isSharedCheck_2868_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2861_);
                        lean_dec(v___x_2860_);
                        v___x_2863_ = lean_box(0);
                        v_isShared_2864_ = v_isSharedCheck_2868_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2869_ = lean_ctor_get(v___x_2860_, 0);
                    v_isSharedCheck_2877_ = (!lean_is_exclusive(v___x_2860_)) as u8;
                    if v_isSharedCheck_2877_ == 0 {
                        v___x_2871_ = v___x_2860_;
                        v_isShared_2872_ = v_isSharedCheck_2877_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2869_);
                        lean_dec(v___x_2860_);
                        v___x_2871_ = lean_box(0);
                        v_isShared_2872_ = v_isSharedCheck_2877_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2864_ == 0 {
                    v___x_2866_ = v___x_2863_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
                    v___x_2866_ = v_reuseFailAlloc_2867_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2866_;
            }
            3 => {
                v___x_2873_ = lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 5);
                lean_closure_set(v___x_2873_, 0, lean_box(0));
                lean_closure_set(v___x_2873_, 1, lean_box(0));
                lean_closure_set(v___x_2873_, 2, v___x_2856_);
                lean_closure_set(v___x_2873_, 3, lean_box(0));
                lean_closure_set(v___x_2873_, 4, v_a_2869_);
                if v_isShared_2872_ == 0 {
                    lean_ctor_set(v___x_2871_, 0, v___x_2873_);
                    v___x_2875_ = v___x_2871_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2873_);
                    v___x_2875_ = v_reuseFailAlloc_2876_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2875_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1___boxed(
    mut v_inst_2878_: *mut LeanObject,
    mut v___x_2879_: *mut LeanObject,
    mut v_j_2880_: *mut LeanObject,
    mut v___y_2881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2882_: *mut LeanObject = core::ptr::null_mut();
    v_res_2882_ = l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1(
        v_inst_2878_,
        v___x_2879_,
        v_j_2880_,
        v___y_2881_,
    );
    lean_dec_ref(v___y_2881_);
    return v_res_2882_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg(
    mut v_inst_2883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_2883_);
    v___f_2884_ = lean_alloc_closure(
        l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2884_, 0, v_inst_2883_);
    v___x_2885_ = l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9;
    v___f_2886_ = lean_alloc_closure(
        l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2886_, 0, v_inst_2883_);
    lean_closure_set(v___f_2886_, 1, v___x_2885_);
    v___x_2887_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2887_, 0, v___f_2884_);
    lean_ctor_set(v___x_2887_, 1, v___f_2886_);
    return v___x_2887_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableStateMRpcObjectStore(
    mut v_00_u03b1_2888_: *mut LeanObject,
    mut v_inst_2889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    v___x_2890_ = l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg(v_inst_2889_);
    return v___x_2890_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(
    mut v_inst_2891_: *mut LeanObject,
    mut v_r_2892_: *mut LeanObject,
    mut v_a_2893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2899_: u8 = 0;
    let mut v___y_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: usize = 0;
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wireFormat_2912_: u8 = 0;
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2915_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2894_ =
                    l_Lean_Server_rpcStoreRef___redArg(v_inst_2891_, v_r_2892_, v_a_2893_);
                v_fst_2895_ = lean_ctor_get(v___x_2894_, 0);
                v_snd_2896_ = lean_ctor_get(v___x_2894_, 1);
                v_isSharedCheck_2915_ = (!lean_is_exclusive(v___x_2894_)) as u8;
                if v_isSharedCheck_2915_ == 0 {
                    v___x_2898_ = v___x_2894_;
                    v_isShared_2899_ = v_isSharedCheck_2915_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2896_);
                    lean_inc(v_fst_2895_);
                    lean_dec(v___x_2894_);
                    v___x_2898_ = lean_box(0);
                    v_isShared_2899_ = v_isSharedCheck_2915_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_wireFormat_2912_ = lean_ctor_get_uint8(
                    v_snd_2896_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                if v_wireFormat_2912_ == 0 {
                    v___x_2913_ = l_Lean_Lsp_RpcWireFormat_refFieldName___closed__0;
                    v___y_2901_ = v___x_2913_;
                    state = 2;
                    continue;
                } else {
                    v___x_2914_ = l_Lean_Lsp_RpcWireFormat_refFieldName___closed__1;
                    v___y_2901_ = v___x_2914_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2902_ = lean_unbox_usize(v_fst_2895_);
                lean_dec(v_fst_2895_);
                v___x_2903_ = lean_usize_to_nat(v___x_2902_);
                v___x_2904_ = l_Lean_bignumToJson(v___x_2903_);
                lean_inc_ref(v___y_2901_);
                if v_isShared_2899_ == 0 {
                    lean_ctor_set(v___x_2898_, 1, v___x_2904_);
                    lean_ctor_set(v___x_2898_, 0, v___y_2901_);
                    v___x_2906_ = v___x_2898_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___y_2901_);
                    lean_ctor_set(v_reuseFailAlloc_2911_, 1, v___x_2904_);
                    v___x_2906_ = v_reuseFailAlloc_2911_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2907_ = lean_box(0);
                v___x_2908_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2908_, 0, v___x_2906_);
                lean_ctor_set(v___x_2908_, 1, v___x_2907_);
                v___x_2909_ = l_Lean_Json_mkObj(v___x_2908_);
                lean_dec_ref_known(v___x_2908_, 2);
                v___x_2910_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2910_, 0, v___x_2909_);
                lean_ctor_set(v___x_2910_, 1, v_snd_2896_);
                return v___x_2910_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg___boxed(
    mut v_inst_2916_: *mut LeanObject,
    mut v_r_2917_: *mut LeanObject,
    mut v_a_2918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2919_: *mut LeanObject = core::ptr::null_mut();
    v_res_2919_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(
        v_inst_2916_,
        v_r_2917_,
        v_a_2918_,
    );
    lean_dec_ref(v_r_2917_);
    return v_res_2919_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode(
    mut v_00_u03b1_2920_: *mut LeanObject,
    mut v_inst_2921_: *mut LeanObject,
    mut v_r_2922_: *mut LeanObject,
    mut v_a_2923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    v___x_2924_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(
        v_inst_2921_,
        v_r_2922_,
        v_a_2923_,
    );
    return v___x_2924_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___boxed(
    mut v_00_u03b1_2925_: *mut LeanObject,
    mut v_inst_2926_: *mut LeanObject,
    mut v_r_2927_: *mut LeanObject,
    mut v_a_2928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2929_: *mut LeanObject = core::ptr::null_mut();
    v_res_2929_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode(
        v_00_u03b1_2925_,
        v_inst_2926_,
        v_r_2927_,
        v_a_2928_,
    );
    lean_dec_ref(v_r_2927_);
    return v_res_2929_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(
    mut v_inst_2931_: *mut LeanObject,
    mut v_j_2932_: *mut LeanObject,
    mut v_a_2933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_wireFormat_2934_: u8 = 0;
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2942_: u8 = 0;
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2946_: u8 = 0;
    let mut v_a_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: usize = 0;
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_wireFormat_2934_ = lean_ctor_get_uint8(
                    v_a_2933_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v___x_2935_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg___closed__0;
                if v_wireFormat_2934_ == 0 {
                    v___x_2950_ = l_Lean_Lsp_RpcWireFormat_refFieldName___closed__0;
                    v___y_2937_ = v___x_2950_;
                    state = 1;
                    continue;
                } else {
                    v___x_2951_ = l_Lean_Lsp_RpcWireFormat_refFieldName___closed__1;
                    v___y_2937_ = v___x_2951_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2938_ =
                    l_Lean_Json_getObjValAs_x3f___redArg(v_j_2932_, v___x_2935_, v___y_2937_);
                if lean_obj_tag(v___x_2938_) == 0 {
                    lean_dec(v_inst_2931_);
                    v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
                    v_isSharedCheck_2946_ = (!lean_is_exclusive(v___x_2938_)) as u8;
                    if v_isSharedCheck_2946_ == 0 {
                        v___x_2941_ = v___x_2938_;
                        v_isShared_2942_ = v_isSharedCheck_2946_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2939_);
                        lean_dec(v___x_2938_);
                        v___x_2941_ = lean_box(0);
                        v_isShared_2942_ = v_isSharedCheck_2946_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2947_ = lean_ctor_get(v___x_2938_, 0);
                    lean_inc(v_a_2947_);
                    lean_dec_ref_known(v___x_2938_, 1);
                    v___x_2948_ = lean_unbox_usize(v_a_2947_);
                    lean_dec(v_a_2947_);
                    v___x_2949_ =
                        l_Lean_Server_rpcGetRef___redArg(v_inst_2931_, v___x_2948_, v_a_2933_);
                    return v___x_2949_;
                }
            }
            2 => {
                if v_isShared_2942_ == 0 {
                    v___x_2944_ = v___x_2941_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
                    v___x_2944_ = v_reuseFailAlloc_2945_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2944_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg___boxed(
    mut v_inst_2952_: *mut LeanObject,
    mut v_j_2953_: *mut LeanObject,
    mut v_a_2954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2955_: *mut LeanObject = core::ptr::null_mut();
    v_res_2955_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(
        v_inst_2952_,
        v_j_2953_,
        v_a_2954_,
    );
    lean_dec_ref(v_a_2954_);
    return v_res_2955_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode(
    mut v_00_u03b1_2956_: *mut LeanObject,
    mut v_inst_2957_: *mut LeanObject,
    mut v_j_2958_: *mut LeanObject,
    mut v_a_2959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    v___x_2960_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(
        v_inst_2957_,
        v_j_2958_,
        v_a_2959_,
    );
    return v___x_2960_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___boxed(
    mut v_00_u03b1_2961_: *mut LeanObject,
    mut v_inst_2962_: *mut LeanObject,
    mut v_j_2963_: *mut LeanObject,
    mut v_a_2964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2965_: *mut LeanObject = core::ptr::null_mut();
    v_res_2965_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode(
        v_00_u03b1_2961_,
        v_inst_2962_,
        v_j_2963_,
        v_a_2964_,
    );
    lean_dec_ref(v_a_2964_);
    return v_res_2965_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName___redArg(
    mut v_inst_2966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_inst_2966_);
    v___x_2967_ = lean_alloc_closure(
        l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_2967_, 0, lean_box(0));
    lean_closure_set(v___x_2967_, 1, v_inst_2966_);
    v___x_2968_ = lean_alloc_closure(
        l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_2968_, 0, lean_box(0));
    lean_closure_set(v___x_2968_, 1, v_inst_2966_);
    v___x_2969_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2969_, 0, v___x_2967_);
    lean_ctor_set(v___x_2969_, 1, v___x_2968_);
    return v___x_2969_;
}
pub unsafe fn l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName(
    mut v_00_u03b1_2970_: *mut LeanObject,
    mut v_inst_2971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    v___x_2972_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName___redArg(v_inst_2971_);
    return v___x_2972_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_Rpc_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Dynamic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Json_FromToJson_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Lsp_instInhabitedRpcRef_default = _init_l_Lean_Lsp_instInhabitedRpcRef_default();
    l_Lean_Lsp_instInhabitedRpcRef = _init_l_Lean_Lsp_instInhabitedRpcRef();
    res = l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Server_freshWithRpcRefId = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Server_freshWithRpcRefId);
    lean_dec_ref(res);
    l_Lean_Server_rpcStoreRef___redArg___boxed__const__1 =
        _init_l_Lean_Server_rpcStoreRef___redArg___boxed__const__1();
    lean_mark_persistent(l_Lean_Server_rpcStoreRef___redArg___boxed__const__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_Rpc_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_Rpc_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Dynamic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_Json_FromToJson_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Rpc_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Server_Rpc_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Server_Rpc_Basic(builtin);
}
