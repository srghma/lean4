// Lean compiler output
// Module: Lean.Data.Lsp.TextSync
// Imports: Lean.Data.Lsp.Basic
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr3};
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getBool_x3f, l_Lean_Json_getNat_x3f, l_Lean_Json_getObjValD,
    l_Lean_Json_getStr_x3f, l_Lean_Json_mkObj, l_Lean_JsonNumber_fromNat,
};
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::l_Lean_Json_getObjValAs_x3f___redArg;
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_pretty;
use crate::r#gen::Lean::Data::Lsp::Basic::{
    initialize_Lean_Data_Lsp_Basic, l_Lean_Lsp_instFromJsonDocumentFilter_fromJson,
    l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson,
    l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson,
    l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson,
    l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson,
    l_Lean_Lsp_instToJsonTextDocumentItem_toJson,
    l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson,
    runtime_initialize_Lean_Data_Lsp_Basic,
};
use crate::r#gen::Lean::Data::Lsp::BasicAux::{
    l_Lean_Lsp_instFromJsonRange_fromJson, l_Lean_Lsp_instToJsonRange_toJson,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_box,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__0_value:
    LeanStringObject<29> = LeanStringObject {
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
        117, 110, 107, 110, 111, 119, 110, 32, 84, 101, 120, 116, 68, 111, 99, 117, 109, 101, 110,
        116, 83, 121, 110, 99, 75, 105, 110, 100, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__1_value: LeanCtorObject<
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
        l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__2_value: LeanCtorObject<
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
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__3_value: LeanCtorObject<
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
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__4_value: LeanCtorObject<
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
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncKind___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonTextDocumentSyncKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instToJsonTextDocumentSyncKind___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncKind___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonTextDocumentSyncKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncKind___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0_value:
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
static mut l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1_value:
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
static mut l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonDidOpenTextDocumentParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonDidOpenTextDocumentParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonDidOpenTextDocumentParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value:
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
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value:
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
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__2_value:
    LeanStringObject<26> = LeanStringObject {
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
        68, 105, 100, 79, 112, 101, 110, 84, 101, 120, 116, 68, 111, 99, 117, 109, 101, 110, 116,
        80, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__2_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3_value_aux_0:
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
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3_value_aux_1:
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
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value
        ) as *mut LeanObject,
        6773744487318448338 as *mut LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3_value:
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
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__2_value
        ) as *mut LeanObject,
        1777096150718724193 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5_value:
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
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0_value)
            as *mut LeanObject,
        18338692295241883607 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10_value:
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
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10_value
)
    as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams___closed__0_value: LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams___closed__0_value)
        as *mut LeanObject;
pub static l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0_value) as *mut LeanObject;
pub static l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1_value) as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__0_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [100, 111, 99, 117, 109, 101, 110, 116, 83, 101, 108, 101, 99, 116, 111, 114, 0]};
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__1_value: LeanStringObject<38> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [84, 101, 120, 116, 68, 111, 99, 117, 109, 101, 110, 116, 67, 104, 97, 110, 103, 101, 82, 101, 103, 105, 115, 116, 114, 97, 116, 105, 111, 110, 79, 112, 116, 105, 111, 110, 115, 0]};
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__1_value
) as *mut LeanObject;
static l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value) as *mut LeanObject,6773744487318448338 as *mut LeanObject] };
pub static l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__1_value) as *mut LeanObject,17376441392313824390 as *mut LeanObject] };
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2_value
) as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__5_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [100, 111, 99, 117, 109, 101, 110, 116, 83, 101, 108, 101, 99, 116, 111, 114, 63, 0]};
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__5_value
) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__5_value) as *mut LeanObject,14662850476098908763 as *mut LeanObject] };
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__6_value
) as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__10_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 121, 110, 99, 75, 105, 110, 100, 0]};
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__10_value
) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__10_value) as *mut LeanObject,9751881898413921770 as *mut LeanObject] };
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__11_value
) as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions___closed__0_value
) as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0_value:
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
    m_data: [116, 101, 120, 116, 0],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1_value:
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
static mut l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonRange_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__1_value:
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
    m_fun: l_Lean_Json_getStr_x3f as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__2_value:
    LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__1_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__0_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__2_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson___closed__0_value:
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
    m_fun: l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0_value:
    LeanStringObject<15> = LeanStringObject {
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
        99, 111, 110, 116, 101, 110, 116, 67, 104, 97, 110, 103, 101, 115, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonDidChangeTextDocumentParams___closed__0_value: LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonDidChangeTextDocumentParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidChangeTextDocumentParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonDidChangeTextDocumentParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidChangeTextDocumentParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__0_value:
    LeanStringObject<28> = LeanStringObject {
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
        68, 105, 100, 67, 104, 97, 110, 103, 101, 84, 101, 120, 116, 68, 111, 99, 117, 109, 101,
        110, 116, 80, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__0_value
) as *mut LeanObject;
static l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1_value_aux_0:
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
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1_value_aux_1:
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
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value
        ) as *mut LeanObject,
        6773744487318448338 as *mut LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1_value:
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
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__0_value
        ) as *mut LeanObject,
        17982117513186199655 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1_value
) as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__6_value:
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
            l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0_value
        ) as *mut LeanObject,
        17232133447220150647 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__6_value
) as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams___closed__0_value: LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonDidSaveTextDocumentParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonDidSaveTextDocumentParams_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonDidSaveTextDocumentParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidSaveTextDocumentParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonDidSaveTextDocumentParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidSaveTextDocumentParams___closed__0_value)
        as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__0_value:
    LeanStringObject<26> = LeanStringObject {
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
        68, 105, 100, 83, 97, 118, 101, 84, 101, 120, 116, 68, 111, 99, 117, 109, 101, 110, 116,
        80, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__0_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1_value_aux_0:
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
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1_value_aux_1:
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
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value
        ) as *mut LeanObject,
        6773744487318448338 as *mut LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1_value:
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
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__0_value
        ) as *mut LeanObject,
        12587282521778334376 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__6_value:
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
    m_data: [116, 101, 120, 116, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__7_value:
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
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__6_value
        ) as *mut LeanObject,
        2082988283416480631 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams___closed__0_value: LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0_value: LeanStringObject<12> =
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
        m_data: [105, 110, 99, 108, 117, 100, 101, 84, 101, 120, 116, 0],
    };
static mut l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonSaveOptions___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonSaveOptions_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonSaveOptions___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonSaveOptions___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonSaveOptions: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonSaveOptions___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__0_value: LeanStringObject<12> =
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
        m_data: [83, 97, 118, 101, 79, 112, 116, 105, 111, 110, 115, 0],
    };
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__0_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1_value_aux_0: LeanCtorObject<3> =
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
                l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value
            ) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value
            ) as *mut LeanObject,
            6773744487318448338 as *mut LeanObject,
        ],
    };
pub static l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__0_value)
                as *mut LeanObject,
            9731365713045262675 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0_value)
                as *mut LeanObject,
            15217983757875996411 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonSaveOptions___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonSaveOptions_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonSaveOptions___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonSaveOptions___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonSaveOptions: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonSaveOptions___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonDidCloseTextDocumentParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonDidCloseTextDocumentParams_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonDidCloseTextDocumentParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidCloseTextDocumentParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonDidCloseTextDocumentParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidCloseTextDocumentParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__0_value:
    LeanStringObject<27> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        68, 105, 100, 67, 108, 111, 115, 101, 84, 101, 120, 116, 68, 111, 99, 117, 109, 101, 110,
        116, 80, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__0_value
)
    as *mut LeanObject;
static l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1_value_aux_0:
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
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1_value_aux_1:
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
            l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value
        ) as *mut LeanObject,
        6773744487318448338 as *mut LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1_value:
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
            l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__0_value
        ) as *mut LeanObject,
        308332401153831253 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1_value
)
    as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams___closed__0_value: LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0_value: LeanStringObject<
    10,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [111, 112, 101, 110, 67, 108, 111, 115, 101, 0],
};
static mut l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1_value: LeanStringObject<
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
    m_data: [99, 104, 97, 110, 103, 101, 0],
};
static mut l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2_value: LeanStringObject<
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
    m_data: [119, 105, 108, 108, 83, 97, 118, 101, 0],
};
static mut l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3_value: LeanStringObject<
    18,
> = LeanStringObject {
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
        119, 105, 108, 108, 83, 97, 118, 101, 87, 97, 105, 116, 85, 110, 116, 105, 108, 0,
    ],
};
static mut l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__4_value: LeanStringObject<
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
    m_data: [115, 97, 118, 101, 0],
};
static mut l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonTextDocumentSyncOptions___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonTextDocumentSyncOptions___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncOptions___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonTextDocumentSyncOptions: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncOptions___closed__0_value)
        as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__0_value:
    LeanStringObject<24> = LeanStringObject {
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
        84, 101, 120, 116, 68, 111, 99, 117, 109, 101, 110, 116, 83, 121, 110, 99, 79, 112, 116,
        105, 111, 110, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__0_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1_value_aux_0:
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
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1_value_aux_1:
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
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value
        ) as *mut LeanObject,
        6773744487318448338 as *mut LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1_value:
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
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__0_value
        ) as *mut LeanObject,
        4958612648835839449 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0_value)
            as *mut LeanObject,
        9134419134227876233 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1_value)
            as *mut LeanObject,
        13755659578849458301 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__12_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2_value)
            as *mut LeanObject,
        12861593690867574868 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__16_value:
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
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3_value)
            as *mut LeanObject,
        15946133124393108346 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__16_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__20_value:
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
    m_data: [115, 97, 118, 101, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__20_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__21_value:
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
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__20_value
        ) as *mut LeanObject,
        12047597270034623148 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__21_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonTextDocumentSyncOptions: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_ctorIdx(mut v_x_1308_: u8) -> *mut LeanObject {
    match v_x_1308_ {
        0 => {
            let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
            v___x_1309_ = lean_unsigned_to_nat(0);
            return v___x_1309_;
        }
        1 => {
            let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
            v___x_1310_ = lean_unsigned_to_nat(1);
            return v___x_1310_;
        }
        _ => {
            let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
            v___x_1311_ = lean_unsigned_to_nat(2);
            return v___x_1311_;
        }
    }
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_ctorIdx___boxed(
    mut v_x_1312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_1313_: u8 = 0;
    let mut v_res_1314_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_1313_ = (lean_unbox(v_x_1312_) as u8);
    v_res_1314_ = l_Lean_Lsp_TextDocumentSyncKind_ctorIdx(v_x_boxed_1313_);
    return v_res_1314_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_toCtorIdx(mut v_x_1315_: u8) -> *mut LeanObject {
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    v___x_1316_ = l_Lean_Lsp_TextDocumentSyncKind_ctorIdx(v_x_1315_);
    return v___x_1316_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_toCtorIdx___boxed(
    mut v_x_1317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_1318_: u8 = 0;
    let mut v_res_1319_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1318_ = (lean_unbox(v_x_1317_) as u8);
    v_res_1319_ = l_Lean_Lsp_TextDocumentSyncKind_toCtorIdx(v_x_4__boxed_1318_);
    return v_res_1319_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_ctorElim___redArg(
    mut v_k_1320_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_1320_);
    return v_k_1320_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_ctorElim___redArg___boxed(
    mut v_k_1321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1322_: *mut LeanObject = core::ptr::null_mut();
    v_res_1322_ = l_Lean_Lsp_TextDocumentSyncKind_ctorElim___redArg(v_k_1321_);
    lean_dec(v_k_1321_);
    return v_res_1322_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_ctorElim(
    mut v_motive_1323_: *mut LeanObject,
    mut v_ctorIdx_1324_: *mut LeanObject,
    mut v_t_1325_: u8,
    mut v_h_1326_: *mut LeanObject,
    mut v_k_1327_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_1327_);
    return v_k_1327_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_ctorElim___boxed(
    mut v_motive_1328_: *mut LeanObject,
    mut v_ctorIdx_1329_: *mut LeanObject,
    mut v_t_1330_: *mut LeanObject,
    mut v_h_1331_: *mut LeanObject,
    mut v_k_1332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1333_: u8 = 0;
    let mut v_res_1334_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1333_ = (lean_unbox(v_t_1330_) as u8);
    v_res_1334_ = l_Lean_Lsp_TextDocumentSyncKind_ctorElim(
        v_motive_1328_,
        v_ctorIdx_1329_,
        v_t_boxed_1333_,
        v_h_1331_,
        v_k_1332_,
    );
    lean_dec(v_k_1332_);
    lean_dec(v_ctorIdx_1329_);
    return v_res_1334_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_none_elim___redArg(
    mut v_none_1335_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_none_1335_);
    return v_none_1335_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_none_elim___redArg___boxed(
    mut v_none_1336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1337_: *mut LeanObject = core::ptr::null_mut();
    v_res_1337_ = l_Lean_Lsp_TextDocumentSyncKind_none_elim___redArg(v_none_1336_);
    lean_dec(v_none_1336_);
    return v_res_1337_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_none_elim(
    mut v_motive_1338_: *mut LeanObject,
    mut v_t_1339_: u8,
    mut v_h_1340_: *mut LeanObject,
    mut v_none_1341_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_none_1341_);
    return v_none_1341_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_none_elim___boxed(
    mut v_motive_1342_: *mut LeanObject,
    mut v_t_1343_: *mut LeanObject,
    mut v_h_1344_: *mut LeanObject,
    mut v_none_1345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1346_: u8 = 0;
    let mut v_res_1347_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1346_ = (lean_unbox(v_t_1343_) as u8);
    v_res_1347_ = l_Lean_Lsp_TextDocumentSyncKind_none_elim(
        v_motive_1342_,
        v_t_boxed_1346_,
        v_h_1344_,
        v_none_1345_,
    );
    lean_dec(v_none_1345_);
    return v_res_1347_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_full_elim___redArg(
    mut v_full_1348_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_full_1348_);
    return v_full_1348_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_full_elim___redArg___boxed(
    mut v_full_1349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1350_: *mut LeanObject = core::ptr::null_mut();
    v_res_1350_ = l_Lean_Lsp_TextDocumentSyncKind_full_elim___redArg(v_full_1349_);
    lean_dec(v_full_1349_);
    return v_res_1350_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_full_elim(
    mut v_motive_1351_: *mut LeanObject,
    mut v_t_1352_: u8,
    mut v_h_1353_: *mut LeanObject,
    mut v_full_1354_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_full_1354_);
    return v_full_1354_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_full_elim___boxed(
    mut v_motive_1355_: *mut LeanObject,
    mut v_t_1356_: *mut LeanObject,
    mut v_h_1357_: *mut LeanObject,
    mut v_full_1358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1359_: u8 = 0;
    let mut v_res_1360_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1359_ = (lean_unbox(v_t_1356_) as u8);
    v_res_1360_ = l_Lean_Lsp_TextDocumentSyncKind_full_elim(
        v_motive_1355_,
        v_t_boxed_1359_,
        v_h_1357_,
        v_full_1358_,
    );
    lean_dec(v_full_1358_);
    return v_res_1360_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___redArg(
    mut v_incremental_1361_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_incremental_1361_);
    return v_incremental_1361_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___redArg___boxed(
    mut v_incremental_1362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1363_: *mut LeanObject = core::ptr::null_mut();
    v_res_1363_ = l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___redArg(v_incremental_1362_);
    lean_dec(v_incremental_1362_);
    return v_res_1363_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_incremental_elim(
    mut v_motive_1364_: *mut LeanObject,
    mut v_t_1365_: u8,
    mut v_h_1366_: *mut LeanObject,
    mut v_incremental_1367_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_incremental_1367_);
    return v_incremental_1367_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___boxed(
    mut v_motive_1368_: *mut LeanObject,
    mut v_t_1369_: *mut LeanObject,
    mut v_h_1370_: *mut LeanObject,
    mut v_incremental_1371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1372_: u8 = 0;
    let mut v_res_1373_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1372_ = (lean_unbox(v_t_1369_) as u8);
    v_res_1373_ = l_Lean_Lsp_TextDocumentSyncKind_incremental_elim(
        v_motive_1368_,
        v_t_boxed_1372_,
        v_h_1370_,
        v_incremental_1371_,
    );
    lean_dec(v_incremental_1371_);
    return v_res_1373_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0(
    mut v_j_1386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: u8 = 0;
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: u8 = 0;
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: u8 = 0;
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1389_ = l_Lean_Json_getNat_x3f(v_j_1386_);
                if lean_obj_tag(v___x_1389_) == 1 {
                    v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
                    lean_inc(v_a_1390_);
                    lean_dec_ref_known(v___x_1389_, 1);
                    v___x_1391_ = lean_unsigned_to_nat(0);
                    v___x_1392_ = lean_nat_dec_eq(v_a_1390_, v___x_1391_);
                    if v___x_1392_ == 0 {
                        v___x_1393_ = lean_unsigned_to_nat(1);
                        v___x_1394_ = lean_nat_dec_eq(v_a_1390_, v___x_1393_);
                        if v___x_1394_ == 0 {
                            v___x_1395_ = lean_unsigned_to_nat(2);
                            v___x_1396_ = lean_nat_dec_eq(v_a_1390_, v___x_1395_);
                            lean_dec(v_a_1390_);
                            if v___x_1396_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                v___x_1397_ = l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__2;
                                return v___x_1397_;
                            }
                        } else {
                            lean_dec(v_a_1390_);
                            v___x_1398_ =
                                l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__3;
                            return v___x_1398_;
                        }
                    } else {
                        lean_dec(v_a_1390_);
                        v___x_1399_ =
                            l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__4;
                        return v___x_1399_;
                    }
                } else {
                    lean_dec_ref(v___x_1389_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1388_ = l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__1;
                return v___x_1388_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    v___x_1402_ = lean_unsigned_to_nat(0);
    v___x_1403_ = l_Lean_JsonNumber_fromNat(v___x_1402_);
    return v___x_1403_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    v___x_1404_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0_once
        ),
        _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0,
    );
    v___x_1405_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_1405_, 0, v___x_1404_);
    return v___x_1405_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    v___x_1406_ = lean_unsigned_to_nat(1);
    v___x_1407_ = l_Lean_JsonNumber_fromNat(v___x_1406_);
    return v___x_1407_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    v___x_1408_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2_once
        ),
        _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2,
    );
    v___x_1409_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_1409_, 0, v___x_1408_);
    return v___x_1409_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4()
-> *mut LeanObject {
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    v___x_1410_ = lean_unsigned_to_nat(2);
    v___x_1411_ = l_Lean_JsonNumber_fromNat(v___x_1410_);
    return v___x_1411_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5()
-> *mut LeanObject {
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    v___x_1412_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4_once
        ),
        _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4,
    );
    v___x_1413_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_1413_, 0, v___x_1412_);
    return v___x_1413_;
}
pub unsafe fn l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0(
    mut v_x_1414_: u8,
) -> *mut LeanObject {
    match v_x_1414_ {
        0 => {
            let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
            v___x_1415_ = lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1_once
                ),
                _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1,
            );
            return v___x_1415_;
        }
        1 => {
            let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
            v___x_1416_ = lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3_once
                ),
                _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3,
            );
            return v___x_1416_;
        }
        _ => {
            let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
            v___x_1417_ = lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5_once
                ),
                _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5,
            );
            return v___x_1417_;
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___boxed(
    mut v_x_1418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_81__boxed_1419_: u8 = 0;
    let mut v_res_1420_: *mut LeanObject = core::ptr::null_mut();
    v_x_81__boxed_1419_ = (lean_unbox(v_x_1418_) as u8);
    v_res_1420_ = l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0(v_x_81__boxed_1419_);
    return v_res_1420_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(
    mut v_a_1423_: *mut LeanObject,
    mut v_a_1424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1423_) == 0 {
                    v___x_1425_ = lean_array_to_list(v_a_1424_);
                    return v___x_1425_;
                } else {
                    v_head_1426_ = lean_ctor_get(v_a_1423_, 0);
                    lean_inc(v_head_1426_);
                    v_tail_1427_ = lean_ctor_get(v_a_1423_, 1);
                    lean_inc(v_tail_1427_);
                    lean_dec_ref_known(v_a_1423_, 2);
                    v___x_1428_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_1424_,
                        v_head_1426_,
                    );
                    v_a_1423_ = v_tail_1427_;
                    v_a_1424_ = v___x_1428_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson(
    mut v_x_1433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    v___x_1434_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0;
    v___x_1435_ = l_Lean_Lsp_instToJsonTextDocumentItem_toJson(v_x_1433_);
    v___x_1436_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1436_, 0, v___x_1434_);
    lean_ctor_set(v___x_1436_, 1, v___x_1435_);
    v___x_1437_ = lean_box(0);
    v___x_1438_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1438_, 0, v___x_1436_);
    lean_ctor_set(v___x_1438_, 1, v___x_1437_);
    v___x_1439_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1439_, 0, v___x_1438_);
    lean_ctor_set(v___x_1439_, 1, v___x_1437_);
    v___x_1440_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1;
    v___x_1441_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_1439_, v___x_1440_);
    v___x_1442_ = l_Lean_Json_mkObj(v___x_1441_);
    lean_dec(v___x_1441_);
    return v___x_1442_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson_spec__0(
    mut v_j_1445_: *mut LeanObject,
    mut v_k_1446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    v___x_1447_ = l_Lean_Json_getObjValD(v_j_1445_, v_k_1446_);
    v___x_1448_ = l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson(v___x_1447_);
    return v___x_1448_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson_spec__0___boxed(
    mut v_j_1449_: *mut LeanObject,
    mut v_k_1450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1451_: *mut LeanObject = core::ptr::null_mut();
    v_res_1451_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson_spec__0(v_j_1449_, v_k_1450_);
    lean_dec_ref(v_k_1450_);
    return v_res_1451_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4()
-> *mut LeanObject {
    let mut v___x_1459_: u8 = 0;
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    v___x_1459_ = 1;
    v___x_1460_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3;
    v___x_1461_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1460_, v___x_1459_);
    return v___x_1461_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6()
-> *mut LeanObject {
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    v___x_1463_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5;
    v___x_1464_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4,
    );
    v___x_1465_ = lean_string_append(v___x_1464_, v___x_1463_);
    return v___x_1465_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8()
-> *mut LeanObject {
    let mut v___x_1468_: u8 = 0;
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    v___x_1468_ = 1;
    v___x_1469_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__7;
    v___x_1470_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1469_, v___x_1468_);
    return v___x_1470_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9()
-> *mut LeanObject {
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    v___x_1471_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8,
    );
    v___x_1472_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6,
    );
    v___x_1473_ = lean_string_append(v___x_1472_, v___x_1471_);
    return v___x_1473_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11()
-> *mut LeanObject {
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    v___x_1475_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_1476_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9,
    );
    v___x_1477_ = lean_string_append(v___x_1476_, v___x_1475_);
    return v___x_1477_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson(
    mut v_json_1478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1484_: u8 = 0;
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1490_: u8 = 0;
    let mut v_a_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1494_: u8 = 0;
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1498_: u8 = 0;
    let mut v_a_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1502_: u8 = 0;
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1479_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0;
                v___x_1480_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson_spec__0(v_json_1478_, v___x_1479_);
                if lean_obj_tag(v___x_1480_) == 0 {
                    v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
                    v_isSharedCheck_1490_ = (!lean_is_exclusive(v___x_1480_)) as u8;
                    if v_isSharedCheck_1490_ == 0 {
                        v___x_1483_ = v___x_1480_;
                        v_isShared_1484_ = v_isSharedCheck_1490_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1481_);
                        lean_dec(v___x_1480_);
                        v___x_1483_ = lean_box(0);
                        v_isShared_1484_ = v_isSharedCheck_1490_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_1480_) == 0 {
                        v_a_1491_ = lean_ctor_get(v___x_1480_, 0);
                        v_isSharedCheck_1498_ = (!lean_is_exclusive(v___x_1480_)) as u8;
                        if v_isSharedCheck_1498_ == 0 {
                            v___x_1493_ = v___x_1480_;
                            v_isShared_1494_ = v_isSharedCheck_1498_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1491_);
                            lean_dec(v___x_1480_);
                            v___x_1493_ = lean_box(0);
                            v_isShared_1494_ = v_isSharedCheck_1498_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1499_ = lean_ctor_get(v___x_1480_, 0);
                        v_isSharedCheck_1506_ = (!lean_is_exclusive(v___x_1480_)) as u8;
                        if v_isSharedCheck_1506_ == 0 {
                            v___x_1501_ = v___x_1480_;
                            v_isShared_1502_ = v_isSharedCheck_1506_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1499_);
                            lean_dec(v___x_1480_);
                            v___x_1501_ = lean_box(0);
                            v_isShared_1502_ = v_isSharedCheck_1506_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1485_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11,
                );
                v___x_1486_ = lean_string_append(v___x_1485_, v_a_1481_);
                lean_dec(v_a_1481_);
                if v_isShared_1484_ == 0 {
                    lean_ctor_set(v___x_1483_, 0, v___x_1486_);
                    v___x_1488_ = v___x_1483_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1486_);
                    v___x_1488_ = v_reuseFailAlloc_1489_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1488_;
            }
            3 => {
                if v_isShared_1494_ == 0 {
                    lean_ctor_set_tag(v___x_1493_, 0);
                    v___x_1496_ = v___x_1493_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
                    v___x_1496_ = v_reuseFailAlloc_1497_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1496_;
            }
            5 => {
                if v_isShared_1502_ == 0 {
                    v___x_1504_ = v___x_1501_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
                    v___x_1504_ = v_reuseFailAlloc_1505_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1504_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1(
    mut v_j_1509_: *mut LeanObject,
    mut v_k_1510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: u8 = 0;
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: u8 = 0;
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: u8 = 0;
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1513_ = l_Lean_Json_getObjValD(v_j_1509_, v_k_1510_);
                v___x_1514_ = l_Lean_Json_getNat_x3f(v___x_1513_);
                if lean_obj_tag(v___x_1514_) == 1 {
                    v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
                    lean_inc(v_a_1515_);
                    lean_dec_ref_known(v___x_1514_, 1);
                    v___x_1516_ = lean_unsigned_to_nat(0);
                    v___x_1517_ = lean_nat_dec_eq(v_a_1515_, v___x_1516_);
                    if v___x_1517_ == 0 {
                        v___x_1518_ = lean_unsigned_to_nat(1);
                        v___x_1519_ = lean_nat_dec_eq(v_a_1515_, v___x_1518_);
                        if v___x_1519_ == 0 {
                            v___x_1520_ = lean_unsigned_to_nat(2);
                            v___x_1521_ = lean_nat_dec_eq(v_a_1515_, v___x_1520_);
                            lean_dec(v_a_1515_);
                            if v___x_1521_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                v___x_1522_ = l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__2;
                                return v___x_1522_;
                            }
                        } else {
                            lean_dec(v_a_1515_);
                            v___x_1523_ =
                                l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__3;
                            return v___x_1523_;
                        }
                    } else {
                        lean_dec(v_a_1515_);
                        v___x_1524_ =
                            l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__4;
                        return v___x_1524_;
                    }
                } else {
                    lean_dec_ref(v___x_1514_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1512_ = l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__1;
                return v___x_1512_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1___boxed(
    mut v_j_1525_: *mut LeanObject,
    mut v_k_1526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1527_: *mut LeanObject = core::ptr::null_mut();
    v_res_1527_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1(v_j_1525_, v_k_1526_);
    lean_dec_ref(v_k_1526_);
    return v_res_1527_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3(
    mut v_sz_1528_: usize,
    mut v_i_1529_: usize,
    mut v_bs_1530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1531_: u8 = 0;
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1538_: u8 = 0;
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1542_: u8 = 0;
    let mut v_a_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: usize = 0;
    let mut v___x_1547_: usize = 0;
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1531_ = lean_usize_dec_lt(v_i_1529_, v_sz_1528_);
                if v___x_1531_ == 0 {
                    v___x_1532_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1532_, 0, v_bs_1530_);
                    return v___x_1532_;
                } else {
                    v_v_1533_ = lean_array_uget_borrowed(v_bs_1530_, v_i_1529_);
                    lean_inc(v_v_1533_);
                    v___x_1534_ = l_Lean_Lsp_instFromJsonDocumentFilter_fromJson(v_v_1533_);
                    if lean_obj_tag(v___x_1534_) == 0 {
                        lean_dec_ref(v_bs_1530_);
                        v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
                        v_isSharedCheck_1542_ = (!lean_is_exclusive(v___x_1534_)) as u8;
                        if v_isSharedCheck_1542_ == 0 {
                            v___x_1537_ = v___x_1534_;
                            v_isShared_1538_ = v_isSharedCheck_1542_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1535_);
                            lean_dec(v___x_1534_);
                            v___x_1537_ = lean_box(0);
                            v_isShared_1538_ = v_isSharedCheck_1542_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1543_ = lean_ctor_get(v___x_1534_, 0);
                        lean_inc(v_a_1543_);
                        lean_dec_ref_known(v___x_1534_, 1);
                        v___x_1544_ = lean_unsigned_to_nat(0);
                        v_bs_x27_1545_ = lean_array_uset(v_bs_1530_, v_i_1529_, v___x_1544_);
                        v___x_1546_ = 1usize;
                        v___x_1547_ = lean_usize_add(v_i_1529_, v___x_1546_);
                        v___x_1548_ = lean_array_uset(v_bs_x27_1545_, v_i_1529_, v_a_1543_);
                        v_i_1529_ = v___x_1547_;
                        v_bs_1530_ = v___x_1548_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1538_ == 0 {
                    v___x_1540_ = v___x_1537_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
                    v___x_1540_ = v_reuseFailAlloc_1541_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1540_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3___boxed(
    mut v_sz_1550_: *mut LeanObject,
    mut v_i_1551_: *mut LeanObject,
    mut v_bs_1552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1553_: usize = 0;
    let mut v_i_boxed_1554_: usize = 0;
    let mut v_res_1555_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1553_ = lean_unbox_usize(v_sz_1550_);
    lean_dec(v_sz_1550_);
    v_i_boxed_1554_ = lean_unbox_usize(v_i_1551_);
    lean_dec(v_i_1551_);
    v_res_1555_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3(v_sz_boxed_1553_, v_i_boxed_1554_, v_bs_1552_);
    return v_res_1555_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2(
    mut v_x_1558_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1558_) == 4 {
        let mut v_elems_1559_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_1560_: usize = 0;
        let mut v___x_1561_: usize = 0;
        let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
        v_elems_1559_ = lean_ctor_get(v_x_1558_, 0);
        lean_inc_ref(v_elems_1559_);
        lean_dec_ref_known(v_x_1558_, 1);
        v_sz_1560_ = lean_array_size(v_elems_1559_);
        v___x_1561_ = 0usize;
        v___x_1562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3(v_sz_1560_, v___x_1561_, v_elems_1559_);
        return v___x_1562_;
    } else {
        let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
        v___x_1563_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0;
        v___x_1564_ = lean_unsigned_to_nat(80);
        v___x_1565_ = l_Lean_Json_pretty(v_x_1558_, v___x_1564_);
        v___x_1566_ = lean_string_append(v___x_1563_, v___x_1565_);
        lean_dec_ref(v___x_1565_);
        v___x_1567_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1;
        v___x_1568_ = lean_string_append(v___x_1566_, v___x_1567_);
        v___x_1569_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1569_, 0, v___x_1568_);
        return v___x_1569_;
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0(
    mut v_x_1572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1578_: u8 = 0;
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1582_: u8 = 0;
    let mut v_a_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1586_: u8 = 0;
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1591_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1572_) == 0 {
                    v___x_1573_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0___closed__0;
                    return v___x_1573_;
                } else {
                    v___x_1574_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2(v_x_1572_);
                    if lean_obj_tag(v___x_1574_) == 0 {
                        v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
                        v_isSharedCheck_1582_ = (!lean_is_exclusive(v___x_1574_)) as u8;
                        if v_isSharedCheck_1582_ == 0 {
                            v___x_1577_ = v___x_1574_;
                            v_isShared_1578_ = v_isSharedCheck_1582_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1575_);
                            lean_dec(v___x_1574_);
                            v___x_1577_ = lean_box(0);
                            v_isShared_1578_ = v_isSharedCheck_1582_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1583_ = lean_ctor_get(v___x_1574_, 0);
                        v_isSharedCheck_1591_ = (!lean_is_exclusive(v___x_1574_)) as u8;
                        if v_isSharedCheck_1591_ == 0 {
                            v___x_1585_ = v___x_1574_;
                            v_isShared_1586_ = v_isSharedCheck_1591_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1583_);
                            lean_dec(v___x_1574_);
                            v___x_1585_ = lean_box(0);
                            v_isShared_1586_ = v_isSharedCheck_1591_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1578_ == 0 {
                    v___x_1580_ = v___x_1577_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
                    v___x_1580_ = v_reuseFailAlloc_1581_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1580_;
            }
            3 => {
                v___x_1587_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1587_, 0, v_a_1583_);
                if v_isShared_1586_ == 0 {
                    lean_ctor_set(v___x_1585_, 0, v___x_1587_);
                    v___x_1589_ = v___x_1585_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1587_);
                    v___x_1589_ = v_reuseFailAlloc_1590_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1589_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0(
    mut v_j_1592_: *mut LeanObject,
    mut v_k_1593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    v___x_1594_ = l_Lean_Json_getObjValD(v_j_1592_, v_k_1593_);
    v___x_1595_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0(v___x_1594_);
    return v___x_1595_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0___boxed(
    mut v_j_1596_: *mut LeanObject,
    mut v_k_1597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1598_: *mut LeanObject = core::ptr::null_mut();
    v_res_1598_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0(v_j_1596_, v_k_1597_);
    lean_dec_ref(v_k_1597_);
    return v_res_1598_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3()
-> *mut LeanObject {
    let mut v___x_1605_: u8 = 0;
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    v___x_1605_ = 1;
    v___x_1606_ = l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2;
    v___x_1607_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1606_, v___x_1605_);
    return v___x_1607_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4()
-> *mut LeanObject {
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    v___x_1608_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5;
    v___x_1609_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3,
    );
    v___x_1610_ = lean_string_append(v___x_1609_, v___x_1608_);
    return v___x_1610_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7()
-> *mut LeanObject {
    let mut v___x_1614_: u8 = 0;
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    v___x_1614_ = 1;
    v___x_1615_ = l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__6;
    v___x_1616_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1615_, v___x_1614_);
    return v___x_1616_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8()
-> *mut LeanObject {
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    v___x_1617_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7,
    );
    v___x_1618_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4,
    );
    v___x_1619_ = lean_string_append(v___x_1618_, v___x_1617_);
    return v___x_1619_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9()
-> *mut LeanObject {
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    v___x_1620_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_1621_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8,
    );
    v___x_1622_ = lean_string_append(v___x_1621_, v___x_1620_);
    return v___x_1622_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12()
-> *mut LeanObject {
    let mut v___x_1626_: u8 = 0;
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    v___x_1626_ = 1;
    v___x_1627_ =
        l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__11;
    v___x_1628_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1627_, v___x_1626_);
    return v___x_1628_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13()
-> *mut LeanObject {
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    v___x_1629_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12,
    );
    v___x_1630_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4,
    );
    v___x_1631_ = lean_string_append(v___x_1630_, v___x_1629_);
    return v___x_1631_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14()
-> *mut LeanObject {
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    v___x_1632_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_1633_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13,
    );
    v___x_1634_ = lean_string_append(v___x_1633_, v___x_1632_);
    return v___x_1634_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson(
    mut v_json_1635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1641_: u8 = 0;
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1647_: u8 = 0;
    let mut v_a_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1651_: u8 = 0;
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1655_: u8 = 0;
    let mut v_a_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1662_: u8 = 0;
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1668_: u8 = 0;
    let mut v_a_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1672_: u8 = 0;
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1676_: u8 = 0;
    let mut v_a_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1680_: u8 = 0;
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: u8 = 0;
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1686_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1636_ = l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__0;
                lean_inc(v_json_1635_);
                v___x_1637_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0(v_json_1635_, v___x_1636_);
                if lean_obj_tag(v___x_1637_) == 0 {
                    lean_dec(v_json_1635_);
                    v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
                    v_isSharedCheck_1647_ = (!lean_is_exclusive(v___x_1637_)) as u8;
                    if v_isSharedCheck_1647_ == 0 {
                        v___x_1640_ = v___x_1637_;
                        v_isShared_1641_ = v_isSharedCheck_1647_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1638_);
                        lean_dec(v___x_1637_);
                        v___x_1640_ = lean_box(0);
                        v_isShared_1641_ = v_isSharedCheck_1647_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_1637_) == 0 {
                        lean_dec(v_json_1635_);
                        v_a_1648_ = lean_ctor_get(v___x_1637_, 0);
                        v_isSharedCheck_1655_ = (!lean_is_exclusive(v___x_1637_)) as u8;
                        if v_isSharedCheck_1655_ == 0 {
                            v___x_1650_ = v___x_1637_;
                            v_isShared_1651_ = v_isSharedCheck_1655_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1648_);
                            lean_dec(v___x_1637_);
                            v___x_1650_ = lean_box(0);
                            v_isShared_1651_ = v_isSharedCheck_1655_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1656_ = lean_ctor_get(v___x_1637_, 0);
                        lean_inc(v_a_1656_);
                        lean_dec_ref_known(v___x_1637_, 1);
                        v___x_1657_ = l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__10;
                        v___x_1658_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1(v_json_1635_, v___x_1657_);
                        if lean_obj_tag(v___x_1658_) == 0 {
                            lean_dec(v_a_1656_);
                            v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
                            v_isSharedCheck_1668_ = (!lean_is_exclusive(v___x_1658_)) as u8;
                            if v_isSharedCheck_1668_ == 0 {
                                v___x_1661_ = v___x_1658_;
                                v_isShared_1662_ = v_isSharedCheck_1668_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_1659_);
                                lean_dec(v___x_1658_);
                                v___x_1661_ = lean_box(0);
                                v_isShared_1662_ = v_isSharedCheck_1668_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_1658_) == 0 {
                                lean_dec(v_a_1656_);
                                v_a_1669_ = lean_ctor_get(v___x_1658_, 0);
                                v_isSharedCheck_1676_ = (!lean_is_exclusive(v___x_1658_)) as u8;
                                if v_isSharedCheck_1676_ == 0 {
                                    v___x_1671_ = v___x_1658_;
                                    v_isShared_1672_ = v_isSharedCheck_1676_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_1669_);
                                    lean_dec(v___x_1658_);
                                    v___x_1671_ = lean_box(0);
                                    v_isShared_1672_ = v_isSharedCheck_1676_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_1677_ = lean_ctor_get(v___x_1658_, 0);
                                v_isSharedCheck_1686_ = (!lean_is_exclusive(v___x_1658_)) as u8;
                                if v_isSharedCheck_1686_ == 0 {
                                    v___x_1679_ = v___x_1658_;
                                    v_isShared_1680_ = v_isSharedCheck_1686_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_1677_);
                                    lean_dec(v___x_1658_);
                                    v___x_1679_ = lean_box(0);
                                    v_isShared_1680_ = v_isSharedCheck_1686_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1642_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9_once), _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9);
                v___x_1643_ = lean_string_append(v___x_1642_, v_a_1638_);
                lean_dec(v_a_1638_);
                if v_isShared_1641_ == 0 {
                    lean_ctor_set(v___x_1640_, 0, v___x_1643_);
                    v___x_1645_ = v___x_1640_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1643_);
                    v___x_1645_ = v_reuseFailAlloc_1646_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1645_;
            }
            3 => {
                if v_isShared_1651_ == 0 {
                    lean_ctor_set_tag(v___x_1650_, 0);
                    v___x_1653_ = v___x_1650_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
                    v___x_1653_ = v_reuseFailAlloc_1654_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1653_;
            }
            5 => {
                v___x_1663_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14_once), _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14);
                v___x_1664_ = lean_string_append(v___x_1663_, v_a_1659_);
                lean_dec(v_a_1659_);
                if v_isShared_1662_ == 0 {
                    lean_ctor_set(v___x_1661_, 0, v___x_1664_);
                    v___x_1666_ = v___x_1661_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1664_);
                    v___x_1666_ = v_reuseFailAlloc_1667_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1666_;
            }
            7 => {
                if v_isShared_1672_ == 0 {
                    lean_ctor_set_tag(v___x_1671_, 0);
                    v___x_1674_ = v___x_1671_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
                    v___x_1674_ = v_reuseFailAlloc_1675_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1674_;
            }
            9 => {
                v___x_1681_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_1681_, 0, v_a_1656_);
                v___x_1682_ = (lean_unbox(v_a_1677_) as u8);
                lean_dec(v_a_1677_);
                lean_ctor_set_uint8(
                    v___x_1681_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1682_,
                );
                if v_isShared_1680_ == 0 {
                    lean_ctor_set(v___x_1679_, 0, v___x_1681_);
                    v___x_1684_ = v___x_1679_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1681_);
                    v___x_1684_ = v_reuseFailAlloc_1685_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1684_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_TextDocumentContentChangeEvent_ctorIdx(
    mut v_x_1689_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1689_) == 0 {
        let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
        v___x_1690_ = lean_unsigned_to_nat(0);
        return v___x_1690_;
    } else {
        let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
        v___x_1691_ = lean_unsigned_to_nat(1);
        return v___x_1691_;
    }
}
pub unsafe fn l_Lean_Lsp_TextDocumentContentChangeEvent_ctorIdx___boxed(
    mut v_x_1692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1693_: *mut LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorIdx(v_x_1692_);
    lean_dec_ref(v_x_1692_);
    return v_res_1693_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(
    mut v_t_1694_: *mut LeanObject,
    mut v_k_1695_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1694_) == 0 {
        let mut v_range_1696_: *mut LeanObject = core::ptr::null_mut();
        let mut v_text_1697_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
        v_range_1696_ = lean_ctor_get(v_t_1694_, 0);
        lean_inc_ref(v_range_1696_);
        v_text_1697_ = lean_ctor_get(v_t_1694_, 1);
        lean_inc_ref(v_text_1697_);
        lean_dec_ref_known(v_t_1694_, 2);
        v___x_1698_ = lean_apply_2(v_k_1695_, v_range_1696_, v_text_1697_);
        return v___x_1698_;
    } else {
        let mut v_text_1699_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
        v_text_1699_ = lean_ctor_get(v_t_1694_, 0);
        lean_inc_ref(v_text_1699_);
        lean_dec_ref_known(v_t_1694_, 1);
        v___x_1700_ = lean_apply_1(v_k_1695_, v_text_1699_);
        return v___x_1700_;
    }
}
pub unsafe fn l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim(
    mut v_motive_1701_: *mut LeanObject,
    mut v_ctorIdx_1702_: *mut LeanObject,
    mut v_t_1703_: *mut LeanObject,
    mut v_h_1704_: *mut LeanObject,
    mut v_k_1705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    v___x_1706_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_1703_, v_k_1705_);
    return v___x_1706_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___boxed(
    mut v_motive_1707_: *mut LeanObject,
    mut v_ctorIdx_1708_: *mut LeanObject,
    mut v_t_1709_: *mut LeanObject,
    mut v_h_1710_: *mut LeanObject,
    mut v_k_1711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1712_: *mut LeanObject = core::ptr::null_mut();
    v_res_1712_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim(
        v_motive_1707_,
        v_ctorIdx_1708_,
        v_t_1709_,
        v_h_1710_,
        v_k_1711_,
    );
    lean_dec(v_ctorIdx_1708_);
    return v_res_1712_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentContentChangeEvent_rangeChange_elim___redArg(
    mut v_t_1713_: *mut LeanObject,
    mut v_rangeChange_1714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    v___x_1715_ =
        l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_1713_, v_rangeChange_1714_);
    return v___x_1715_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentContentChangeEvent_rangeChange_elim(
    mut v_motive_1716_: *mut LeanObject,
    mut v_t_1717_: *mut LeanObject,
    mut v_h_1718_: *mut LeanObject,
    mut v_rangeChange_1719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    v___x_1720_ =
        l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_1717_, v_rangeChange_1719_);
    return v___x_1720_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentContentChangeEvent_fullChange_elim___redArg(
    mut v_t_1721_: *mut LeanObject,
    mut v_fullChange_1722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    v___x_1723_ =
        l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_1721_, v_fullChange_1722_);
    return v___x_1723_;
}
pub unsafe fn l_Lean_Lsp_TextDocumentContentChangeEvent_fullChange_elim(
    mut v_motive_1724_: *mut LeanObject,
    mut v_t_1725_: *mut LeanObject,
    mut v_h_1726_: *mut LeanObject,
    mut v_fullChange_1727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    v___x_1728_ =
        l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_1725_, v_fullChange_1727_);
    return v___x_1728_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0(
    mut v___x_1731_: *mut LeanObject,
    mut v___x_1732_: *mut LeanObject,
    mut v_j_1733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1740_: u8 = 0;
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1744_: u8 = 0;
    let mut v_a_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1748_: u8 = 0;
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1753_: u8 = 0;
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1762_: u8 = 0;
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1767_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1754_ =
                    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1;
                lean_inc(v_j_1733_);
                v___x_1755_ =
                    l_Lean_Json_getObjValAs_x3f___redArg(v_j_1733_, v___x_1732_, v___x_1754_);
                if lean_obj_tag(v___x_1755_) == 0 {
                    lean_dec_ref_known(v___x_1755_, 1);
                    state = 1;
                    continue;
                } else {
                    v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
                    lean_inc(v_a_1756_);
                    lean_dec_ref_known(v___x_1755_, 1);
                    v___x_1757_ =
                        l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0;
                    lean_inc_ref(v___x_1731_);
                    lean_inc(v_j_1733_);
                    v___x_1758_ =
                        l_Lean_Json_getObjValAs_x3f___redArg(v_j_1733_, v___x_1731_, v___x_1757_);
                    if lean_obj_tag(v___x_1758_) == 0 {
                        lean_dec_ref_known(v___x_1758_, 1);
                        lean_dec(v_a_1756_);
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_j_1733_);
                        lean_dec_ref(v___x_1731_);
                        v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
                        v_isSharedCheck_1767_ = (!lean_is_exclusive(v___x_1758_)) as u8;
                        if v_isSharedCheck_1767_ == 0 {
                            v___x_1761_ = v___x_1758_;
                            v_isShared_1762_ = v_isSharedCheck_1767_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1759_);
                            lean_dec(v___x_1758_);
                            v___x_1761_ = lean_box(0);
                            v_isShared_1762_ = v_isSharedCheck_1767_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1735_ =
                    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0;
                v___x_1736_ =
                    l_Lean_Json_getObjValAs_x3f___redArg(v_j_1733_, v___x_1731_, v___x_1735_);
                if lean_obj_tag(v___x_1736_) == 0 {
                    v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
                    v_isSharedCheck_1744_ = (!lean_is_exclusive(v___x_1736_)) as u8;
                    if v_isSharedCheck_1744_ == 0 {
                        v___x_1739_ = v___x_1736_;
                        v_isShared_1740_ = v_isSharedCheck_1744_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1737_);
                        lean_dec(v___x_1736_);
                        v___x_1739_ = lean_box(0);
                        v_isShared_1740_ = v_isSharedCheck_1744_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1745_ = lean_ctor_get(v___x_1736_, 0);
                    v_isSharedCheck_1753_ = (!lean_is_exclusive(v___x_1736_)) as u8;
                    if v_isSharedCheck_1753_ == 0 {
                        v___x_1747_ = v___x_1736_;
                        v_isShared_1748_ = v_isSharedCheck_1753_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1745_);
                        lean_dec(v___x_1736_);
                        v___x_1747_ = lean_box(0);
                        v_isShared_1748_ = v_isSharedCheck_1753_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1740_ == 0 {
                    v___x_1742_ = v___x_1739_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
                    v___x_1742_ = v_reuseFailAlloc_1743_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1742_;
            }
            4 => {
                v___x_1749_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1749_, 0, v_a_1745_);
                if v_isShared_1748_ == 0 {
                    lean_ctor_set(v___x_1747_, 0, v___x_1749_);
                    v___x_1751_ = v___x_1747_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1749_);
                    v___x_1751_ = v_reuseFailAlloc_1752_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1751_;
            }
            6 => {
                v___x_1763_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1763_, 0, v_a_1756_);
                lean_ctor_set(v___x_1763_, 1, v_a_1759_);
                if v_isShared_1762_ == 0 {
                    lean_ctor_set(v___x_1761_, 0, v___x_1763_);
                    v___x_1765_ = v___x_1761_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
                    v___x_1765_ = v_reuseFailAlloc_1766_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1765_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson___lam__0(
    mut v_o_1774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_range_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1779_: u8 = 0;
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1792_: u8 = 0;
    let mut v_text_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1796_: u8 = 0;
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1805_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_o_1774_) == 0 {
                    v_range_1775_ = lean_ctor_get(v_o_1774_, 0);
                    v_text_1776_ = lean_ctor_get(v_o_1774_, 1);
                    v_isSharedCheck_1792_ = (!lean_is_exclusive(v_o_1774_)) as u8;
                    if v_isSharedCheck_1792_ == 0 {
                        v___x_1778_ = v_o_1774_;
                        v_isShared_1779_ = v_isSharedCheck_1792_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_text_1776_);
                        lean_inc(v_range_1775_);
                        lean_dec(v_o_1774_);
                        v___x_1778_ = lean_box(0);
                        v_isShared_1779_ = v_isSharedCheck_1792_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_text_1793_ = lean_ctor_get(v_o_1774_, 0);
                    v_isSharedCheck_1805_ = (!lean_is_exclusive(v_o_1774_)) as u8;
                    if v_isSharedCheck_1805_ == 0 {
                        v___x_1795_ = v_o_1774_;
                        v_isShared_1796_ = v_isSharedCheck_1805_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_text_1793_);
                        lean_dec(v_o_1774_);
                        v___x_1795_ = lean_box(0);
                        v_isShared_1796_ = v_isSharedCheck_1805_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1780_ =
                    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1;
                v___x_1781_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_1775_);
                if v_isShared_1779_ == 0 {
                    lean_ctor_set(v___x_1778_, 1, v___x_1781_);
                    lean_ctor_set(v___x_1778_, 0, v___x_1780_);
                    v___x_1783_ = v___x_1778_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1780_);
                    lean_ctor_set(v_reuseFailAlloc_1791_, 1, v___x_1781_);
                    v___x_1783_ = v_reuseFailAlloc_1791_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1784_ =
                    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0;
                v___x_1785_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1785_, 0, v_text_1776_);
                v___x_1786_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1786_, 0, v___x_1784_);
                lean_ctor_set(v___x_1786_, 1, v___x_1785_);
                v___x_1787_ = lean_box(0);
                v___x_1788_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1788_, 0, v___x_1786_);
                lean_ctor_set(v___x_1788_, 1, v___x_1787_);
                v___x_1789_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1789_, 0, v___x_1783_);
                lean_ctor_set(v___x_1789_, 1, v___x_1788_);
                v___x_1790_ = l_Lean_Json_mkObj(v___x_1789_);
                lean_dec_ref_known(v___x_1789_, 2);
                return v___x_1790_;
            }
            3 => {
                v___x_1797_ =
                    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0;
                if v_isShared_1796_ == 0 {
                    lean_ctor_set_tag(v___x_1795_, 3);
                    v___x_1799_ = v___x_1795_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1804_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_text_1793_);
                    v___x_1799_ = v_reuseFailAlloc_1804_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1800_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1800_, 0, v___x_1797_);
                lean_ctor_set(v___x_1800_, 1, v___x_1799_);
                v___x_1801_ = lean_box(0);
                v___x_1802_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1802_, 0, v___x_1800_);
                lean_ctor_set(v___x_1802_, 1, v___x_1801_);
                v___x_1803_ = l_Lean_Json_mkObj(v___x_1802_);
                lean_dec_ref_known(v___x_1802_, 2);
                return v___x_1803_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0(
    mut v_sz_1808_: usize,
    mut v_i_1809_: usize,
    mut v_bs_1810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1811_: u8 = 0;
    let mut v_v_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: usize = 0;
    let mut v___x_1818_: usize = 0;
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1825_: u8 = 0;
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1838_: u8 = 0;
    let mut v_text_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1842_: u8 = 0;
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1851_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1811_ = lean_usize_dec_lt(v_i_1809_, v_sz_1808_);
                if v___x_1811_ == 0 {
                    return v_bs_1810_;
                } else {
                    v_v_1812_ = lean_array_uget(v_bs_1810_, v_i_1809_);
                    v___x_1813_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1814_ = lean_array_uset(v_bs_1810_, v_i_1809_, v___x_1813_);
                    if lean_obj_tag(v_v_1812_) == 0 {
                        v_range_1821_ = lean_ctor_get(v_v_1812_, 0);
                        v_text_1822_ = lean_ctor_get(v_v_1812_, 1);
                        v_isSharedCheck_1838_ = (!lean_is_exclusive(v_v_1812_)) as u8;
                        if v_isSharedCheck_1838_ == 0 {
                            v___x_1824_ = v_v_1812_;
                            v_isShared_1825_ = v_isSharedCheck_1838_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_text_1822_);
                            lean_inc(v_range_1821_);
                            lean_dec(v_v_1812_);
                            v___x_1824_ = lean_box(0);
                            v_isShared_1825_ = v_isSharedCheck_1838_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_text_1839_ = lean_ctor_get(v_v_1812_, 0);
                        v_isSharedCheck_1851_ = (!lean_is_exclusive(v_v_1812_)) as u8;
                        if v_isSharedCheck_1851_ == 0 {
                            v___x_1841_ = v_v_1812_;
                            v_isShared_1842_ = v_isSharedCheck_1851_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_text_1839_);
                            lean_dec(v_v_1812_);
                            v___x_1841_ = lean_box(0);
                            v_isShared_1842_ = v_isSharedCheck_1851_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1817_ = 1usize;
                v___x_1818_ = lean_usize_add(v_i_1809_, v___x_1817_);
                v___x_1819_ = lean_array_uset(v_bs_x27_1814_, v_i_1809_, v___y_1816_);
                v_i_1809_ = v___x_1818_;
                v_bs_1810_ = v___x_1819_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1826_ =
                    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1;
                v___x_1827_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_1821_);
                if v_isShared_1825_ == 0 {
                    lean_ctor_set(v___x_1824_, 1, v___x_1827_);
                    lean_ctor_set(v___x_1824_, 0, v___x_1826_);
                    v___x_1829_ = v___x_1824_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1826_);
                    lean_ctor_set(v_reuseFailAlloc_1837_, 1, v___x_1827_);
                    v___x_1829_ = v_reuseFailAlloc_1837_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1830_ =
                    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0;
                v___x_1831_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1831_, 0, v_text_1822_);
                v___x_1832_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1832_, 0, v___x_1830_);
                lean_ctor_set(v___x_1832_, 1, v___x_1831_);
                v___x_1833_ = lean_box(0);
                v___x_1834_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1834_, 0, v___x_1832_);
                lean_ctor_set(v___x_1834_, 1, v___x_1833_);
                v___x_1835_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1835_, 0, v___x_1829_);
                lean_ctor_set(v___x_1835_, 1, v___x_1834_);
                v___x_1836_ = l_Lean_Json_mkObj(v___x_1835_);
                lean_dec_ref_known(v___x_1835_, 2);
                v___y_1816_ = v___x_1836_;
                state = 1;
                continue;
            }
            4 => {
                v___x_1843_ =
                    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0;
                if v_isShared_1842_ == 0 {
                    lean_ctor_set_tag(v___x_1841_, 3);
                    v___x_1845_ = v___x_1841_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1850_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_text_1839_);
                    v___x_1845_ = v_reuseFailAlloc_1850_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1846_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1846_, 0, v___x_1843_);
                lean_ctor_set(v___x_1846_, 1, v___x_1845_);
                v___x_1847_ = lean_box(0);
                v___x_1848_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1848_, 0, v___x_1846_);
                lean_ctor_set(v___x_1848_, 1, v___x_1847_);
                v___x_1849_ = l_Lean_Json_mkObj(v___x_1848_);
                lean_dec_ref_known(v___x_1848_, 2);
                v___y_1816_ = v___x_1849_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0___boxed(
    mut v_sz_1852_: *mut LeanObject,
    mut v_i_1853_: *mut LeanObject,
    mut v_bs_1854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1855_: usize = 0;
    let mut v_i_boxed_1856_: usize = 0;
    let mut v_res_1857_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1855_ = lean_unbox_usize(v_sz_1852_);
    lean_dec(v_sz_1852_);
    v_i_boxed_1856_ = lean_unbox_usize(v_i_1853_);
    lean_dec(v_i_1853_);
    v_res_1857_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0(v_sz_boxed_1855_, v_i_boxed_1856_, v_bs_1854_);
    return v_res_1857_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0(
    mut v_a_1858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_1859_: usize = 0;
    let mut v___x_1860_: usize = 0;
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    v_sz_1859_ = lean_array_size(v_a_1858_);
    v___x_1860_ = 0usize;
    v___x_1861_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0(v_sz_1859_, v___x_1860_, v_a_1858_);
    v___x_1862_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_1862_, 0, v___x_1861_);
    return v___x_1862_;
}
pub unsafe fn l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson(
    mut v_x_1864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_textDocument_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contentChanges_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1869_: u8 = 0;
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_textDocument_1865_ = lean_ctor_get(v_x_1864_, 0);
                v_contentChanges_1866_ = lean_ctor_get(v_x_1864_, 1);
                v_isSharedCheck_1886_ = (!lean_is_exclusive(v_x_1864_)) as u8;
                if v_isSharedCheck_1886_ == 0 {
                    v___x_1868_ = v_x_1864_;
                    v_isShared_1869_ = v_isSharedCheck_1886_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_contentChanges_1866_);
                    lean_inc(v_textDocument_1865_);
                    lean_dec(v_x_1864_);
                    v___x_1868_ = lean_box(0);
                    v_isShared_1869_ = v_isSharedCheck_1886_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1870_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0;
                v___x_1871_ = l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson(
                    v_textDocument_1865_,
                );
                if v_isShared_1869_ == 0 {
                    lean_ctor_set(v___x_1868_, 1, v___x_1871_);
                    lean_ctor_set(v___x_1868_, 0, v___x_1870_);
                    v___x_1873_ = v___x_1868_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1870_);
                    lean_ctor_set(v_reuseFailAlloc_1885_, 1, v___x_1871_);
                    v___x_1873_ = v_reuseFailAlloc_1885_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1874_ = lean_box(0);
                v___x_1875_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1875_, 0, v___x_1873_);
                lean_ctor_set(v___x_1875_, 1, v___x_1874_);
                v___x_1876_ = l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0;
                v___x_1877_ = l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0(v_contentChanges_1866_);
                v___x_1878_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1878_, 0, v___x_1876_);
                lean_ctor_set(v___x_1878_, 1, v___x_1877_);
                v___x_1879_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1879_, 0, v___x_1878_);
                lean_ctor_set(v___x_1879_, 1, v___x_1874_);
                v___x_1880_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1880_, 0, v___x_1879_);
                lean_ctor_set(v___x_1880_, 1, v___x_1874_);
                v___x_1881_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1881_, 0, v___x_1875_);
                lean_ctor_set(v___x_1881_, 1, v___x_1880_);
                v___x_1882_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1;
                v___x_1883_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_1881_, v___x_1882_);
                v___x_1884_ = l_Lean_Json_mkObj(v___x_1883_);
                lean_dec(v___x_1883_);
                return v___x_1884_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0(
    mut v_j_1889_: *mut LeanObject,
    mut v_k_1890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    v___x_1891_ = l_Lean_Json_getObjValD(v_j_1889_, v_k_1890_);
    v___x_1892_ = l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(v___x_1891_);
    return v___x_1892_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0___boxed(
    mut v_j_1893_: *mut LeanObject,
    mut v_k_1894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1895_: *mut LeanObject = core::ptr::null_mut();
    v_res_1895_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0(v_j_1893_, v_k_1894_);
    lean_dec_ref(v_k_1894_);
    return v_res_1895_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3(
    mut v_j_1896_: *mut LeanObject,
    mut v_k_1897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    v___x_1898_ = l_Lean_Json_getObjValD(v_j_1896_, v_k_1897_);
    v___x_1899_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_1898_);
    return v___x_1899_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3___boxed(
    mut v_j_1900_: *mut LeanObject,
    mut v_k_1901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1902_: *mut LeanObject = core::ptr::null_mut();
    v_res_1902_ = l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3(v_j_1900_, v_k_1901_);
    lean_dec_ref(v_k_1901_);
    return v_res_1902_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(
    mut v_j_1903_: *mut LeanObject,
    mut v_k_1904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    v___x_1905_ = l_Lean_Json_getObjValD(v_j_1903_, v_k_1904_);
    v___x_1906_ = l_Lean_Json_getStr_x3f(v___x_1905_);
    return v___x_1906_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2___boxed(
    mut v_j_1907_: *mut LeanObject,
    mut v_k_1908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1909_: *mut LeanObject = core::ptr::null_mut();
    v_res_1909_ = l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(v_j_1907_, v_k_1908_);
    lean_dec_ref(v_k_1908_);
    return v_res_1909_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4(
    mut v_sz_1910_: usize,
    mut v_i_1911_: usize,
    mut v_bs_1912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1913_: u8 = 0;
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: usize = 0;
    let mut v___x_1921_: usize = 0;
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1930_: u8 = 0;
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1934_: u8 = 0;
    let mut v_a_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1913_ = lean_usize_dec_lt(v_i_1911_, v_sz_1910_);
                if v___x_1913_ == 0 {
                    v___x_1914_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1914_, 0, v_bs_1912_);
                    return v___x_1914_;
                } else {
                    v_v_1915_ = lean_array_uget(v_bs_1912_, v_i_1911_);
                    v___x_1916_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1917_ = lean_array_uset(v_bs_1912_, v_i_1911_, v___x_1916_);
                    v___x_1937_ =
                        l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1;
                    lean_inc(v_v_1915_);
                    v___x_1938_ = l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3(v_v_1915_, v___x_1937_);
                    if lean_obj_tag(v___x_1938_) == 0 {
                        lean_dec_ref_known(v___x_1938_, 1);
                        state = 2;
                        continue;
                    } else {
                        v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
                        lean_inc(v_a_1939_);
                        lean_dec_ref_known(v___x_1938_, 1);
                        v___x_1940_ = l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0;
                        lean_inc(v_v_1915_);
                        v___x_1941_ = l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(v_v_1915_, v___x_1940_);
                        if lean_obj_tag(v___x_1941_) == 0 {
                            lean_dec_ref_known(v___x_1941_, 1);
                            lean_dec(v_a_1939_);
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v_v_1915_);
                            v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
                            lean_inc(v_a_1942_);
                            lean_dec_ref_known(v___x_1941_, 1);
                            v___x_1943_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_1943_, 0, v_a_1939_);
                            lean_ctor_set(v___x_1943_, 1, v_a_1942_);
                            v_a_1919_ = v___x_1943_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1920_ = 1usize;
                v___x_1921_ = lean_usize_add(v_i_1911_, v___x_1920_);
                v___x_1922_ = lean_array_uset(v_bs_x27_1917_, v_i_1911_, v_a_1919_);
                v_i_1911_ = v___x_1921_;
                v_bs_1912_ = v___x_1922_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1925_ =
                    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0;
                v___x_1926_ = l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(v_v_1915_, v___x_1925_);
                if lean_obj_tag(v___x_1926_) == 0 {
                    lean_dec_ref(v_bs_x27_1917_);
                    v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
                    v_isSharedCheck_1934_ = (!lean_is_exclusive(v___x_1926_)) as u8;
                    if v_isSharedCheck_1934_ == 0 {
                        v___x_1929_ = v___x_1926_;
                        v_isShared_1930_ = v_isSharedCheck_1934_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1927_);
                        lean_dec(v___x_1926_);
                        v___x_1929_ = lean_box(0);
                        v_isShared_1930_ = v_isSharedCheck_1934_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_1935_ = lean_ctor_get(v___x_1926_, 0);
                    lean_inc(v_a_1935_);
                    lean_dec_ref_known(v___x_1926_, 1);
                    v___x_1936_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1936_, 0, v_a_1935_);
                    v_a_1919_ = v___x_1936_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_1930_ == 0 {
                    v___x_1932_ = v___x_1929_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
                    v___x_1932_ = v_reuseFailAlloc_1933_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1932_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4___boxed(
    mut v_sz_1944_: *mut LeanObject,
    mut v_i_1945_: *mut LeanObject,
    mut v_bs_1946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1947_: usize = 0;
    let mut v_i_boxed_1948_: usize = 0;
    let mut v_res_1949_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1947_ = lean_unbox_usize(v_sz_1944_);
    lean_dec(v_sz_1944_);
    v_i_boxed_1948_ = lean_unbox_usize(v_i_1945_);
    lean_dec(v_i_1945_);
    v_res_1949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4(v_sz_boxed_1947_, v_i_boxed_1948_, v_bs_1946_);
    return v_res_1949_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1(
    mut v_x_1950_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1950_) == 4 {
        let mut v_elems_1951_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_1952_: usize = 0;
        let mut v___x_1953_: usize = 0;
        let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
        v_elems_1951_ = lean_ctor_get(v_x_1950_, 0);
        lean_inc_ref(v_elems_1951_);
        lean_dec_ref_known(v_x_1950_, 1);
        v_sz_1952_ = lean_array_size(v_elems_1951_);
        v___x_1953_ = 0usize;
        v___x_1954_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4(v_sz_1952_, v___x_1953_, v_elems_1951_);
        return v___x_1954_;
    } else {
        let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
        v___x_1955_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0;
        v___x_1956_ = lean_unsigned_to_nat(80);
        v___x_1957_ = l_Lean_Json_pretty(v_x_1950_, v___x_1956_);
        v___x_1958_ = lean_string_append(v___x_1955_, v___x_1957_);
        lean_dec_ref(v___x_1957_);
        v___x_1959_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1;
        v___x_1960_ = lean_string_append(v___x_1958_, v___x_1959_);
        v___x_1961_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1961_, 0, v___x_1960_);
        return v___x_1961_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1(
    mut v_j_1962_: *mut LeanObject,
    mut v_k_1963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    v___x_1964_ = l_Lean_Json_getObjValD(v_j_1962_, v_k_1963_);
    v___x_1965_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1(v___x_1964_);
    return v___x_1965_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1___boxed(
    mut v_j_1966_: *mut LeanObject,
    mut v_k_1967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1968_: *mut LeanObject = core::ptr::null_mut();
    v_res_1968_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1(v_j_1966_, v_k_1967_);
    lean_dec_ref(v_k_1967_);
    return v_res_1968_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2()
-> *mut LeanObject {
    let mut v___x_1974_: u8 = 0;
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    v___x_1974_ = 1;
    v___x_1975_ = l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1;
    v___x_1976_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1975_, v___x_1974_);
    return v___x_1976_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3()
-> *mut LeanObject {
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    v___x_1977_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5;
    v___x_1978_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2,
    );
    v___x_1979_ = lean_string_append(v___x_1978_, v___x_1977_);
    return v___x_1979_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4()
-> *mut LeanObject {
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    v___x_1980_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8,
    );
    v___x_1981_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3,
    );
    v___x_1982_ = lean_string_append(v___x_1981_, v___x_1980_);
    return v___x_1982_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5()
-> *mut LeanObject {
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    v___x_1983_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_1984_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4,
    );
    v___x_1985_ = lean_string_append(v___x_1984_, v___x_1983_);
    return v___x_1985_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7()
-> *mut LeanObject {
    let mut v___x_1988_: u8 = 0;
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    v___x_1988_ = 1;
    v___x_1989_ = l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__6;
    v___x_1990_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1989_, v___x_1988_);
    return v___x_1990_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8()
-> *mut LeanObject {
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    v___x_1991_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7,
    );
    v___x_1992_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3,
    );
    v___x_1993_ = lean_string_append(v___x_1992_, v___x_1991_);
    return v___x_1993_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9()
-> *mut LeanObject {
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    v___x_1994_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_1995_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8,
    );
    v___x_1996_ = lean_string_append(v___x_1995_, v___x_1994_);
    return v___x_1996_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson(
    mut v_json_1997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2003_: u8 = 0;
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2009_: u8 = 0;
    let mut v_a_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2013_: u8 = 0;
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2017_: u8 = 0;
    let mut v_a_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2024_: u8 = 0;
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2030_: u8 = 0;
    let mut v_a_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2034_: u8 = 0;
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2038_: u8 = 0;
    let mut v_a_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2042_: u8 = 0;
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2047_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1998_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0;
                lean_inc(v_json_1997_);
                v___x_1999_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0(v_json_1997_, v___x_1998_);
                if lean_obj_tag(v___x_1999_) == 0 {
                    lean_dec(v_json_1997_);
                    v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
                    v_isSharedCheck_2009_ = (!lean_is_exclusive(v___x_1999_)) as u8;
                    if v_isSharedCheck_2009_ == 0 {
                        v___x_2002_ = v___x_1999_;
                        v_isShared_2003_ = v_isSharedCheck_2009_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2000_);
                        lean_dec(v___x_1999_);
                        v___x_2002_ = lean_box(0);
                        v_isShared_2003_ = v_isSharedCheck_2009_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_1999_) == 0 {
                        lean_dec(v_json_1997_);
                        v_a_2010_ = lean_ctor_get(v___x_1999_, 0);
                        v_isSharedCheck_2017_ = (!lean_is_exclusive(v___x_1999_)) as u8;
                        if v_isSharedCheck_2017_ == 0 {
                            v___x_2012_ = v___x_1999_;
                            v_isShared_2013_ = v_isSharedCheck_2017_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2010_);
                            lean_dec(v___x_1999_);
                            v___x_2012_ = lean_box(0);
                            v_isShared_2013_ = v_isSharedCheck_2017_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2018_ = lean_ctor_get(v___x_1999_, 0);
                        lean_inc(v_a_2018_);
                        lean_dec_ref_known(v___x_1999_, 1);
                        v___x_2019_ =
                            l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0;
                        v___x_2020_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1(v_json_1997_, v___x_2019_);
                        if lean_obj_tag(v___x_2020_) == 0 {
                            lean_dec(v_a_2018_);
                            v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
                            v_isSharedCheck_2030_ = (!lean_is_exclusive(v___x_2020_)) as u8;
                            if v_isSharedCheck_2030_ == 0 {
                                v___x_2023_ = v___x_2020_;
                                v_isShared_2024_ = v_isSharedCheck_2030_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_2021_);
                                lean_dec(v___x_2020_);
                                v___x_2023_ = lean_box(0);
                                v_isShared_2024_ = v_isSharedCheck_2030_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_2020_) == 0 {
                                lean_dec(v_a_2018_);
                                v_a_2031_ = lean_ctor_get(v___x_2020_, 0);
                                v_isSharedCheck_2038_ = (!lean_is_exclusive(v___x_2020_)) as u8;
                                if v_isSharedCheck_2038_ == 0 {
                                    v___x_2033_ = v___x_2020_;
                                    v_isShared_2034_ = v_isSharedCheck_2038_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_2031_);
                                    lean_dec(v___x_2020_);
                                    v___x_2033_ = lean_box(0);
                                    v_isShared_2034_ = v_isSharedCheck_2038_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_2039_ = lean_ctor_get(v___x_2020_, 0);
                                v_isSharedCheck_2047_ = (!lean_is_exclusive(v___x_2020_)) as u8;
                                if v_isSharedCheck_2047_ == 0 {
                                    v___x_2041_ = v___x_2020_;
                                    v_isShared_2042_ = v_isSharedCheck_2047_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_2039_);
                                    lean_dec(v___x_2020_);
                                    v___x_2041_ = lean_box(0);
                                    v_isShared_2042_ = v_isSharedCheck_2047_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2004_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5_once), _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5);
                v___x_2005_ = lean_string_append(v___x_2004_, v_a_2000_);
                lean_dec(v_a_2000_);
                if v_isShared_2003_ == 0 {
                    lean_ctor_set(v___x_2002_, 0, v___x_2005_);
                    v___x_2007_ = v___x_2002_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
                    v___x_2007_ = v_reuseFailAlloc_2008_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2007_;
            }
            3 => {
                if v_isShared_2013_ == 0 {
                    lean_ctor_set_tag(v___x_2012_, 0);
                    v___x_2015_ = v___x_2012_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
                    v___x_2015_ = v_reuseFailAlloc_2016_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2015_;
            }
            5 => {
                v___x_2025_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9_once), _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9);
                v___x_2026_ = lean_string_append(v___x_2025_, v_a_2021_);
                lean_dec(v_a_2021_);
                if v_isShared_2024_ == 0 {
                    lean_ctor_set(v___x_2023_, 0, v___x_2026_);
                    v___x_2028_ = v___x_2023_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
                    v___x_2028_ = v_reuseFailAlloc_2029_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2028_;
            }
            7 => {
                if v_isShared_2034_ == 0 {
                    lean_ctor_set_tag(v___x_2033_, 0);
                    v___x_2036_ = v___x_2033_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
                    v___x_2036_ = v_reuseFailAlloc_2037_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2036_;
            }
            9 => {
                v___x_2043_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2043_, 0, v_a_2018_);
                lean_ctor_set(v___x_2043_, 1, v_a_2039_);
                if v_isShared_2042_ == 0 {
                    lean_ctor_set(v___x_2041_, 0, v___x_2043_);
                    v___x_2045_ = v___x_2041_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2043_);
                    v___x_2045_ = v_reuseFailAlloc_2046_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2045_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDidSaveTextDocumentParams_toJson_spec__0(
    mut v_k_2050_: *mut LeanObject,
    mut v_x_2051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2056_: u8 = 0;
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2063_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2051_) == 0 {
                    lean_dec_ref(v_k_2050_);
                    v___x_2052_ = lean_box(0);
                    return v___x_2052_;
                } else {
                    v_val_2053_ = lean_ctor_get(v_x_2051_, 0);
                    v_isSharedCheck_2063_ = (!lean_is_exclusive(v_x_2051_)) as u8;
                    if v_isSharedCheck_2063_ == 0 {
                        v___x_2055_ = v_x_2051_;
                        v_isShared_2056_ = v_isSharedCheck_2063_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2053_);
                        lean_dec(v_x_2051_);
                        v___x_2055_ = lean_box(0);
                        v_isShared_2056_ = v_isSharedCheck_2063_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2056_ == 0 {
                    lean_ctor_set_tag(v___x_2055_, 3);
                    v___x_2058_ = v___x_2055_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2062_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_val_2053_);
                    v___x_2058_ = v_reuseFailAlloc_2062_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2059_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2059_, 0, v_k_2050_);
                lean_ctor_set(v___x_2059_, 1, v___x_2058_);
                v___x_2060_ = lean_box(0);
                v___x_2061_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2061_, 0, v___x_2059_);
                lean_ctor_set(v___x_2061_, 1, v___x_2060_);
                return v___x_2061_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonDidSaveTextDocumentParams_toJson(
    mut v_x_2064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_textDocument_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_x3f_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2069_: u8 = 0;
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2084_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_textDocument_2065_ = lean_ctor_get(v_x_2064_, 0);
                v_text_x3f_2066_ = lean_ctor_get(v_x_2064_, 1);
                v_isSharedCheck_2084_ = (!lean_is_exclusive(v_x_2064_)) as u8;
                if v_isSharedCheck_2084_ == 0 {
                    v___x_2068_ = v_x_2064_;
                    v_isShared_2069_ = v_isSharedCheck_2084_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_text_x3f_2066_);
                    lean_inc(v_textDocument_2065_);
                    lean_dec(v_x_2064_);
                    v___x_2068_ = lean_box(0);
                    v_isShared_2069_ = v_isSharedCheck_2084_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2070_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0;
                v___x_2071_ =
                    l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_2065_);
                if v_isShared_2069_ == 0 {
                    lean_ctor_set(v___x_2068_, 1, v___x_2071_);
                    lean_ctor_set(v___x_2068_, 0, v___x_2070_);
                    v___x_2073_ = v___x_2068_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2070_);
                    lean_ctor_set(v_reuseFailAlloc_2083_, 1, v___x_2071_);
                    v___x_2073_ = v_reuseFailAlloc_2083_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2074_ = lean_box(0);
                v___x_2075_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2075_, 0, v___x_2073_);
                lean_ctor_set(v___x_2075_, 1, v___x_2074_);
                v___x_2076_ =
                    l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0;
                v___x_2077_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDidSaveTextDocumentParams_toJson_spec__0(v___x_2076_, v_text_x3f_2066_);
                v___x_2078_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2078_, 0, v___x_2077_);
                lean_ctor_set(v___x_2078_, 1, v___x_2074_);
                v___x_2079_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2079_, 0, v___x_2075_);
                lean_ctor_set(v___x_2079_, 1, v___x_2078_);
                v___x_2080_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1;
                v___x_2081_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_2079_, v___x_2080_);
                v___x_2082_ = l_Lean_Json_mkObj(v___x_2081_);
                lean_dec(v___x_2081_);
                return v___x_2082_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(
    mut v_j_2087_: *mut LeanObject,
    mut v_k_2088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    v___x_2089_ = l_Lean_Json_getObjValD(v_j_2087_, v_k_2088_);
    v___x_2090_ = l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson(v___x_2089_);
    return v___x_2090_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0___boxed(
    mut v_j_2091_: *mut LeanObject,
    mut v_k_2092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2093_: *mut LeanObject = core::ptr::null_mut();
    v_res_2093_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(v_j_2091_, v_k_2092_);
    lean_dec_ref(v_k_2092_);
    return v_res_2093_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1(
    mut v_x_2096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2102_: u8 = 0;
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2106_: u8 = 0;
    let mut v_a_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2110_: u8 = 0;
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2115_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2096_) == 0 {
                    v___x_2097_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1___closed__0;
                    return v___x_2097_;
                } else {
                    v___x_2098_ = l_Lean_Json_getStr_x3f(v_x_2096_);
                    if lean_obj_tag(v___x_2098_) == 0 {
                        v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
                        v_isSharedCheck_2106_ = (!lean_is_exclusive(v___x_2098_)) as u8;
                        if v_isSharedCheck_2106_ == 0 {
                            v___x_2101_ = v___x_2098_;
                            v_isShared_2102_ = v_isSharedCheck_2106_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2099_);
                            lean_dec(v___x_2098_);
                            v___x_2101_ = lean_box(0);
                            v_isShared_2102_ = v_isSharedCheck_2106_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2107_ = lean_ctor_get(v___x_2098_, 0);
                        v_isSharedCheck_2115_ = (!lean_is_exclusive(v___x_2098_)) as u8;
                        if v_isSharedCheck_2115_ == 0 {
                            v___x_2109_ = v___x_2098_;
                            v_isShared_2110_ = v_isSharedCheck_2115_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2107_);
                            lean_dec(v___x_2098_);
                            v___x_2109_ = lean_box(0);
                            v_isShared_2110_ = v_isSharedCheck_2115_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2102_ == 0 {
                    v___x_2104_ = v___x_2101_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
                    v___x_2104_ = v_reuseFailAlloc_2105_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2104_;
            }
            3 => {
                v___x_2111_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2111_, 0, v_a_2107_);
                if v_isShared_2110_ == 0 {
                    lean_ctor_set(v___x_2109_, 0, v___x_2111_);
                    v___x_2113_ = v___x_2109_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2111_);
                    v___x_2113_ = v_reuseFailAlloc_2114_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2113_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1(
    mut v_j_2116_: *mut LeanObject,
    mut v_k_2117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    v___x_2118_ = l_Lean_Json_getObjValD(v_j_2116_, v_k_2117_);
    v___x_2119_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1(v___x_2118_);
    return v___x_2119_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1___boxed(
    mut v_j_2120_: *mut LeanObject,
    mut v_k_2121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2122_: *mut LeanObject = core::ptr::null_mut();
    v_res_2122_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1(v_j_2120_, v_k_2121_);
    lean_dec_ref(v_k_2121_);
    return v_res_2122_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2()
-> *mut LeanObject {
    let mut v___x_2128_: u8 = 0;
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    v___x_2128_ = 1;
    v___x_2129_ = l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1;
    v___x_2130_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2129_, v___x_2128_);
    return v___x_2130_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3()
-> *mut LeanObject {
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    v___x_2131_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5;
    v___x_2132_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2,
    );
    v___x_2133_ = lean_string_append(v___x_2132_, v___x_2131_);
    return v___x_2133_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4()
-> *mut LeanObject {
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    v___x_2134_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8,
    );
    v___x_2135_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3,
    );
    v___x_2136_ = lean_string_append(v___x_2135_, v___x_2134_);
    return v___x_2136_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5()
-> *mut LeanObject {
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    v___x_2137_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_2138_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4,
    );
    v___x_2139_ = lean_string_append(v___x_2138_, v___x_2137_);
    return v___x_2139_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8()
-> *mut LeanObject {
    let mut v___x_2143_: u8 = 0;
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    v___x_2143_ = 1;
    v___x_2144_ = l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__7;
    v___x_2145_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2144_, v___x_2143_);
    return v___x_2145_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9()
-> *mut LeanObject {
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    v___x_2146_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8,
    );
    v___x_2147_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3,
    );
    v___x_2148_ = lean_string_append(v___x_2147_, v___x_2146_);
    return v___x_2148_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10()
-> *mut LeanObject {
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    v___x_2149_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_2150_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9,
    );
    v___x_2151_ = lean_string_append(v___x_2150_, v___x_2149_);
    return v___x_2151_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson(
    mut v_json_2152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2158_: u8 = 0;
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2164_: u8 = 0;
    let mut v_a_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2168_: u8 = 0;
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2172_: u8 = 0;
    let mut v_a_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2179_: u8 = 0;
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2185_: u8 = 0;
    let mut v_a_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2189_: u8 = 0;
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2193_: u8 = 0;
    let mut v_a_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2197_: u8 = 0;
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2202_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2153_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0;
                lean_inc(v_json_2152_);
                v___x_2154_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(v_json_2152_, v___x_2153_);
                if lean_obj_tag(v___x_2154_) == 0 {
                    lean_dec(v_json_2152_);
                    v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
                    v_isSharedCheck_2164_ = (!lean_is_exclusive(v___x_2154_)) as u8;
                    if v_isSharedCheck_2164_ == 0 {
                        v___x_2157_ = v___x_2154_;
                        v_isShared_2158_ = v_isSharedCheck_2164_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2155_);
                        lean_dec(v___x_2154_);
                        v___x_2157_ = lean_box(0);
                        v_isShared_2158_ = v_isSharedCheck_2164_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_2154_) == 0 {
                        lean_dec(v_json_2152_);
                        v_a_2165_ = lean_ctor_get(v___x_2154_, 0);
                        v_isSharedCheck_2172_ = (!lean_is_exclusive(v___x_2154_)) as u8;
                        if v_isSharedCheck_2172_ == 0 {
                            v___x_2167_ = v___x_2154_;
                            v_isShared_2168_ = v_isSharedCheck_2172_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2165_);
                            lean_dec(v___x_2154_);
                            v___x_2167_ = lean_box(0);
                            v_isShared_2168_ = v_isSharedCheck_2172_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2173_ = lean_ctor_get(v___x_2154_, 0);
                        lean_inc(v_a_2173_);
                        lean_dec_ref_known(v___x_2154_, 1);
                        v___x_2174_ = l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0;
                        v___x_2175_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1(v_json_2152_, v___x_2174_);
                        if lean_obj_tag(v___x_2175_) == 0 {
                            lean_dec(v_a_2173_);
                            v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
                            v_isSharedCheck_2185_ = (!lean_is_exclusive(v___x_2175_)) as u8;
                            if v_isSharedCheck_2185_ == 0 {
                                v___x_2178_ = v___x_2175_;
                                v_isShared_2179_ = v_isSharedCheck_2185_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_2176_);
                                lean_dec(v___x_2175_);
                                v___x_2178_ = lean_box(0);
                                v_isShared_2179_ = v_isSharedCheck_2185_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_2175_) == 0 {
                                lean_dec(v_a_2173_);
                                v_a_2186_ = lean_ctor_get(v___x_2175_, 0);
                                v_isSharedCheck_2193_ = (!lean_is_exclusive(v___x_2175_)) as u8;
                                if v_isSharedCheck_2193_ == 0 {
                                    v___x_2188_ = v___x_2175_;
                                    v_isShared_2189_ = v_isSharedCheck_2193_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_2186_);
                                    lean_dec(v___x_2175_);
                                    v___x_2188_ = lean_box(0);
                                    v_isShared_2189_ = v_isSharedCheck_2193_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_2194_ = lean_ctor_get(v___x_2175_, 0);
                                v_isSharedCheck_2202_ = (!lean_is_exclusive(v___x_2175_)) as u8;
                                if v_isSharedCheck_2202_ == 0 {
                                    v___x_2196_ = v___x_2175_;
                                    v_isShared_2197_ = v_isSharedCheck_2202_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_2194_);
                                    lean_dec(v___x_2175_);
                                    v___x_2196_ = lean_box(0);
                                    v_isShared_2197_ = v_isSharedCheck_2202_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2159_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5,
                );
                v___x_2160_ = lean_string_append(v___x_2159_, v_a_2155_);
                lean_dec(v_a_2155_);
                if v_isShared_2158_ == 0 {
                    lean_ctor_set(v___x_2157_, 0, v___x_2160_);
                    v___x_2162_ = v___x_2157_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
                    v___x_2162_ = v_reuseFailAlloc_2163_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2162_;
            }
            3 => {
                if v_isShared_2168_ == 0 {
                    lean_ctor_set_tag(v___x_2167_, 0);
                    v___x_2170_ = v___x_2167_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
                    v___x_2170_ = v_reuseFailAlloc_2171_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2170_;
            }
            5 => {
                v___x_2180_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10,
                );
                v___x_2181_ = lean_string_append(v___x_2180_, v_a_2176_);
                lean_dec(v_a_2176_);
                if v_isShared_2179_ == 0 {
                    lean_ctor_set(v___x_2178_, 0, v___x_2181_);
                    v___x_2183_ = v___x_2178_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
                    v___x_2183_ = v_reuseFailAlloc_2184_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2183_;
            }
            7 => {
                if v_isShared_2189_ == 0 {
                    lean_ctor_set_tag(v___x_2188_, 0);
                    v___x_2191_ = v___x_2188_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
                    v___x_2191_ = v_reuseFailAlloc_2192_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2191_;
            }
            9 => {
                v___x_2198_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2198_, 0, v_a_2173_);
                lean_ctor_set(v___x_2198_, 1, v_a_2194_);
                if v_isShared_2197_ == 0 {
                    lean_ctor_set(v___x_2196_, 0, v___x_2198_);
                    v___x_2200_ = v___x_2196_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2198_);
                    v___x_2200_ = v_reuseFailAlloc_2201_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2200_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonSaveOptions_toJson(mut v_x_2206_: u8) -> *mut LeanObject {
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    v___x_2207_ = l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0;
    v___x_2208_ = lean_alloc_ctor(1, 0, (1) as u32);
    lean_ctor_set_uint8(v___x_2208_, 0 as u32, v_x_2206_);
    v___x_2209_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2209_, 0, v___x_2207_);
    lean_ctor_set(v___x_2209_, 1, v___x_2208_);
    v___x_2210_ = lean_box(0);
    v___x_2211_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2211_, 0, v___x_2209_);
    lean_ctor_set(v___x_2211_, 1, v___x_2210_);
    v___x_2212_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2212_, 0, v___x_2211_);
    lean_ctor_set(v___x_2212_, 1, v___x_2210_);
    v___x_2213_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1;
    v___x_2214_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_2212_, v___x_2213_);
    v___x_2215_ = l_Lean_Json_mkObj(v___x_2214_);
    lean_dec(v___x_2214_);
    return v___x_2215_;
}
pub unsafe fn l_Lean_Lsp_instToJsonSaveOptions_toJson___boxed(
    mut v_x_2216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_29__boxed_2217_: u8 = 0;
    let mut v_res_2218_: *mut LeanObject = core::ptr::null_mut();
    v_x_29__boxed_2217_ = (lean_unbox(v_x_2216_) as u8);
    v_res_2218_ = l_Lean_Lsp_instToJsonSaveOptions_toJson(v_x_29__boxed_2217_);
    return v_res_2218_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(
    mut v_j_2221_: *mut LeanObject,
    mut v_k_2222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    v___x_2223_ = l_Lean_Json_getObjValD(v_j_2221_, v_k_2222_);
    v___x_2224_ = l_Lean_Json_getBool_x3f(v___x_2223_);
    lean_dec(v___x_2223_);
    return v___x_2224_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0___boxed(
    mut v_j_2225_: *mut LeanObject,
    mut v_k_2226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2227_: *mut LeanObject = core::ptr::null_mut();
    v_res_2227_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(
            v_j_2225_, v_k_2226_,
        );
    lean_dec_ref(v_k_2226_);
    return v_res_2227_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2() -> *mut LeanObject {
    let mut v___x_2233_: u8 = 0;
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    v___x_2233_ = 1;
    v___x_2234_ = l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1;
    v___x_2235_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2234_, v___x_2233_);
    return v___x_2235_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3() -> *mut LeanObject {
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    v___x_2236_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5;
    v___x_2237_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2_once),
        _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2,
    );
    v___x_2238_ = lean_string_append(v___x_2237_, v___x_2236_);
    return v___x_2238_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5() -> *mut LeanObject {
    let mut v___x_2241_: u8 = 0;
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    v___x_2241_ = 1;
    v___x_2242_ = l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__4;
    v___x_2243_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2242_, v___x_2241_);
    return v___x_2243_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6() -> *mut LeanObject {
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    v___x_2244_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5_once),
        _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5,
    );
    v___x_2245_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3,
    );
    v___x_2246_ = lean_string_append(v___x_2245_, v___x_2244_);
    return v___x_2246_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7() -> *mut LeanObject {
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    v___x_2247_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_2248_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6,
    );
    v___x_2249_ = lean_string_append(v___x_2248_, v___x_2247_);
    return v___x_2249_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonSaveOptions_fromJson(
    mut v_json_2250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2256_: u8 = 0;
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2262_: u8 = 0;
    let mut v_a_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2266_: u8 = 0;
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2270_: u8 = 0;
    let mut v_a_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2274_: u8 = 0;
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2278_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2251_ = l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0;
                v___x_2252_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_2250_, v___x_2251_);
                if lean_obj_tag(v___x_2252_) == 0 {
                    v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
                    v_isSharedCheck_2262_ = (!lean_is_exclusive(v___x_2252_)) as u8;
                    if v_isSharedCheck_2262_ == 0 {
                        v___x_2255_ = v___x_2252_;
                        v_isShared_2256_ = v_isSharedCheck_2262_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2253_);
                        lean_dec(v___x_2252_);
                        v___x_2255_ = lean_box(0);
                        v_isShared_2256_ = v_isSharedCheck_2262_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_2252_) == 0 {
                        v_a_2263_ = lean_ctor_get(v___x_2252_, 0);
                        v_isSharedCheck_2270_ = (!lean_is_exclusive(v___x_2252_)) as u8;
                        if v_isSharedCheck_2270_ == 0 {
                            v___x_2265_ = v___x_2252_;
                            v_isShared_2266_ = v_isSharedCheck_2270_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2263_);
                            lean_dec(v___x_2252_);
                            v___x_2265_ = lean_box(0);
                            v_isShared_2266_ = v_isSharedCheck_2270_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2271_ = lean_ctor_get(v___x_2252_, 0);
                        v_isSharedCheck_2278_ = (!lean_is_exclusive(v___x_2252_)) as u8;
                        if v_isSharedCheck_2278_ == 0 {
                            v___x_2273_ = v___x_2252_;
                            v_isShared_2274_ = v_isSharedCheck_2278_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_2271_);
                            lean_dec(v___x_2252_);
                            v___x_2273_ = lean_box(0);
                            v_isShared_2274_ = v_isSharedCheck_2278_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2257_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7,
                );
                v___x_2258_ = lean_string_append(v___x_2257_, v_a_2253_);
                lean_dec(v_a_2253_);
                if v_isShared_2256_ == 0 {
                    lean_ctor_set(v___x_2255_, 0, v___x_2258_);
                    v___x_2260_ = v___x_2255_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2261_, 0, v___x_2258_);
                    v___x_2260_ = v_reuseFailAlloc_2261_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2260_;
            }
            3 => {
                if v_isShared_2266_ == 0 {
                    lean_ctor_set_tag(v___x_2265_, 0);
                    v___x_2268_ = v___x_2265_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
                    v___x_2268_ = v_reuseFailAlloc_2269_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2268_;
            }
            5 => {
                if v_isShared_2274_ == 0 {
                    v___x_2276_ = v___x_2273_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
                    v___x_2276_ = v_reuseFailAlloc_2277_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2276_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonDidCloseTextDocumentParams_toJson(
    mut v_x_2281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    v___x_2282_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0;
    v___x_2283_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_x_2281_);
    v___x_2284_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2284_, 0, v___x_2282_);
    lean_ctor_set(v___x_2284_, 1, v___x_2283_);
    v___x_2285_ = lean_box(0);
    v___x_2286_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2286_, 0, v___x_2284_);
    lean_ctor_set(v___x_2286_, 1, v___x_2285_);
    v___x_2287_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2287_, 0, v___x_2286_);
    lean_ctor_set(v___x_2287_, 1, v___x_2285_);
    v___x_2288_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1;
    v___x_2289_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_2287_, v___x_2288_);
    v___x_2290_ = l_Lean_Json_mkObj(v___x_2289_);
    lean_dec(v___x_2289_);
    return v___x_2290_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2()
-> *mut LeanObject {
    let mut v___x_2298_: u8 = 0;
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    v___x_2298_ = 1;
    v___x_2299_ = l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1;
    v___x_2300_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2299_, v___x_2298_);
    return v___x_2300_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3()
-> *mut LeanObject {
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    v___x_2301_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5;
    v___x_2302_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2,
    );
    v___x_2303_ = lean_string_append(v___x_2302_, v___x_2301_);
    return v___x_2303_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4()
-> *mut LeanObject {
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    v___x_2304_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8,
    );
    v___x_2305_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3,
    );
    v___x_2306_ = lean_string_append(v___x_2305_, v___x_2304_);
    return v___x_2306_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5()
-> *mut LeanObject {
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    v___x_2307_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_2308_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4,
    );
    v___x_2309_ = lean_string_append(v___x_2308_, v___x_2307_);
    return v___x_2309_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson(
    mut v_json_2310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2316_: u8 = 0;
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2322_: u8 = 0;
    let mut v_a_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2326_: u8 = 0;
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2330_: u8 = 0;
    let mut v_a_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2334_: u8 = 0;
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2338_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2311_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0;
                v___x_2312_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(v_json_2310_, v___x_2311_);
                if lean_obj_tag(v___x_2312_) == 0 {
                    v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
                    v_isSharedCheck_2322_ = (!lean_is_exclusive(v___x_2312_)) as u8;
                    if v_isSharedCheck_2322_ == 0 {
                        v___x_2315_ = v___x_2312_;
                        v_isShared_2316_ = v_isSharedCheck_2322_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2313_);
                        lean_dec(v___x_2312_);
                        v___x_2315_ = lean_box(0);
                        v_isShared_2316_ = v_isSharedCheck_2322_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_2312_) == 0 {
                        v_a_2323_ = lean_ctor_get(v___x_2312_, 0);
                        v_isSharedCheck_2330_ = (!lean_is_exclusive(v___x_2312_)) as u8;
                        if v_isSharedCheck_2330_ == 0 {
                            v___x_2325_ = v___x_2312_;
                            v_isShared_2326_ = v_isSharedCheck_2330_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2323_);
                            lean_dec(v___x_2312_);
                            v___x_2325_ = lean_box(0);
                            v_isShared_2326_ = v_isSharedCheck_2330_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2331_ = lean_ctor_get(v___x_2312_, 0);
                        v_isSharedCheck_2338_ = (!lean_is_exclusive(v___x_2312_)) as u8;
                        if v_isSharedCheck_2338_ == 0 {
                            v___x_2333_ = v___x_2312_;
                            v_isShared_2334_ = v_isSharedCheck_2338_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_2331_);
                            lean_dec(v___x_2312_);
                            v___x_2333_ = lean_box(0);
                            v_isShared_2334_ = v_isSharedCheck_2338_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2317_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5,
                );
                v___x_2318_ = lean_string_append(v___x_2317_, v_a_2313_);
                lean_dec(v_a_2313_);
                if v_isShared_2316_ == 0 {
                    lean_ctor_set(v___x_2315_, 0, v___x_2318_);
                    v___x_2320_ = v___x_2315_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2318_);
                    v___x_2320_ = v_reuseFailAlloc_2321_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2320_;
            }
            3 => {
                if v_isShared_2326_ == 0 {
                    lean_ctor_set_tag(v___x_2325_, 0);
                    v___x_2328_ = v___x_2325_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
                    v___x_2328_ = v_reuseFailAlloc_2329_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2328_;
            }
            5 => {
                if v_isShared_2334_ == 0 {
                    v___x_2336_ = v___x_2333_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
                    v___x_2336_ = v_reuseFailAlloc_2337_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2336_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0(
    mut v_k_2341_: *mut LeanObject,
    mut v_x_2342_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2342_) == 0 {
        let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_k_2341_);
        v___x_2343_ = lean_box(0);
        return v___x_2343_;
    } else {
        let mut v_val_2344_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2345_: u8 = 0;
        let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
        v_val_2344_ = lean_ctor_get(v_x_2342_, 0);
        v___x_2345_ = (lean_unbox(v_val_2344_) as u8);
        v___x_2346_ = l_Lean_Lsp_instToJsonSaveOptions_toJson(v___x_2345_);
        v___x_2347_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2347_, 0, v_k_2341_);
        lean_ctor_set(v___x_2347_, 1, v___x_2346_);
        v___x_2348_ = lean_box(0);
        v___x_2349_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2349_, 0, v___x_2347_);
        lean_ctor_set(v___x_2349_, 1, v___x_2348_);
        return v___x_2349_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0___boxed(
    mut v_k_2350_: *mut LeanObject,
    mut v_x_2351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2352_: *mut LeanObject = core::ptr::null_mut();
    v_res_2352_ =
        l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0(
            v_k_2350_, v_x_2351_,
        );
    lean_dec(v_x_2351_);
    return v_res_2352_;
}
pub unsafe fn l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson(
    mut v_x_2358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_openClose_2359_: u8 = 0;
    let mut v_change_2360_: u8 = 0;
    let mut v_willSave_2361_: u8 = 0;
    let mut v_willSaveWaitUntil_2362_: u8 = 0;
    let mut v_save_x3f_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_openClose_2359_ = lean_ctor_get_uint8(
                    v_x_2358_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_change_2360_ = lean_ctor_get_uint8(
                    v_x_2358_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v_willSave_2361_ = lean_ctor_get_uint8(
                    v_x_2358_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                v_willSaveWaitUntil_2362_ = lean_ctor_get_uint8(
                    v_x_2358_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 3) as u32,
                );
                v_save_x3f_2363_ = lean_ctor_get(v_x_2358_, 0);
                v___x_2364_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0;
                v___x_2365_ = lean_alloc_ctor(1, 0, (1) as u32);
                lean_ctor_set_uint8(v___x_2365_, 0 as u32, v_openClose_2359_);
                v___x_2366_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2366_, 0, v___x_2364_);
                lean_ctor_set(v___x_2366_, 1, v___x_2365_);
                v___x_2367_ = lean_box(0);
                v___x_2368_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2368_, 0, v___x_2366_);
                lean_ctor_set(v___x_2368_, 1, v___x_2367_);
                v___x_2369_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1;
                match v_change_2360_ {
                    0 => {
                        v___x_2392_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1_once
                            ),
                            _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1,
                        );
                        v___y_2371_ = v___x_2392_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_2393_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3_once
                            ),
                            _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3,
                        );
                        v___y_2371_ = v___x_2393_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_2394_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5_once
                            ),
                            _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5,
                        );
                        v___y_2371_ = v___x_2394_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v___y_2371_);
                v___x_2372_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2372_, 0, v___x_2369_);
                lean_ctor_set(v___x_2372_, 1, v___y_2371_);
                v___x_2373_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2373_, 0, v___x_2372_);
                lean_ctor_set(v___x_2373_, 1, v___x_2367_);
                v___x_2374_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2;
                v___x_2375_ = lean_alloc_ctor(1, 0, (1) as u32);
                lean_ctor_set_uint8(v___x_2375_, 0 as u32, v_willSave_2361_);
                v___x_2376_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2376_, 0, v___x_2374_);
                lean_ctor_set(v___x_2376_, 1, v___x_2375_);
                v___x_2377_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2377_, 0, v___x_2376_);
                lean_ctor_set(v___x_2377_, 1, v___x_2367_);
                v___x_2378_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3;
                v___x_2379_ = lean_alloc_ctor(1, 0, (1) as u32);
                lean_ctor_set_uint8(v___x_2379_, 0 as u32, v_willSaveWaitUntil_2362_);
                v___x_2380_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2380_, 0, v___x_2378_);
                lean_ctor_set(v___x_2380_, 1, v___x_2379_);
                v___x_2381_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2381_, 0, v___x_2380_);
                lean_ctor_set(v___x_2381_, 1, v___x_2367_);
                v___x_2382_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__4;
                v___x_2383_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0(v___x_2382_, v_save_x3f_2363_);
                v___x_2384_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2384_, 0, v___x_2383_);
                lean_ctor_set(v___x_2384_, 1, v___x_2367_);
                v___x_2385_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2385_, 0, v___x_2381_);
                lean_ctor_set(v___x_2385_, 1, v___x_2384_);
                v___x_2386_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2386_, 0, v___x_2377_);
                lean_ctor_set(v___x_2386_, 1, v___x_2385_);
                v___x_2387_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2387_, 0, v___x_2373_);
                lean_ctor_set(v___x_2387_, 1, v___x_2386_);
                v___x_2388_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2388_, 0, v___x_2368_);
                lean_ctor_set(v___x_2388_, 1, v___x_2387_);
                v___x_2389_ = l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1;
                v___x_2390_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_2388_, v___x_2389_);
                v___x_2391_ = l_Lean_Json_mkObj(v___x_2390_);
                lean_dec(v___x_2390_);
                return v___x_2391_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___boxed(
    mut v_x_2395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2396_: *mut LeanObject = core::ptr::null_mut();
    v_res_2396_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson(v_x_2395_);
    lean_dec_ref(v_x_2395_);
    return v_res_2396_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0(
    mut v_x_2401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2407_: u8 = 0;
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2411_: u8 = 0;
    let mut v_a_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2415_: u8 = 0;
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2420_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2401_) == 0 {
                    v___x_2402_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0___closed__0;
                    return v___x_2402_;
                } else {
                    v___x_2403_ = l_Lean_Lsp_instFromJsonSaveOptions_fromJson(v_x_2401_);
                    if lean_obj_tag(v___x_2403_) == 0 {
                        v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
                        v_isSharedCheck_2411_ = (!lean_is_exclusive(v___x_2403_)) as u8;
                        if v_isSharedCheck_2411_ == 0 {
                            v___x_2406_ = v___x_2403_;
                            v_isShared_2407_ = v_isSharedCheck_2411_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2404_);
                            lean_dec(v___x_2403_);
                            v___x_2406_ = lean_box(0);
                            v_isShared_2407_ = v_isSharedCheck_2411_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2412_ = lean_ctor_get(v___x_2403_, 0);
                        v_isSharedCheck_2420_ = (!lean_is_exclusive(v___x_2403_)) as u8;
                        if v_isSharedCheck_2420_ == 0 {
                            v___x_2414_ = v___x_2403_;
                            v_isShared_2415_ = v_isSharedCheck_2420_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2412_);
                            lean_dec(v___x_2403_);
                            v___x_2414_ = lean_box(0);
                            v_isShared_2415_ = v_isSharedCheck_2420_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2407_ == 0 {
                    v___x_2409_ = v___x_2406_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
                    v___x_2409_ = v_reuseFailAlloc_2410_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2409_;
            }
            3 => {
                v___x_2416_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2416_, 0, v_a_2412_);
                if v_isShared_2415_ == 0 {
                    lean_ctor_set(v___x_2414_, 0, v___x_2416_);
                    v___x_2418_ = v___x_2414_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2416_);
                    v___x_2418_ = v_reuseFailAlloc_2419_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2418_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0(
    mut v_j_2421_: *mut LeanObject,
    mut v_k_2422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    v___x_2423_ = l_Lean_Json_getObjValD(v_j_2421_, v_k_2422_);
    v___x_2424_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0(v___x_2423_);
    return v___x_2424_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0___boxed(
    mut v_j_2425_: *mut LeanObject,
    mut v_k_2426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2427_: *mut LeanObject = core::ptr::null_mut();
    v_res_2427_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0(v_j_2425_, v_k_2426_);
    lean_dec_ref(v_k_2426_);
    return v_res_2427_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2()
-> *mut LeanObject {
    let mut v___x_2433_: u8 = 0;
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    v___x_2433_ = 1;
    v___x_2434_ = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1;
    v___x_2435_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2434_, v___x_2433_);
    return v___x_2435_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3()
-> *mut LeanObject {
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    v___x_2436_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5;
    v___x_2437_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2,
    );
    v___x_2438_ = lean_string_append(v___x_2437_, v___x_2436_);
    return v___x_2438_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5()
-> *mut LeanObject {
    let mut v___x_2441_: u8 = 0;
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    v___x_2441_ = 1;
    v___x_2442_ = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__4;
    v___x_2443_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2442_, v___x_2441_);
    return v___x_2443_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6()
-> *mut LeanObject {
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    v___x_2444_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5,
    );
    v___x_2445_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3,
    );
    v___x_2446_ = lean_string_append(v___x_2445_, v___x_2444_);
    return v___x_2446_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7()
-> *mut LeanObject {
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    v___x_2447_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_2448_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6,
    );
    v___x_2449_ = lean_string_append(v___x_2448_, v___x_2447_);
    return v___x_2449_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9()
-> *mut LeanObject {
    let mut v___x_2452_: u8 = 0;
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    v___x_2452_ = 1;
    v___x_2453_ = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__8;
    v___x_2454_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2453_, v___x_2452_);
    return v___x_2454_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10()
-> *mut LeanObject {
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    v___x_2455_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9,
    );
    v___x_2456_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3,
    );
    v___x_2457_ = lean_string_append(v___x_2456_, v___x_2455_);
    return v___x_2457_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11()
-> *mut LeanObject {
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    v___x_2458_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_2459_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10,
    );
    v___x_2460_ = lean_string_append(v___x_2459_, v___x_2458_);
    return v___x_2460_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13()
-> *mut LeanObject {
    let mut v___x_2463_: u8 = 0;
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    v___x_2463_ = 1;
    v___x_2464_ = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__12;
    v___x_2465_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2464_, v___x_2463_);
    return v___x_2465_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14()
-> *mut LeanObject {
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    v___x_2466_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13,
    );
    v___x_2467_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3,
    );
    v___x_2468_ = lean_string_append(v___x_2467_, v___x_2466_);
    return v___x_2468_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15()
-> *mut LeanObject {
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    v___x_2469_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_2470_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14,
    );
    v___x_2471_ = lean_string_append(v___x_2470_, v___x_2469_);
    return v___x_2471_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17()
-> *mut LeanObject {
    let mut v___x_2474_: u8 = 0;
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    v___x_2474_ = 1;
    v___x_2475_ = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__16;
    v___x_2476_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2475_, v___x_2474_);
    return v___x_2476_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18()
-> *mut LeanObject {
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    v___x_2477_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17,
    );
    v___x_2478_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3,
    );
    v___x_2479_ = lean_string_append(v___x_2478_, v___x_2477_);
    return v___x_2479_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19()
-> *mut LeanObject {
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    v___x_2480_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_2481_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18,
    );
    v___x_2482_ = lean_string_append(v___x_2481_, v___x_2480_);
    return v___x_2482_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22()
-> *mut LeanObject {
    let mut v___x_2486_: u8 = 0;
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    v___x_2486_ = 1;
    v___x_2487_ = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__21;
    v___x_2488_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2487_, v___x_2486_);
    return v___x_2488_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23()
-> *mut LeanObject {
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    v___x_2489_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22,
    );
    v___x_2490_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3,
    );
    v___x_2491_ = lean_string_append(v___x_2490_, v___x_2489_);
    return v___x_2491_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24()
-> *mut LeanObject {
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    v___x_2492_ = l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10;
    v___x_2493_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23_once
        ),
        _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23,
    );
    v___x_2494_ = lean_string_append(v___x_2493_, v___x_2492_);
    return v___x_2494_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson(
    mut v_json_2495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2501_: u8 = 0;
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2507_: u8 = 0;
    let mut v_a_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2511_: u8 = 0;
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2515_: u8 = 0;
    let mut v_a_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2522_: u8 = 0;
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2528_: u8 = 0;
    let mut v_a_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2532_: u8 = 0;
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2536_: u8 = 0;
    let mut v_a_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2543_: u8 = 0;
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2549_: u8 = 0;
    let mut v_a_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2553_: u8 = 0;
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2557_: u8 = 0;
    let mut v_a_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2564_: u8 = 0;
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2570_: u8 = 0;
    let mut v_a_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2574_: u8 = 0;
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2578_: u8 = 0;
    let mut v_a_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2585_: u8 = 0;
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2591_: u8 = 0;
    let mut v_a_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2595_: u8 = 0;
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2599_: u8 = 0;
    let mut v_a_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2603_: u8 = 0;
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: u8 = 0;
    let mut v___x_2606_: u8 = 0;
    let mut v___x_2607_: u8 = 0;
    let mut v___x_2608_: u8 = 0;
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2612_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2496_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0;
                lean_inc(v_json_2495_);
                v___x_2497_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_2495_, v___x_2496_);
                if lean_obj_tag(v___x_2497_) == 0 {
                    lean_dec(v_json_2495_);
                    v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
                    v_isSharedCheck_2507_ = (!lean_is_exclusive(v___x_2497_)) as u8;
                    if v_isSharedCheck_2507_ == 0 {
                        v___x_2500_ = v___x_2497_;
                        v_isShared_2501_ = v_isSharedCheck_2507_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2498_);
                        lean_dec(v___x_2497_);
                        v___x_2500_ = lean_box(0);
                        v_isShared_2501_ = v_isSharedCheck_2507_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_2497_) == 0 {
                        lean_dec(v_json_2495_);
                        v_a_2508_ = lean_ctor_get(v___x_2497_, 0);
                        v_isSharedCheck_2515_ = (!lean_is_exclusive(v___x_2497_)) as u8;
                        if v_isSharedCheck_2515_ == 0 {
                            v___x_2510_ = v___x_2497_;
                            v_isShared_2511_ = v_isSharedCheck_2515_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2508_);
                            lean_dec(v___x_2497_);
                            v___x_2510_ = lean_box(0);
                            v_isShared_2511_ = v_isSharedCheck_2515_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2516_ = lean_ctor_get(v___x_2497_, 0);
                        lean_inc(v_a_2516_);
                        lean_dec_ref_known(v___x_2497_, 1);
                        v___x_2517_ =
                            l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1;
                        lean_inc(v_json_2495_);
                        v___x_2518_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1(v_json_2495_, v___x_2517_);
                        if lean_obj_tag(v___x_2518_) == 0 {
                            lean_dec(v_a_2516_);
                            lean_dec(v_json_2495_);
                            v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
                            v_isSharedCheck_2528_ = (!lean_is_exclusive(v___x_2518_)) as u8;
                            if v_isSharedCheck_2528_ == 0 {
                                v___x_2521_ = v___x_2518_;
                                v_isShared_2522_ = v_isSharedCheck_2528_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_2519_);
                                lean_dec(v___x_2518_);
                                v___x_2521_ = lean_box(0);
                                v_isShared_2522_ = v_isSharedCheck_2528_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_2518_) == 0 {
                                lean_dec(v_a_2516_);
                                lean_dec(v_json_2495_);
                                v_a_2529_ = lean_ctor_get(v___x_2518_, 0);
                                v_isSharedCheck_2536_ = (!lean_is_exclusive(v___x_2518_)) as u8;
                                if v_isSharedCheck_2536_ == 0 {
                                    v___x_2531_ = v___x_2518_;
                                    v_isShared_2532_ = v_isSharedCheck_2536_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_2529_);
                                    lean_dec(v___x_2518_);
                                    v___x_2531_ = lean_box(0);
                                    v_isShared_2532_ = v_isSharedCheck_2536_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_2537_ = lean_ctor_get(v___x_2518_, 0);
                                lean_inc(v_a_2537_);
                                lean_dec_ref_known(v___x_2518_, 1);
                                v___x_2538_ =
                                    l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2;
                                lean_inc(v_json_2495_);
                                v___x_2539_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_2495_, v___x_2538_);
                                if lean_obj_tag(v___x_2539_) == 0 {
                                    lean_dec(v_a_2537_);
                                    lean_dec(v_a_2516_);
                                    lean_dec(v_json_2495_);
                                    v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
                                    v_isSharedCheck_2549_ = (!lean_is_exclusive(v___x_2539_)) as u8;
                                    if v_isSharedCheck_2549_ == 0 {
                                        v___x_2542_ = v___x_2539_;
                                        v_isShared_2543_ = v_isSharedCheck_2549_;
                                        state = 9;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2540_);
                                        lean_dec(v___x_2539_);
                                        v___x_2542_ = lean_box(0);
                                        v_isShared_2543_ = v_isSharedCheck_2549_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if lean_obj_tag(v___x_2539_) == 0 {
                                        lean_dec(v_a_2537_);
                                        lean_dec(v_a_2516_);
                                        lean_dec(v_json_2495_);
                                        v_a_2550_ = lean_ctor_get(v___x_2539_, 0);
                                        v_isSharedCheck_2557_ =
                                            (!lean_is_exclusive(v___x_2539_)) as u8;
                                        if v_isSharedCheck_2557_ == 0 {
                                            v___x_2552_ = v___x_2539_;
                                            v_isShared_2553_ = v_isSharedCheck_2557_;
                                            state = 11;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2550_);
                                            lean_dec(v___x_2539_);
                                            v___x_2552_ = lean_box(0);
                                            v_isShared_2553_ = v_isSharedCheck_2557_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_2558_ = lean_ctor_get(v___x_2539_, 0);
                                        lean_inc(v_a_2558_);
                                        lean_dec_ref_known(v___x_2539_, 1);
                                        v___x_2559_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3;
                                        lean_inc(v_json_2495_);
                                        v___x_2560_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_2495_, v___x_2559_);
                                        if lean_obj_tag(v___x_2560_) == 0 {
                                            lean_dec(v_a_2558_);
                                            lean_dec(v_a_2537_);
                                            lean_dec(v_a_2516_);
                                            lean_dec(v_json_2495_);
                                            v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
                                            v_isSharedCheck_2570_ =
                                                (!lean_is_exclusive(v___x_2560_)) as u8;
                                            if v_isSharedCheck_2570_ == 0 {
                                                v___x_2563_ = v___x_2560_;
                                                v_isShared_2564_ = v_isSharedCheck_2570_;
                                                state = 13;
                                                continue;
                                            } else {
                                                lean_inc(v_a_2561_);
                                                lean_dec(v___x_2560_);
                                                v___x_2563_ = lean_box(0);
                                                v_isShared_2564_ = v_isSharedCheck_2570_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            if lean_obj_tag(v___x_2560_) == 0 {
                                                lean_dec(v_a_2558_);
                                                lean_dec(v_a_2537_);
                                                lean_dec(v_a_2516_);
                                                lean_dec(v_json_2495_);
                                                v_a_2571_ = lean_ctor_get(v___x_2560_, 0);
                                                v_isSharedCheck_2578_ =
                                                    (!lean_is_exclusive(v___x_2560_)) as u8;
                                                if v_isSharedCheck_2578_ == 0 {
                                                    v___x_2573_ = v___x_2560_;
                                                    v_isShared_2574_ = v_isSharedCheck_2578_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_2571_);
                                                    lean_dec(v___x_2560_);
                                                    v___x_2573_ = lean_box(0);
                                                    v_isShared_2574_ = v_isSharedCheck_2578_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_2579_ = lean_ctor_get(v___x_2560_, 0);
                                                lean_inc(v_a_2579_);
                                                lean_dec_ref_known(v___x_2560_, 1);
                                                v___x_2580_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__4;
                                                v___x_2581_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0(v_json_2495_, v___x_2580_);
                                                if lean_obj_tag(v___x_2581_) == 0 {
                                                    lean_dec(v_a_2579_);
                                                    lean_dec(v_a_2558_);
                                                    lean_dec(v_a_2537_);
                                                    lean_dec(v_a_2516_);
                                                    v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
                                                    v_isSharedCheck_2591_ =
                                                        (!lean_is_exclusive(v___x_2581_)) as u8;
                                                    if v_isSharedCheck_2591_ == 0 {
                                                        v___x_2584_ = v___x_2581_;
                                                        v_isShared_2585_ = v_isSharedCheck_2591_;
                                                        state = 17;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_2582_);
                                                        lean_dec(v___x_2581_);
                                                        v___x_2584_ = lean_box(0);
                                                        v_isShared_2585_ = v_isSharedCheck_2591_;
                                                        state = 17;
                                                        continue;
                                                    }
                                                } else {
                                                    if lean_obj_tag(v___x_2581_) == 0 {
                                                        lean_dec(v_a_2579_);
                                                        lean_dec(v_a_2558_);
                                                        lean_dec(v_a_2537_);
                                                        lean_dec(v_a_2516_);
                                                        v_a_2592_ = lean_ctor_get(v___x_2581_, 0);
                                                        v_isSharedCheck_2599_ =
                                                            (!lean_is_exclusive(v___x_2581_)) as u8;
                                                        if v_isSharedCheck_2599_ == 0 {
                                                            v___x_2594_ = v___x_2581_;
                                                            v_isShared_2595_ =
                                                                v_isSharedCheck_2599_;
                                                            state = 19;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_2592_);
                                                            lean_dec(v___x_2581_);
                                                            v___x_2594_ = lean_box(0);
                                                            v_isShared_2595_ =
                                                                v_isSharedCheck_2599_;
                                                            state = 19;
                                                            continue;
                                                        }
                                                    } else {
                                                        v_a_2600_ = lean_ctor_get(v___x_2581_, 0);
                                                        v_isSharedCheck_2612_ =
                                                            (!lean_is_exclusive(v___x_2581_)) as u8;
                                                        if v_isSharedCheck_2612_ == 0 {
                                                            v___x_2602_ = v___x_2581_;
                                                            v_isShared_2603_ =
                                                                v_isSharedCheck_2612_;
                                                            state = 21;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_2600_);
                                                            lean_dec(v___x_2581_);
                                                            v___x_2602_ = lean_box(0);
                                                            v_isShared_2603_ =
                                                                v_isSharedCheck_2612_;
                                                            state = 21;
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
            }
            1 => {
                v___x_2502_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7,
                );
                v___x_2503_ = lean_string_append(v___x_2502_, v_a_2498_);
                lean_dec(v_a_2498_);
                if v_isShared_2501_ == 0 {
                    lean_ctor_set(v___x_2500_, 0, v___x_2503_);
                    v___x_2505_ = v___x_2500_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2503_);
                    v___x_2505_ = v_reuseFailAlloc_2506_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2505_;
            }
            3 => {
                if v_isShared_2511_ == 0 {
                    lean_ctor_set_tag(v___x_2510_, 0);
                    v___x_2513_ = v___x_2510_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
                    v___x_2513_ = v_reuseFailAlloc_2514_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2513_;
            }
            5 => {
                v___x_2523_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11,
                );
                v___x_2524_ = lean_string_append(v___x_2523_, v_a_2519_);
                lean_dec(v_a_2519_);
                if v_isShared_2522_ == 0 {
                    lean_ctor_set(v___x_2521_, 0, v___x_2524_);
                    v___x_2526_ = v___x_2521_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2527_, 0, v___x_2524_);
                    v___x_2526_ = v_reuseFailAlloc_2527_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2526_;
            }
            7 => {
                if v_isShared_2532_ == 0 {
                    lean_ctor_set_tag(v___x_2531_, 0);
                    v___x_2534_ = v___x_2531_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
                    v___x_2534_ = v_reuseFailAlloc_2535_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2534_;
            }
            9 => {
                v___x_2544_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15,
                );
                v___x_2545_ = lean_string_append(v___x_2544_, v_a_2540_);
                lean_dec(v_a_2540_);
                if v_isShared_2543_ == 0 {
                    lean_ctor_set(v___x_2542_, 0, v___x_2545_);
                    v___x_2547_ = v___x_2542_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2545_);
                    v___x_2547_ = v_reuseFailAlloc_2548_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2547_;
            }
            11 => {
                if v_isShared_2553_ == 0 {
                    lean_ctor_set_tag(v___x_2552_, 0);
                    v___x_2555_ = v___x_2552_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2550_);
                    v___x_2555_ = v_reuseFailAlloc_2556_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2555_;
            }
            13 => {
                v___x_2565_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19,
                );
                v___x_2566_ = lean_string_append(v___x_2565_, v_a_2561_);
                lean_dec(v_a_2561_);
                if v_isShared_2564_ == 0 {
                    lean_ctor_set(v___x_2563_, 0, v___x_2566_);
                    v___x_2568_ = v___x_2563_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2566_);
                    v___x_2568_ = v_reuseFailAlloc_2569_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2568_;
            }
            15 => {
                if v_isShared_2574_ == 0 {
                    lean_ctor_set_tag(v___x_2573_, 0);
                    v___x_2576_ = v___x_2573_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
                    v___x_2576_ = v_reuseFailAlloc_2577_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2576_;
            }
            17 => {
                v___x_2586_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24,
                );
                v___x_2587_ = lean_string_append(v___x_2586_, v_a_2582_);
                lean_dec(v_a_2582_);
                if v_isShared_2585_ == 0 {
                    lean_ctor_set(v___x_2584_, 0, v___x_2587_);
                    v___x_2589_ = v___x_2584_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
                    v___x_2589_ = v_reuseFailAlloc_2590_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2589_;
            }
            19 => {
                if v_isShared_2595_ == 0 {
                    lean_ctor_set_tag(v___x_2594_, 0);
                    v___x_2597_ = v___x_2594_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
                    v___x_2597_ = v_reuseFailAlloc_2598_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2597_;
            }
            21 => {
                v___x_2604_ = lean_alloc_ctor(0, 1, (4) as u32);
                lean_ctor_set(v___x_2604_, 0, v_a_2600_);
                v___x_2605_ = (lean_unbox(v_a_2516_) as u8);
                lean_dec(v_a_2516_);
                lean_ctor_set_uint8(
                    v___x_2604_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2605_,
                );
                v___x_2606_ = (lean_unbox(v_a_2537_) as u8);
                lean_dec(v_a_2537_);
                lean_ctor_set_uint8(
                    v___x_2604_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v___x_2606_,
                );
                v___x_2607_ = (lean_unbox(v_a_2558_) as u8);
                lean_dec(v_a_2558_);
                lean_ctor_set_uint8(
                    v___x_2604_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                    v___x_2607_,
                );
                v___x_2608_ = (lean_unbox(v_a_2579_) as u8);
                lean_dec(v_a_2579_);
                lean_ctor_set_uint8(
                    v___x_2604_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 3) as u32,
                    v___x_2608_,
                );
                if v_isShared_2603_ == 0 {
                    lean_ctor_set(v___x_2602_, 0, v___x_2604_);
                    v___x_2610_ = v___x_2602_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2604_);
                    v___x_2610_ = v_reuseFailAlloc_2611_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2610_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Lsp_TextSync(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Lsp_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Lsp_TextSync(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Lsp_TextSync(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Lsp_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_TextSync(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Lsp_TextSync(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_Lsp_TextSync(builtin);
}
