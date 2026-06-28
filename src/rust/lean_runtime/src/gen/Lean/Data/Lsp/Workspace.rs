// Lean compiler output
// Module: Lean.Data.Lsp.Workspace
// Imports: Lean.Data.Lsp.Basic
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr3};
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getNat_x3f, l_Lean_Json_getObjValD, l_Lean_Json_getStr_x3f, l_Lean_Json_mkObj,
    l_Lean_JsonNumber_fromNat,
};
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_pretty;
use crate::r#gen::Lean::Data::Lsp::Basic::{
    initialize_Lean_Data_Lsp_Basic, runtime_initialize_Lean_Data_Lsp_Basic,
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
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0_value: LeanStringObject<4> =
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
        m_data: [117, 114, 105, 0],
    };
static mut l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1_value: LeanStringObject<5> =
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
static mut l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2_value: LeanArrayObject<0> =
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
static mut l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonWorkspaceFolder___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonWorkspaceFolder_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonWorkspaceFolder___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWorkspaceFolder___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonWorkspaceFolder: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonWorkspaceFolder___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value: LeanStringObject<4> =
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
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__2_value: LeanStringObject<16> =
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
            87, 111, 114, 107, 115, 112, 97, 99, 101, 70, 111, 108, 100, 101, 114, 0,
        ],
    };
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__2_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value)
                as *mut LeanObject,
            6773744487318448338 as *mut LeanObject,
        ],
    };
pub static l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value: LeanCtorObject<3> =
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
                l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__2_value)
                as *mut LeanObject,
            6668733902101006929 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5_value: LeanStringObject<2> =
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
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0_value)
                as *mut LeanObject,
            6053811214292724070 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10_value: LeanStringObject<3> =
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
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1_value)
                as *mut LeanObject,
            5949480926448383572 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonWorkspaceFolder___closed__0_value: LeanClosureObject<0> =
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
static mut l_Lean_Lsp_instFromJsonWorkspaceFolder___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonWorkspaceFolder: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder___closed__0_value)
        as *mut LeanObject;
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__0_value: LeanStringObject<
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
    m_data: [103, 108, 111, 98, 80, 97, 116, 116, 101, 114, 110, 0],
};
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__1_value: LeanStringObject<
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
        70, 105, 108, 101, 83, 121, 115, 116, 101, 109, 87, 97, 116, 99, 104, 101, 114, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__1_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2_value_aux_0: LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2_value_aux_1: LeanCtorObject<
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
            l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value)
            as *mut LeanObject,
        6773744487318448338 as *mut LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2_value: LeanCtorObject<3> =
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
                l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__1_value)
                as *mut LeanObject,
            17539411788740541372 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__0_value)
                as *mut LeanObject,
            13563531222688826382 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__9_value: LeanStringObject<
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
    m_data: [107, 105, 110, 100, 0],
};
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__10_value: LeanStringObject<
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
    m_data: [107, 105, 110, 100, 63, 0],
};
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__11_value: LeanCtorObject<3> =
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
                l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__10_value
            ) as *mut LeanObject,
            13532862018704899050 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonFileSystemWatcher___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonFileSystemWatcher___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileSystemWatcher___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonFileSystemWatcher: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileSystemWatcher___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonFileSystemWatcher___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonFileSystemWatcher_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonFileSystemWatcher___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonFileSystemWatcher___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonFileSystemWatcher: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonFileSystemWatcher___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_FileSystemWatcher_create: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Lsp_FileSystemWatcher_change: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Lsp_FileSystemWatcher_delete: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [119, 97, 116, 99, 104, 101, 114, 115, 0]};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__1_value: LeanStringObject<41> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [68, 105, 100, 67, 104, 97, 110, 103, 101, 87, 97, 116, 99, 104, 101, 100, 70, 105, 108, 101, 115, 82, 101, 103, 105, 115, 116, 114, 97, 116, 105, 111, 110, 79, 112, 116, 105, 111, 110, 115, 0]};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__1_value
) as *mut LeanObject;
static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value) as *mut LeanObject,6773744487318448338 as *mut LeanObject] };
pub static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__1_value) as *mut LeanObject,15581767320145518792 as *mut LeanObject] };
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2_value
) as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0_value) as *mut LeanObject,10377628074256779973 as *mut LeanObject] };
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__5_value
) as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions___closed__0_value:
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
    m_fun: l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions___closed__0_value
) as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions___closed__0_value:
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
    m_fun: l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions___closed__0_value
) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__0_value: LeanStringObject<26> =
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
            101, 120, 112, 101, 99, 116, 101, 100, 32, 49, 44, 32, 50, 44, 32, 111, 114, 32, 51,
            44, 32, 103, 111, 116, 32, 0,
        ],
    };
static mut l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__1_value: LeanCtorObject<1> =
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
static mut l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__2_value: LeanCtorObject<1> =
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
static mut l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__3_value: LeanCtorObject<1> =
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
static mut l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonFileChangeType___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonFileChangeType___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonFileChangeType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileChangeType___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonFileChangeType: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileChangeType___closed__0_value) as *mut LeanObject;
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instToJsonFileChangeType___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonFileChangeType___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonFileChangeType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonFileChangeType___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonFileChangeType: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonFileChangeType___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__0_value: LeanStringObject<10> =
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
        m_data: [70, 105, 108, 101, 69, 118, 101, 110, 116, 0],
    };
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__0_value)
        as *mut LeanObject;
static l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value)
                as *mut LeanObject,
            6773744487318448338 as *mut LeanObject,
        ],
    };
pub static l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__0_value)
                as *mut LeanObject,
            14989506372905311455 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6_value: LeanStringObject<5> =
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
        m_data: [116, 121, 112, 101, 0],
    };
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6_value)
                as *mut LeanObject,
            11503787708459150704 as *mut LeanObject,
        ],
    };
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonFileEvent___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instFromJsonFileEvent_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instFromJsonFileEvent___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileEvent___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonFileEvent: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonFileEvent___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonFileEvent___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonFileEvent_toJson___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonFileEvent___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonFileEvent___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonFileEvent: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonFileEvent___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0_value:
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
    m_data: [99, 104, 97, 110, 103, 101, 115, 0],
};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__1_value:
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
        68, 105, 100, 67, 104, 97, 110, 103, 101, 87, 97, 116, 99, 104, 101, 100, 70, 105, 108,
        101, 115, 80, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__1_value
) as *mut LeanObject;
static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2_value_aux_1:
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
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__1_value)
            as *mut LeanObject,
        6773744487318448338 as *mut LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2_value:
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
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__1_value
        ) as *mut LeanObject,
        403225530036258855 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2_value
) as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__5_value:
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
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0_value
        ) as *mut LeanObject,
        729844717526787275 as *mut LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__5_value
) as *mut LeanObject;
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams___closed__0_value: LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams___closed__0_value: LeanClosureObject<
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
    m_fun: l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(
    mut v_a_841_: *mut LeanObject,
    mut v_a_842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_841_) == 0 {
                    v___x_843_ = lean_array_to_list(v_a_842_);
                    return v___x_843_;
                } else {
                    v_head_844_ = lean_ctor_get(v_a_841_, 0);
                    lean_inc(v_head_844_);
                    v_tail_845_ = lean_ctor_get(v_a_841_, 1);
                    lean_inc(v_tail_845_);
                    lean_dec_ref_known(v_a_841_, 2);
                    v___x_846_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_842_,
                        v_head_844_,
                    );
                    v_a_841_ = v_tail_845_;
                    v_a_842_ = v___x_846_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonWorkspaceFolder_toJson(
    mut v_x_852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_uri_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_857_: u8 = 0;
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_874_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_uri_853_ = lean_ctor_get(v_x_852_, 0);
                v_name_854_ = lean_ctor_get(v_x_852_, 1);
                v_isSharedCheck_874_ = (!lean_is_exclusive(v_x_852_)) as u8;
                if v_isSharedCheck_874_ == 0 {
                    v___x_856_ = v_x_852_;
                    v_isShared_857_ = v_isSharedCheck_874_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_name_854_);
                    lean_inc(v_uri_853_);
                    lean_dec(v_x_852_);
                    v___x_856_ = lean_box(0);
                    v_isShared_857_ = v_isSharedCheck_874_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_858_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0;
                v___x_859_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_859_, 0, v_uri_853_);
                if v_isShared_857_ == 0 {
                    lean_ctor_set(v___x_856_, 1, v___x_859_);
                    lean_ctor_set(v___x_856_, 0, v___x_858_);
                    v___x_861_ = v___x_856_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_858_);
                    lean_ctor_set(v_reuseFailAlloc_873_, 1, v___x_859_);
                    v___x_861_ = v_reuseFailAlloc_873_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_862_ = lean_box(0);
                v___x_863_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_863_, 0, v___x_861_);
                lean_ctor_set(v___x_863_, 1, v___x_862_);
                v___x_864_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1;
                v___x_865_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_865_, 0, v_name_854_);
                v___x_866_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_866_, 0, v___x_864_);
                lean_ctor_set(v___x_866_, 1, v___x_865_);
                v___x_867_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_867_, 0, v___x_866_);
                lean_ctor_set(v___x_867_, 1, v___x_862_);
                v___x_868_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_868_, 0, v___x_867_);
                lean_ctor_set(v___x_868_, 1, v___x_862_);
                v___x_869_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_869_, 0, v___x_863_);
                lean_ctor_set(v___x_869_, 1, v___x_868_);
                v___x_870_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2;
                v___x_871_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(v___x_869_, v___x_870_);
                v___x_872_ = l_Lean_Json_mkObj(v___x_871_);
                lean_dec(v___x_871_);
                return v___x_872_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(
    mut v_j_877_: *mut LeanObject,
    mut v_k_878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    v___x_879_ = l_Lean_Json_getObjValD(v_j_877_, v_k_878_);
    v___x_880_ = l_Lean_Json_getStr_x3f(v___x_879_);
    return v___x_880_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0___boxed(
    mut v_j_881_: *mut LeanObject,
    mut v_k_882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_883_: *mut LeanObject = core::ptr::null_mut();
    v_res_883_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(
            v_j_881_, v_k_882_,
        );
    lean_dec_ref(v_k_882_);
    return v_res_883_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4() -> *mut LeanObject
{
    let mut v___x_891_: u8 = 0;
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    v___x_891_ = 1;
    v___x_892_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__3;
    v___x_893_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_892_, v___x_891_);
    return v___x_893_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6() -> *mut LeanObject
{
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    v___x_895_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5;
    v___x_896_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__4,
    );
    v___x_897_ = lean_string_append(v___x_896_, v___x_895_);
    return v___x_897_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8() -> *mut LeanObject
{
    let mut v___x_900_: u8 = 0;
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    v___x_900_ = 1;
    v___x_901_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__7;
    v___x_902_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_901_, v___x_900_);
    return v___x_902_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__9() -> *mut LeanObject
{
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    v___x_903_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8_once),
        _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8,
    );
    v___x_904_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6,
    );
    v___x_905_ = lean_string_append(v___x_904_, v___x_903_);
    return v___x_905_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__11() -> *mut LeanObject
{
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    v___x_907_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10;
    v___x_908_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__9_once),
        _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__9,
    );
    v___x_909_ = lean_string_append(v___x_908_, v___x_907_);
    return v___x_909_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__13() -> *mut LeanObject
{
    let mut v___x_912_: u8 = 0;
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    v___x_912_ = 1;
    v___x_913_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__12;
    v___x_914_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_913_, v___x_912_);
    return v___x_914_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__14() -> *mut LeanObject
{
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    v___x_915_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__13_once),
        _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__13,
    );
    v___x_916_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__6,
    );
    v___x_917_ = lean_string_append(v___x_916_, v___x_915_);
    return v___x_917_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15() -> *mut LeanObject
{
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    v___x_918_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10;
    v___x_919_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__14_once),
        _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__14,
    );
    v___x_920_ = lean_string_append(v___x_919_, v___x_918_);
    return v___x_920_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson(
    mut v_json_921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_927_: u8 = 0;
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_933_: u8 = 0;
    let mut v_a_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_937_: u8 = 0;
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_941_: u8 = 0;
    let mut v_a_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_948_: u8 = 0;
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_954_: u8 = 0;
    let mut v_a_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_958_: u8 = 0;
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_962_: u8 = 0;
    let mut v_a_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_966_: u8 = 0;
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_922_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0;
                lean_inc(v_json_921_);
                v___x_923_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(v_json_921_, v___x_922_);
                if lean_obj_tag(v___x_923_) == 0 {
                    lean_dec(v_json_921_);
                    v_a_924_ = lean_ctor_get(v___x_923_, 0);
                    v_isSharedCheck_933_ = (!lean_is_exclusive(v___x_923_)) as u8;
                    if v_isSharedCheck_933_ == 0 {
                        v___x_926_ = v___x_923_;
                        v_isShared_927_ = v_isSharedCheck_933_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_924_);
                        lean_dec(v___x_923_);
                        v___x_926_ = lean_box(0);
                        v_isShared_927_ = v_isSharedCheck_933_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_923_) == 0 {
                        lean_dec(v_json_921_);
                        v_a_934_ = lean_ctor_get(v___x_923_, 0);
                        v_isSharedCheck_941_ = (!lean_is_exclusive(v___x_923_)) as u8;
                        if v_isSharedCheck_941_ == 0 {
                            v___x_936_ = v___x_923_;
                            v_isShared_937_ = v_isSharedCheck_941_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_934_);
                            lean_dec(v___x_923_);
                            v___x_936_ = lean_box(0);
                            v_isShared_937_ = v_isSharedCheck_941_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_942_ = lean_ctor_get(v___x_923_, 0);
                        lean_inc(v_a_942_);
                        lean_dec_ref_known(v___x_923_, 1);
                        v___x_943_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__1;
                        v___x_944_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(v_json_921_, v___x_943_);
                        if lean_obj_tag(v___x_944_) == 0 {
                            lean_dec(v_a_942_);
                            v_a_945_ = lean_ctor_get(v___x_944_, 0);
                            v_isSharedCheck_954_ = (!lean_is_exclusive(v___x_944_)) as u8;
                            if v_isSharedCheck_954_ == 0 {
                                v___x_947_ = v___x_944_;
                                v_isShared_948_ = v_isSharedCheck_954_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_945_);
                                lean_dec(v___x_944_);
                                v___x_947_ = lean_box(0);
                                v_isShared_948_ = v_isSharedCheck_954_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_944_) == 0 {
                                lean_dec(v_a_942_);
                                v_a_955_ = lean_ctor_get(v___x_944_, 0);
                                v_isSharedCheck_962_ = (!lean_is_exclusive(v___x_944_)) as u8;
                                if v_isSharedCheck_962_ == 0 {
                                    v___x_957_ = v___x_944_;
                                    v_isShared_958_ = v_isSharedCheck_962_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_955_);
                                    lean_dec(v___x_944_);
                                    v___x_957_ = lean_box(0);
                                    v_isShared_958_ = v_isSharedCheck_962_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_963_ = lean_ctor_get(v___x_944_, 0);
                                v_isSharedCheck_971_ = (!lean_is_exclusive(v___x_944_)) as u8;
                                if v_isSharedCheck_971_ == 0 {
                                    v___x_965_ = v___x_944_;
                                    v_isShared_966_ = v_isSharedCheck_971_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_963_);
                                    lean_dec(v___x_944_);
                                    v___x_965_ = lean_box(0);
                                    v_isShared_966_ = v_isSharedCheck_971_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_928_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__11_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__11,
                );
                v___x_929_ = lean_string_append(v___x_928_, v_a_924_);
                lean_dec(v_a_924_);
                if v_isShared_927_ == 0 {
                    lean_ctor_set(v___x_926_, 0, v___x_929_);
                    v___x_931_ = v___x_926_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
                    v___x_931_ = v_reuseFailAlloc_932_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_931_;
            }
            3 => {
                if v_isShared_937_ == 0 {
                    lean_ctor_set_tag(v___x_936_, 0);
                    v___x_939_ = v___x_936_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
                    v___x_939_ = v_reuseFailAlloc_940_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_939_;
            }
            5 => {
                v___x_949_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__15,
                );
                v___x_950_ = lean_string_append(v___x_949_, v_a_945_);
                lean_dec(v_a_945_);
                if v_isShared_948_ == 0 {
                    lean_ctor_set(v___x_947_, 0, v___x_950_);
                    v___x_952_ = v___x_947_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
                    v___x_952_ = v_reuseFailAlloc_953_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_952_;
            }
            7 => {
                if v_isShared_958_ == 0 {
                    lean_ctor_set_tag(v___x_957_, 0);
                    v___x_960_ = v___x_957_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
                    v___x_960_ = v_reuseFailAlloc_961_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_960_;
            }
            9 => {
                v___x_967_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_967_, 0, v_a_942_);
                lean_ctor_set(v___x_967_, 1, v_a_963_);
                if v_isShared_966_ == 0 {
                    lean_ctor_set(v___x_965_, 0, v___x_967_);
                    v___x_969_ = v___x_965_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
                    v___x_969_ = v_reuseFailAlloc_970_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_969_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0(
    mut v_x_976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_982_: u8 = 0;
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_986_: u8 = 0;
    let mut v_a_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_990_: u8 = 0;
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_995_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_976_) == 0 {
                    v___x_977_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0___closed__0;
                    return v___x_977_;
                } else {
                    v___x_978_ = l_Lean_Json_getNat_x3f(v_x_976_);
                    if lean_obj_tag(v___x_978_) == 0 {
                        v_a_979_ = lean_ctor_get(v___x_978_, 0);
                        v_isSharedCheck_986_ = (!lean_is_exclusive(v___x_978_)) as u8;
                        if v_isSharedCheck_986_ == 0 {
                            v___x_981_ = v___x_978_;
                            v_isShared_982_ = v_isSharedCheck_986_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_979_);
                            lean_dec(v___x_978_);
                            v___x_981_ = lean_box(0);
                            v_isShared_982_ = v_isSharedCheck_986_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_987_ = lean_ctor_get(v___x_978_, 0);
                        v_isSharedCheck_995_ = (!lean_is_exclusive(v___x_978_)) as u8;
                        if v_isSharedCheck_995_ == 0 {
                            v___x_989_ = v___x_978_;
                            v_isShared_990_ = v_isSharedCheck_995_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_987_);
                            lean_dec(v___x_978_);
                            v___x_989_ = lean_box(0);
                            v_isShared_990_ = v_isSharedCheck_995_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_982_ == 0 {
                    v___x_984_ = v___x_981_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
                    v___x_984_ = v_reuseFailAlloc_985_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_984_;
            }
            3 => {
                v___x_991_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_991_, 0, v_a_987_);
                if v_isShared_990_ == 0 {
                    lean_ctor_set(v___x_989_, 0, v___x_991_);
                    v___x_993_ = v___x_989_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
                    v___x_993_ = v_reuseFailAlloc_994_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_993_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0(
    mut v_j_996_: *mut LeanObject,
    mut v_k_997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    v___x_998_ = l_Lean_Json_getObjValD(v_j_996_, v_k_997_);
    v___x_999_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0_spec__0(v___x_998_);
    return v___x_999_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0___boxed(
    mut v_j_1000_: *mut LeanObject,
    mut v_k_1001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1002_: *mut LeanObject = core::ptr::null_mut();
    v_res_1002_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0(v_j_1000_, v_k_1001_);
    lean_dec_ref(v_k_1001_);
    return v_res_1002_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3()
-> *mut LeanObject {
    let mut v___x_1009_: u8 = 0;
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    v___x_1009_ = 1;
    v___x_1010_ = l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__2;
    v___x_1011_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1010_, v___x_1009_);
    return v___x_1011_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4()
-> *mut LeanObject {
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    v___x_1012_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5;
    v___x_1013_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__3,
    );
    v___x_1014_ = lean_string_append(v___x_1013_, v___x_1012_);
    return v___x_1014_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6()
-> *mut LeanObject {
    let mut v___x_1017_: u8 = 0;
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    v___x_1017_ = 1;
    v___x_1018_ = l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__5;
    v___x_1019_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1018_, v___x_1017_);
    return v___x_1019_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7()
-> *mut LeanObject {
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    v___x_1020_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__6,
    );
    v___x_1021_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4,
    );
    v___x_1022_ = lean_string_append(v___x_1021_, v___x_1020_);
    return v___x_1022_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8()
-> *mut LeanObject {
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    v___x_1023_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10;
    v___x_1024_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7_once),
        _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__7,
    );
    v___x_1025_ = lean_string_append(v___x_1024_, v___x_1023_);
    return v___x_1025_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12()
-> *mut LeanObject {
    let mut v___x_1030_: u8 = 0;
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    v___x_1030_ = 1;
    v___x_1031_ = l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__11;
    v___x_1032_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1031_, v___x_1030_);
    return v___x_1032_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13()
-> *mut LeanObject {
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    v___x_1033_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12_once
        ),
        _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__12,
    );
    v___x_1034_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__4,
    );
    v___x_1035_ = lean_string_append(v___x_1034_, v___x_1033_);
    return v___x_1035_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14()
-> *mut LeanObject {
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    v___x_1036_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10;
    v___x_1037_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13_once
        ),
        _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__13,
    );
    v___x_1038_ = lean_string_append(v___x_1037_, v___x_1036_);
    return v___x_1038_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson(
    mut v_json_1039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1045_: u8 = 0;
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1051_: u8 = 0;
    let mut v_a_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1055_: u8 = 0;
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1059_: u8 = 0;
    let mut v_a_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1066_: u8 = 0;
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1072_: u8 = 0;
    let mut v_a_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1076_: u8 = 0;
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1080_: u8 = 0;
    let mut v_a_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1084_: u8 = 0;
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1089_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1040_ = l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__0;
                lean_inc(v_json_1039_);
                v___x_1041_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(v_json_1039_, v___x_1040_);
                if lean_obj_tag(v___x_1041_) == 0 {
                    lean_dec(v_json_1039_);
                    v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
                    v_isSharedCheck_1051_ = (!lean_is_exclusive(v___x_1041_)) as u8;
                    if v_isSharedCheck_1051_ == 0 {
                        v___x_1044_ = v___x_1041_;
                        v_isShared_1045_ = v_isSharedCheck_1051_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1042_);
                        lean_dec(v___x_1041_);
                        v___x_1044_ = lean_box(0);
                        v_isShared_1045_ = v_isSharedCheck_1051_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_1041_) == 0 {
                        lean_dec(v_json_1039_);
                        v_a_1052_ = lean_ctor_get(v___x_1041_, 0);
                        v_isSharedCheck_1059_ = (!lean_is_exclusive(v___x_1041_)) as u8;
                        if v_isSharedCheck_1059_ == 0 {
                            v___x_1054_ = v___x_1041_;
                            v_isShared_1055_ = v_isSharedCheck_1059_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1052_);
                            lean_dec(v___x_1041_);
                            v___x_1054_ = lean_box(0);
                            v_isShared_1055_ = v_isSharedCheck_1059_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1060_ = lean_ctor_get(v___x_1041_, 0);
                        lean_inc(v_a_1060_);
                        lean_dec_ref_known(v___x_1041_, 1);
                        v___x_1061_ = l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__9;
                        v___x_1062_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileSystemWatcher_fromJson_spec__0(v_json_1039_, v___x_1061_);
                        if lean_obj_tag(v___x_1062_) == 0 {
                            lean_dec(v_a_1060_);
                            v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
                            v_isSharedCheck_1072_ = (!lean_is_exclusive(v___x_1062_)) as u8;
                            if v_isSharedCheck_1072_ == 0 {
                                v___x_1065_ = v___x_1062_;
                                v_isShared_1066_ = v_isSharedCheck_1072_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_1063_);
                                lean_dec(v___x_1062_);
                                v___x_1065_ = lean_box(0);
                                v_isShared_1066_ = v_isSharedCheck_1072_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_1062_) == 0 {
                                lean_dec(v_a_1060_);
                                v_a_1073_ = lean_ctor_get(v___x_1062_, 0);
                                v_isSharedCheck_1080_ = (!lean_is_exclusive(v___x_1062_)) as u8;
                                if v_isSharedCheck_1080_ == 0 {
                                    v___x_1075_ = v___x_1062_;
                                    v_isShared_1076_ = v_isSharedCheck_1080_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_1073_);
                                    lean_dec(v___x_1062_);
                                    v___x_1075_ = lean_box(0);
                                    v_isShared_1076_ = v_isSharedCheck_1080_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_1081_ = lean_ctor_get(v___x_1062_, 0);
                                v_isSharedCheck_1089_ = (!lean_is_exclusive(v___x_1062_)) as u8;
                                if v_isSharedCheck_1089_ == 0 {
                                    v___x_1083_ = v___x_1062_;
                                    v_isShared_1084_ = v_isSharedCheck_1089_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_1081_);
                                    lean_dec(v___x_1062_);
                                    v___x_1083_ = lean_box(0);
                                    v_isShared_1084_ = v_isSharedCheck_1089_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1046_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__8,
                );
                v___x_1047_ = lean_string_append(v___x_1046_, v_a_1042_);
                lean_dec(v_a_1042_);
                if v_isShared_1045_ == 0 {
                    lean_ctor_set(v___x_1044_, 0, v___x_1047_);
                    v___x_1049_ = v___x_1044_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1047_);
                    v___x_1049_ = v_reuseFailAlloc_1050_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1049_;
            }
            3 => {
                if v_isShared_1055_ == 0 {
                    lean_ctor_set_tag(v___x_1054_, 0);
                    v___x_1057_ = v___x_1054_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
                    v___x_1057_ = v_reuseFailAlloc_1058_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1057_;
            }
            5 => {
                v___x_1067_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__14,
                );
                v___x_1068_ = lean_string_append(v___x_1067_, v_a_1063_);
                lean_dec(v_a_1063_);
                if v_isShared_1066_ == 0 {
                    lean_ctor_set(v___x_1065_, 0, v___x_1068_);
                    v___x_1070_ = v___x_1065_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1068_);
                    v___x_1070_ = v_reuseFailAlloc_1071_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1070_;
            }
            7 => {
                if v_isShared_1076_ == 0 {
                    lean_ctor_set_tag(v___x_1075_, 0);
                    v___x_1078_ = v___x_1075_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
                    v___x_1078_ = v_reuseFailAlloc_1079_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1078_;
            }
            9 => {
                v___x_1085_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1085_, 0, v_a_1060_);
                lean_ctor_set(v___x_1085_, 1, v_a_1081_);
                if v_isShared_1084_ == 0 {
                    lean_ctor_set(v___x_1083_, 0, v___x_1085_);
                    v___x_1087_ = v___x_1083_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
                    v___x_1087_ = v_reuseFailAlloc_1088_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1087_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Lsp_instToJsonFileSystemWatcher_toJson_spec__0(
    mut v_k_1092_: *mut LeanObject,
    mut v_x_1093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1098_: u8 = 0;
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1093_) == 0 {
                    lean_dec_ref(v_k_1092_);
                    v___x_1094_ = lean_box(0);
                    return v___x_1094_;
                } else {
                    v_val_1095_ = lean_ctor_get(v_x_1093_, 0);
                    v_isSharedCheck_1106_ = (!lean_is_exclusive(v_x_1093_)) as u8;
                    if v_isSharedCheck_1106_ == 0 {
                        v___x_1097_ = v_x_1093_;
                        v_isShared_1098_ = v_isSharedCheck_1106_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1095_);
                        lean_dec(v_x_1093_);
                        v___x_1097_ = lean_box(0);
                        v_isShared_1098_ = v_isSharedCheck_1106_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1099_ = l_Lean_JsonNumber_fromNat(v_val_1095_);
                if v_isShared_1098_ == 0 {
                    lean_ctor_set_tag(v___x_1097_, 2);
                    lean_ctor_set(v___x_1097_, 0, v___x_1099_);
                    v___x_1101_ = v___x_1097_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1105_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1099_);
                    v___x_1101_ = v_reuseFailAlloc_1105_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1102_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1102_, 0, v_k_1092_);
                lean_ctor_set(v___x_1102_, 1, v___x_1101_);
                v___x_1103_ = lean_box(0);
                v___x_1104_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1104_, 0, v___x_1102_);
                lean_ctor_set(v___x_1104_, 1, v___x_1103_);
                return v___x_1104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonFileSystemWatcher_toJson(
    mut v_x_1107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_globPattern_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_x3f_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1112_: u8 = 0;
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1127_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_globPattern_1108_ = lean_ctor_get(v_x_1107_, 0);
                v_kind_x3f_1109_ = lean_ctor_get(v_x_1107_, 1);
                v_isSharedCheck_1127_ = (!lean_is_exclusive(v_x_1107_)) as u8;
                if v_isSharedCheck_1127_ == 0 {
                    v___x_1111_ = v_x_1107_;
                    v_isShared_1112_ = v_isSharedCheck_1127_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_kind_x3f_1109_);
                    lean_inc(v_globPattern_1108_);
                    lean_dec(v_x_1107_);
                    v___x_1111_ = lean_box(0);
                    v_isShared_1112_ = v_isSharedCheck_1127_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1113_ = l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__0;
                v___x_1114_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1114_, 0, v_globPattern_1108_);
                if v_isShared_1112_ == 0 {
                    lean_ctor_set(v___x_1111_, 1, v___x_1114_);
                    lean_ctor_set(v___x_1111_, 0, v___x_1113_);
                    v___x_1116_ = v___x_1111_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1113_);
                    lean_ctor_set(v_reuseFailAlloc_1126_, 1, v___x_1114_);
                    v___x_1116_ = v_reuseFailAlloc_1126_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1117_ = lean_box(0);
                v___x_1118_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1118_, 0, v___x_1116_);
                lean_ctor_set(v___x_1118_, 1, v___x_1117_);
                v___x_1119_ = l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson___closed__9;
                v___x_1120_ =
                    l_Lean_Json_opt___at___00Lean_Lsp_instToJsonFileSystemWatcher_toJson_spec__0(
                        v___x_1119_,
                        v_kind_x3f_1109_,
                    );
                v___x_1121_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1121_, 0, v___x_1120_);
                lean_ctor_set(v___x_1121_, 1, v___x_1117_);
                v___x_1122_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1122_, 0, v___x_1118_);
                lean_ctor_set(v___x_1122_, 1, v___x_1121_);
                v___x_1123_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2;
                v___x_1124_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(v___x_1122_, v___x_1123_);
                v___x_1125_ = l_Lean_Json_mkObj(v___x_1124_);
                lean_dec(v___x_1124_);
                return v___x_1125_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Lsp_FileSystemWatcher_create() -> *mut LeanObject {
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    v___x_1130_ = lean_unsigned_to_nat(1);
    return v___x_1130_;
}
pub unsafe fn _init_l_Lean_Lsp_FileSystemWatcher_change() -> *mut LeanObject {
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    v___x_1131_ = lean_unsigned_to_nat(2);
    return v___x_1131_;
}
pub unsafe fn _init_l_Lean_Lsp_FileSystemWatcher_delete() -> *mut LeanObject {
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    v___x_1132_ = lean_unsigned_to_nat(4);
    return v___x_1132_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1(
    mut v_sz_1133_: usize,
    mut v_i_1134_: usize,
    mut v_bs_1135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1136_: u8 = 0;
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1143_: u8 = 0;
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1147_: u8 = 0;
    let mut v_a_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: usize = 0;
    let mut v___x_1152_: usize = 0;
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1136_ = lean_usize_dec_lt(v_i_1134_, v_sz_1133_);
                if v___x_1136_ == 0 {
                    v___x_1137_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1137_, 0, v_bs_1135_);
                    return v___x_1137_;
                } else {
                    v_v_1138_ = lean_array_uget_borrowed(v_bs_1135_, v_i_1134_);
                    lean_inc(v_v_1138_);
                    v___x_1139_ = l_Lean_Lsp_instFromJsonFileSystemWatcher_fromJson(v_v_1138_);
                    if lean_obj_tag(v___x_1139_) == 0 {
                        lean_dec_ref(v_bs_1135_);
                        v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
                        v_isSharedCheck_1147_ = (!lean_is_exclusive(v___x_1139_)) as u8;
                        if v_isSharedCheck_1147_ == 0 {
                            v___x_1142_ = v___x_1139_;
                            v_isShared_1143_ = v_isSharedCheck_1147_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1140_);
                            lean_dec(v___x_1139_);
                            v___x_1142_ = lean_box(0);
                            v_isShared_1143_ = v_isSharedCheck_1147_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1148_ = lean_ctor_get(v___x_1139_, 0);
                        lean_inc(v_a_1148_);
                        lean_dec_ref_known(v___x_1139_, 1);
                        v___x_1149_ = lean_unsigned_to_nat(0);
                        v_bs_x27_1150_ = lean_array_uset(v_bs_1135_, v_i_1134_, v___x_1149_);
                        v___x_1151_ = 1usize;
                        v___x_1152_ = lean_usize_add(v_i_1134_, v___x_1151_);
                        v___x_1153_ = lean_array_uset(v_bs_x27_1150_, v_i_1134_, v_a_1148_);
                        v_i_1134_ = v___x_1152_;
                        v_bs_1135_ = v___x_1153_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1143_ == 0 {
                    v___x_1145_ = v___x_1142_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
                    v___x_1145_ = v_reuseFailAlloc_1146_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1145_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1___boxed(
    mut v_sz_1155_: *mut LeanObject,
    mut v_i_1156_: *mut LeanObject,
    mut v_bs_1157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1158_: usize = 0;
    let mut v_i_boxed_1159_: usize = 0;
    let mut v_res_1160_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1158_ = lean_unbox_usize(v_sz_1155_);
    lean_dec(v_sz_1155_);
    v_i_boxed_1159_ = lean_unbox_usize(v_i_1156_);
    lean_dec(v_i_1156_);
    v_res_1160_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_1158_, v_i_boxed_1159_, v_bs_1157_);
    return v_res_1160_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0(
    mut v_x_1163_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1163_) == 4 {
        let mut v_elems_1164_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_1165_: usize = 0;
        let mut v___x_1166_: usize = 0;
        let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
        v_elems_1164_ = lean_ctor_get(v_x_1163_, 0);
        lean_inc_ref(v_elems_1164_);
        lean_dec_ref_known(v_x_1163_, 1);
        v_sz_1165_ = lean_array_size(v_elems_1164_);
        v___x_1166_ = 0usize;
        v___x_1167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0_spec__1(v_sz_1165_, v___x_1166_, v_elems_1164_);
        return v___x_1167_;
    } else {
        let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
        v___x_1168_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0;
        v___x_1169_ = lean_unsigned_to_nat(80);
        v___x_1170_ = l_Lean_Json_pretty(v_x_1163_, v___x_1169_);
        v___x_1171_ = lean_string_append(v___x_1168_, v___x_1170_);
        lean_dec_ref(v___x_1170_);
        v___x_1172_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1;
        v___x_1173_ = lean_string_append(v___x_1171_, v___x_1172_);
        v___x_1174_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1174_, 0, v___x_1173_);
        return v___x_1174_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0(
    mut v_j_1175_: *mut LeanObject,
    mut v_k_1176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    v___x_1177_ = l_Lean_Json_getObjValD(v_j_1175_, v_k_1176_);
    v___x_1178_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0(v___x_1177_);
    return v___x_1178_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0___boxed(
    mut v_j_1179_: *mut LeanObject,
    mut v_k_1180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1181_: *mut LeanObject = core::ptr::null_mut();
    v_res_1181_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0(v_j_1179_, v_k_1180_);
    lean_dec_ref(v_k_1180_);
    return v_res_1181_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3()
-> *mut LeanObject {
    let mut v___x_1188_: u8 = 0;
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    v___x_1188_ = 1;
    v___x_1189_ =
        l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__2;
    v___x_1190_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1189_, v___x_1188_);
    return v___x_1190_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4()
-> *mut LeanObject {
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    v___x_1191_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5;
    v___x_1192_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3_once), _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__3);
    v___x_1193_ = lean_string_append(v___x_1192_, v___x_1191_);
    return v___x_1193_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6()
-> *mut LeanObject {
    let mut v___x_1196_: u8 = 0;
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    v___x_1196_ = 1;
    v___x_1197_ =
        l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__5;
    v___x_1198_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1197_, v___x_1196_);
    return v___x_1198_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7()
-> *mut LeanObject {
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    v___x_1199_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6_once), _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__6);
    v___x_1200_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4_once), _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__4);
    v___x_1201_ = lean_string_append(v___x_1200_, v___x_1199_);
    return v___x_1201_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8()
-> *mut LeanObject {
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    v___x_1202_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10;
    v___x_1203_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7_once), _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__7);
    v___x_1204_ = lean_string_append(v___x_1203_, v___x_1202_);
    return v___x_1204_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson(
    mut v_json_1205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1211_: u8 = 0;
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1217_: u8 = 0;
    let mut v_a_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1221_: u8 = 0;
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1225_: u8 = 0;
    let mut v_a_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1229_: u8 = 0;
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1206_ = l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0;
                v___x_1207_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0(v_json_1205_, v___x_1206_);
                if lean_obj_tag(v___x_1207_) == 0 {
                    v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
                    v_isSharedCheck_1217_ = (!lean_is_exclusive(v___x_1207_)) as u8;
                    if v_isSharedCheck_1217_ == 0 {
                        v___x_1210_ = v___x_1207_;
                        v_isShared_1211_ = v_isSharedCheck_1217_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1208_);
                        lean_dec(v___x_1207_);
                        v___x_1210_ = lean_box(0);
                        v_isShared_1211_ = v_isSharedCheck_1217_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_1207_) == 0 {
                        v_a_1218_ = lean_ctor_get(v___x_1207_, 0);
                        v_isSharedCheck_1225_ = (!lean_is_exclusive(v___x_1207_)) as u8;
                        if v_isSharedCheck_1225_ == 0 {
                            v___x_1220_ = v___x_1207_;
                            v_isShared_1221_ = v_isSharedCheck_1225_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1218_);
                            lean_dec(v___x_1207_);
                            v___x_1220_ = lean_box(0);
                            v_isShared_1221_ = v_isSharedCheck_1225_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1226_ = lean_ctor_get(v___x_1207_, 0);
                        v_isSharedCheck_1233_ = (!lean_is_exclusive(v___x_1207_)) as u8;
                        if v_isSharedCheck_1233_ == 0 {
                            v___x_1228_ = v___x_1207_;
                            v_isShared_1229_ = v_isSharedCheck_1233_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1226_);
                            lean_dec(v___x_1207_);
                            v___x_1228_ = lean_box(0);
                            v_isShared_1229_ = v_isSharedCheck_1233_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1212_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8_once), _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__8);
                v___x_1213_ = lean_string_append(v___x_1212_, v_a_1208_);
                lean_dec(v_a_1208_);
                if v_isShared_1211_ == 0 {
                    lean_ctor_set(v___x_1210_, 0, v___x_1213_);
                    v___x_1215_ = v___x_1210_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1213_);
                    v___x_1215_ = v_reuseFailAlloc_1216_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1215_;
            }
            3 => {
                if v_isShared_1221_ == 0 {
                    lean_ctor_set_tag(v___x_1220_, 0);
                    v___x_1223_ = v___x_1220_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
                    v___x_1223_ = v_reuseFailAlloc_1224_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1223_;
            }
            5 => {
                if v_isShared_1229_ == 0 {
                    v___x_1231_ = v___x_1228_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
                    v___x_1231_ = v_reuseFailAlloc_1232_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0(
    mut v_sz_1236_: usize,
    mut v_i_1237_: usize,
    mut v_bs_1238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1239_: u8 = 0;
    let mut v_v_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: usize = 0;
    let mut v___x_1245_: usize = 0;
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1239_ = lean_usize_dec_lt(v_i_1237_, v_sz_1236_);
                if v___x_1239_ == 0 {
                    return v_bs_1238_;
                } else {
                    v_v_1240_ = lean_array_uget(v_bs_1238_, v_i_1237_);
                    v___x_1241_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1242_ = lean_array_uset(v_bs_1238_, v_i_1237_, v___x_1241_);
                    v___x_1243_ = l_Lean_Lsp_instToJsonFileSystemWatcher_toJson(v_v_1240_);
                    v___x_1244_ = 1usize;
                    v___x_1245_ = lean_usize_add(v_i_1237_, v___x_1244_);
                    v___x_1246_ = lean_array_uset(v_bs_x27_1242_, v_i_1237_, v___x_1243_);
                    v_i_1237_ = v___x_1245_;
                    v_bs_1238_ = v___x_1246_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0___boxed(
    mut v_sz_1248_: *mut LeanObject,
    mut v_i_1249_: *mut LeanObject,
    mut v_bs_1250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1251_: usize = 0;
    let mut v_i_boxed_1252_: usize = 0;
    let mut v_res_1253_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1251_ = lean_unbox_usize(v_sz_1248_);
    lean_dec(v_sz_1248_);
    v_i_boxed_1252_ = lean_unbox_usize(v_i_1249_);
    lean_dec(v_i_1249_);
    v_res_1253_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0(v_sz_boxed_1251_, v_i_boxed_1252_, v_bs_1250_);
    return v_res_1253_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0(
    mut v_a_1254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_1255_: usize = 0;
    let mut v___x_1256_: usize = 0;
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    v_sz_1255_ = lean_array_size(v_a_1254_);
    v___x_1256_ = 0usize;
    v___x_1257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0_spec__0(v_sz_1255_, v___x_1256_, v_a_1254_);
    v___x_1258_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_1258_, 0, v___x_1257_);
    return v___x_1258_;
}
pub unsafe fn l_Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson(
    mut v_x_1259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    v___x_1260_ =
        l_Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson___closed__0;
    v___x_1261_ = l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesRegistrationOptions_toJson_spec__0(v_x_1259_);
    v___x_1262_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1262_, 0, v___x_1260_);
    lean_ctor_set(v___x_1262_, 1, v___x_1261_);
    v___x_1263_ = lean_box(0);
    v___x_1264_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1264_, 0, v___x_1262_);
    lean_ctor_set(v___x_1264_, 1, v___x_1263_);
    v___x_1265_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1265_, 0, v___x_1264_);
    lean_ctor_set(v___x_1265_, 1, v___x_1263_);
    v___x_1266_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2;
    v___x_1267_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(v___x_1265_, v___x_1266_);
    v___x_1268_ = l_Lean_Json_mkObj(v___x_1267_);
    lean_dec(v___x_1267_);
    return v___x_1268_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_ctorIdx(mut v_x_1271_: u8) -> *mut LeanObject {
    match v_x_1271_ {
        0 => {
            let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
            v___x_1272_ = lean_unsigned_to_nat(0);
            return v___x_1272_;
        }
        1 => {
            let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
            v___x_1273_ = lean_unsigned_to_nat(1);
            return v___x_1273_;
        }
        _ => {
            let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
            v___x_1274_ = lean_unsigned_to_nat(2);
            return v___x_1274_;
        }
    }
}
pub unsafe fn l_Lean_Lsp_FileChangeType_ctorIdx___boxed(
    mut v_x_1275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_1276_: u8 = 0;
    let mut v_res_1277_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_1276_ = (lean_unbox(v_x_1275_) as u8);
    v_res_1277_ = l_Lean_Lsp_FileChangeType_ctorIdx(v_x_boxed_1276_);
    return v_res_1277_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_toCtorIdx(mut v_x_1278_: u8) -> *mut LeanObject {
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    v___x_1279_ = l_Lean_Lsp_FileChangeType_ctorIdx(v_x_1278_);
    return v___x_1279_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_toCtorIdx___boxed(
    mut v_x_1280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_1281_: u8 = 0;
    let mut v_res_1282_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1281_ = (lean_unbox(v_x_1280_) as u8);
    v_res_1282_ = l_Lean_Lsp_FileChangeType_toCtorIdx(v_x_4__boxed_1281_);
    return v_res_1282_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_ctorElim___redArg(
    mut v_k_1283_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_1283_);
    return v_k_1283_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_ctorElim___redArg___boxed(
    mut v_k_1284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1285_: *mut LeanObject = core::ptr::null_mut();
    v_res_1285_ = l_Lean_Lsp_FileChangeType_ctorElim___redArg(v_k_1284_);
    lean_dec(v_k_1284_);
    return v_res_1285_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_ctorElim(
    mut v_motive_1286_: *mut LeanObject,
    mut v_ctorIdx_1287_: *mut LeanObject,
    mut v_t_1288_: u8,
    mut v_h_1289_: *mut LeanObject,
    mut v_k_1290_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_1290_);
    return v_k_1290_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_ctorElim___boxed(
    mut v_motive_1291_: *mut LeanObject,
    mut v_ctorIdx_1292_: *mut LeanObject,
    mut v_t_1293_: *mut LeanObject,
    mut v_h_1294_: *mut LeanObject,
    mut v_k_1295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1296_: u8 = 0;
    let mut v_res_1297_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1296_ = (lean_unbox(v_t_1293_) as u8);
    v_res_1297_ = l_Lean_Lsp_FileChangeType_ctorElim(
        v_motive_1291_,
        v_ctorIdx_1292_,
        v_t_boxed_1296_,
        v_h_1294_,
        v_k_1295_,
    );
    lean_dec(v_k_1295_);
    lean_dec(v_ctorIdx_1292_);
    return v_res_1297_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Created_elim___redArg(
    mut v_Created_1298_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_Created_1298_);
    return v_Created_1298_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Created_elim___redArg___boxed(
    mut v_Created_1299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1300_: *mut LeanObject = core::ptr::null_mut();
    v_res_1300_ = l_Lean_Lsp_FileChangeType_Created_elim___redArg(v_Created_1299_);
    lean_dec(v_Created_1299_);
    return v_res_1300_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Created_elim(
    mut v_motive_1301_: *mut LeanObject,
    mut v_t_1302_: u8,
    mut v_h_1303_: *mut LeanObject,
    mut v_Created_1304_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_Created_1304_);
    return v_Created_1304_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Created_elim___boxed(
    mut v_motive_1305_: *mut LeanObject,
    mut v_t_1306_: *mut LeanObject,
    mut v_h_1307_: *mut LeanObject,
    mut v_Created_1308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1309_: u8 = 0;
    let mut v_res_1310_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1309_ = (lean_unbox(v_t_1306_) as u8);
    v_res_1310_ = l_Lean_Lsp_FileChangeType_Created_elim(
        v_motive_1305_,
        v_t_boxed_1309_,
        v_h_1307_,
        v_Created_1308_,
    );
    lean_dec(v_Created_1308_);
    return v_res_1310_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Changed_elim___redArg(
    mut v_Changed_1311_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_Changed_1311_);
    return v_Changed_1311_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Changed_elim___redArg___boxed(
    mut v_Changed_1312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1313_: *mut LeanObject = core::ptr::null_mut();
    v_res_1313_ = l_Lean_Lsp_FileChangeType_Changed_elim___redArg(v_Changed_1312_);
    lean_dec(v_Changed_1312_);
    return v_res_1313_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Changed_elim(
    mut v_motive_1314_: *mut LeanObject,
    mut v_t_1315_: u8,
    mut v_h_1316_: *mut LeanObject,
    mut v_Changed_1317_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_Changed_1317_);
    return v_Changed_1317_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Changed_elim___boxed(
    mut v_motive_1318_: *mut LeanObject,
    mut v_t_1319_: *mut LeanObject,
    mut v_h_1320_: *mut LeanObject,
    mut v_Changed_1321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1322_: u8 = 0;
    let mut v_res_1323_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1322_ = (lean_unbox(v_t_1319_) as u8);
    v_res_1323_ = l_Lean_Lsp_FileChangeType_Changed_elim(
        v_motive_1318_,
        v_t_boxed_1322_,
        v_h_1320_,
        v_Changed_1321_,
    );
    lean_dec(v_Changed_1321_);
    return v_res_1323_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Deleted_elim___redArg(
    mut v_Deleted_1324_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_Deleted_1324_);
    return v_Deleted_1324_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Deleted_elim___redArg___boxed(
    mut v_Deleted_1325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1326_: *mut LeanObject = core::ptr::null_mut();
    v_res_1326_ = l_Lean_Lsp_FileChangeType_Deleted_elim___redArg(v_Deleted_1325_);
    lean_dec(v_Deleted_1325_);
    return v_res_1326_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Deleted_elim(
    mut v_motive_1327_: *mut LeanObject,
    mut v_t_1328_: u8,
    mut v_h_1329_: *mut LeanObject,
    mut v_Deleted_1330_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_Deleted_1330_);
    return v_Deleted_1330_;
}
pub unsafe fn l_Lean_Lsp_FileChangeType_Deleted_elim___boxed(
    mut v_motive_1331_: *mut LeanObject,
    mut v_t_1332_: *mut LeanObject,
    mut v_h_1333_: *mut LeanObject,
    mut v_Deleted_1334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1335_: u8 = 0;
    let mut v_res_1336_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1335_ = (lean_unbox(v_t_1332_) as u8);
    v_res_1336_ = l_Lean_Lsp_FileChangeType_Deleted_elim(
        v_motive_1331_,
        v_t_boxed_1335_,
        v_h_1333_,
        v_Deleted_1334_,
    );
    lean_dec(v_Deleted_1334_);
    return v_res_1336_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonFileChangeType___lam__0(
    mut v_j_1347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1352_: u8 = 0;
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1356_: u8 = 0;
    let mut v_a_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1360_: u8 = 0;
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: u8 = 0;
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: u8 = 0;
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: u8 = 0;
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1377_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_j_1347_);
                v___x_1348_ = l_Lean_Json_getNat_x3f(v_j_1347_);
                if lean_obj_tag(v___x_1348_) == 0 {
                    lean_dec(v_j_1347_);
                    v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
                    v_isSharedCheck_1356_ = (!lean_is_exclusive(v___x_1348_)) as u8;
                    if v_isSharedCheck_1356_ == 0 {
                        v___x_1351_ = v___x_1348_;
                        v_isShared_1352_ = v_isSharedCheck_1356_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1349_);
                        lean_dec(v___x_1348_);
                        v___x_1351_ = lean_box(0);
                        v_isShared_1352_ = v_isSharedCheck_1356_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1357_ = lean_ctor_get(v___x_1348_, 0);
                    v_isSharedCheck_1377_ = (!lean_is_exclusive(v___x_1348_)) as u8;
                    if v_isSharedCheck_1377_ == 0 {
                        v___x_1359_ = v___x_1348_;
                        v_isShared_1360_ = v_isSharedCheck_1377_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1357_);
                        lean_dec(v___x_1348_);
                        v___x_1359_ = lean_box(0);
                        v_isShared_1360_ = v_isSharedCheck_1377_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1352_ == 0 {
                    v___x_1354_ = v___x_1351_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
                    v___x_1354_ = v_reuseFailAlloc_1355_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1354_;
            }
            3 => {
                v___x_1361_ = lean_unsigned_to_nat(1);
                v___x_1362_ = lean_nat_dec_eq(v_a_1357_, v___x_1361_);
                if v___x_1362_ == 0 {
                    v___x_1363_ = lean_unsigned_to_nat(2);
                    v___x_1364_ = lean_nat_dec_eq(v_a_1357_, v___x_1363_);
                    if v___x_1364_ == 0 {
                        v___x_1365_ = lean_unsigned_to_nat(3);
                        v___x_1366_ = lean_nat_dec_eq(v_a_1357_, v___x_1365_);
                        lean_dec(v_a_1357_);
                        if v___x_1366_ == 0 {
                            v___x_1367_ =
                                l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__0;
                            v___x_1368_ = lean_unsigned_to_nat(80);
                            v___x_1369_ = l_Lean_Json_pretty(v_j_1347_, v___x_1368_);
                            v___x_1370_ = lean_string_append(v___x_1367_, v___x_1369_);
                            lean_dec_ref(v___x_1369_);
                            if v_isShared_1360_ == 0 {
                                lean_ctor_set_tag(v___x_1359_, 0);
                                lean_ctor_set(v___x_1359_, 0, v___x_1370_);
                                v___x_1372_ = v___x_1359_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
                                v___x_1372_ = v_reuseFailAlloc_1373_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_1359_);
                            lean_dec(v_j_1347_);
                            v___x_1374_ =
                                l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__1;
                            return v___x_1374_;
                        }
                    } else {
                        lean_del_object(v___x_1359_);
                        lean_dec(v_a_1357_);
                        lean_dec(v_j_1347_);
                        v___x_1375_ = l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__2;
                        return v___x_1375_;
                    }
                } else {
                    lean_del_object(v___x_1359_);
                    lean_dec(v_a_1357_);
                    lean_dec(v_j_1347_);
                    v___x_1376_ = l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__3;
                    return v___x_1376_;
                }
            }
            4 => {
                return v___x_1372_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0() -> *mut LeanObject {
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    v___x_1380_ = lean_unsigned_to_nat(1);
    v___x_1381_ = l_Lean_JsonNumber_fromNat(v___x_1380_);
    return v___x_1381_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    v___x_1382_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0_once),
        _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__0,
    );
    v___x_1383_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_1383_, 0, v___x_1382_);
    return v___x_1383_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2() -> *mut LeanObject {
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    v___x_1384_ = lean_unsigned_to_nat(2);
    v___x_1385_ = l_Lean_JsonNumber_fromNat(v___x_1384_);
    return v___x_1385_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    v___x_1386_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2_once),
        _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__2,
    );
    v___x_1387_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_1387_, 0, v___x_1386_);
    return v___x_1387_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4() -> *mut LeanObject {
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    v___x_1388_ = lean_unsigned_to_nat(3);
    v___x_1389_ = l_Lean_JsonNumber_fromNat(v___x_1388_);
    return v___x_1389_;
}
pub unsafe fn _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5() -> *mut LeanObject {
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    v___x_1390_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4_once),
        _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__4,
    );
    v___x_1391_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_1391_, 0, v___x_1390_);
    return v___x_1391_;
}
pub unsafe fn l_Lean_Lsp_instToJsonFileChangeType___lam__0(mut v_x_1392_: u8) -> *mut LeanObject {
    match v_x_1392_ {
        0 => {
            let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
            v___x_1393_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1),
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1_once
                ),
                _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1,
            );
            return v___x_1393_;
        }
        1 => {
            let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
            v___x_1394_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3),
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3_once
                ),
                _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3,
            );
            return v___x_1394_;
        }
        _ => {
            let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
            v___x_1395_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5),
                core::ptr::addr_of_mut!(
                    l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5_once
                ),
                _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5,
            );
            return v___x_1395_;
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonFileChangeType___lam__0___boxed(
    mut v_x_1396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_102__boxed_1397_: u8 = 0;
    let mut v_res_1398_: *mut LeanObject = core::ptr::null_mut();
    v_x_102__boxed_1397_ = (lean_unbox(v_x_1396_) as u8);
    v_res_1398_ = l_Lean_Lsp_instToJsonFileChangeType___lam__0(v_x_102__boxed_1397_);
    return v_res_1398_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0(
    mut v_j_1401_: *mut LeanObject,
    mut v_k_1402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1408_: u8 = 0;
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1412_: u8 = 0;
    let mut v_a_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1416_: u8 = 0;
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: u8 = 0;
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: u8 = 0;
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: u8 = 0;
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1433_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1403_ = l_Lean_Json_getObjValD(v_j_1401_, v_k_1402_);
                lean_inc(v___x_1403_);
                v___x_1404_ = l_Lean_Json_getNat_x3f(v___x_1403_);
                if lean_obj_tag(v___x_1404_) == 0 {
                    lean_dec(v___x_1403_);
                    v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
                    v_isSharedCheck_1412_ = (!lean_is_exclusive(v___x_1404_)) as u8;
                    if v_isSharedCheck_1412_ == 0 {
                        v___x_1407_ = v___x_1404_;
                        v_isShared_1408_ = v_isSharedCheck_1412_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1405_);
                        lean_dec(v___x_1404_);
                        v___x_1407_ = lean_box(0);
                        v_isShared_1408_ = v_isSharedCheck_1412_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1413_ = lean_ctor_get(v___x_1404_, 0);
                    v_isSharedCheck_1433_ = (!lean_is_exclusive(v___x_1404_)) as u8;
                    if v_isSharedCheck_1433_ == 0 {
                        v___x_1415_ = v___x_1404_;
                        v_isShared_1416_ = v_isSharedCheck_1433_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1413_);
                        lean_dec(v___x_1404_);
                        v___x_1415_ = lean_box(0);
                        v_isShared_1416_ = v_isSharedCheck_1433_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1408_ == 0 {
                    v___x_1410_ = v___x_1407_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
                    v___x_1410_ = v_reuseFailAlloc_1411_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1410_;
            }
            3 => {
                v___x_1417_ = lean_unsigned_to_nat(1);
                v___x_1418_ = lean_nat_dec_eq(v_a_1413_, v___x_1417_);
                if v___x_1418_ == 0 {
                    v___x_1419_ = lean_unsigned_to_nat(2);
                    v___x_1420_ = lean_nat_dec_eq(v_a_1413_, v___x_1419_);
                    if v___x_1420_ == 0 {
                        v___x_1421_ = lean_unsigned_to_nat(3);
                        v___x_1422_ = lean_nat_dec_eq(v_a_1413_, v___x_1421_);
                        lean_dec(v_a_1413_);
                        if v___x_1422_ == 0 {
                            v___x_1423_ =
                                l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__0;
                            v___x_1424_ = lean_unsigned_to_nat(80);
                            v___x_1425_ = l_Lean_Json_pretty(v___x_1403_, v___x_1424_);
                            v___x_1426_ = lean_string_append(v___x_1423_, v___x_1425_);
                            lean_dec_ref(v___x_1425_);
                            if v_isShared_1416_ == 0 {
                                lean_ctor_set_tag(v___x_1415_, 0);
                                lean_ctor_set(v___x_1415_, 0, v___x_1426_);
                                v___x_1428_ = v___x_1415_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
                                v___x_1428_ = v_reuseFailAlloc_1429_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_1415_);
                            lean_dec(v___x_1403_);
                            v___x_1430_ =
                                l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__1;
                            return v___x_1430_;
                        }
                    } else {
                        lean_del_object(v___x_1415_);
                        lean_dec(v_a_1413_);
                        lean_dec(v___x_1403_);
                        v___x_1431_ = l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__2;
                        return v___x_1431_;
                    }
                } else {
                    lean_del_object(v___x_1415_);
                    lean_dec(v_a_1413_);
                    lean_dec(v___x_1403_);
                    v___x_1432_ = l_Lean_Lsp_instFromJsonFileChangeType___lam__0___closed__3;
                    return v___x_1432_;
                }
            }
            4 => {
                return v___x_1428_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0___boxed(
    mut v_j_1434_: *mut LeanObject,
    mut v_k_1435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1436_: *mut LeanObject = core::ptr::null_mut();
    v_res_1436_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0(
            v_j_1434_, v_k_1435_,
        );
    lean_dec_ref(v_k_1435_);
    return v_res_1436_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2() -> *mut LeanObject {
    let mut v___x_1442_: u8 = 0;
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    v___x_1442_ = 1;
    v___x_1443_ = l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__1;
    v___x_1444_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1443_, v___x_1442_);
    return v___x_1444_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3() -> *mut LeanObject {
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    v___x_1445_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5;
    v___x_1446_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2_once),
        _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__2,
    );
    v___x_1447_ = lean_string_append(v___x_1446_, v___x_1445_);
    return v___x_1447_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4() -> *mut LeanObject {
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    v___x_1448_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8_once),
        _init_l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__8,
    );
    v___x_1449_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3,
    );
    v___x_1450_ = lean_string_append(v___x_1449_, v___x_1448_);
    return v___x_1450_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5() -> *mut LeanObject {
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    v___x_1451_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10;
    v___x_1452_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__4,
    );
    v___x_1453_ = lean_string_append(v___x_1452_, v___x_1451_);
    return v___x_1453_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8() -> *mut LeanObject {
    let mut v___x_1457_: u8 = 0;
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    v___x_1457_ = 1;
    v___x_1458_ = l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__7;
    v___x_1459_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1458_, v___x_1457_);
    return v___x_1459_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9() -> *mut LeanObject {
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    v___x_1460_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8_once),
        _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__8,
    );
    v___x_1461_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3_once),
        _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__3,
    );
    v___x_1462_ = lean_string_append(v___x_1461_, v___x_1460_);
    return v___x_1462_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10() -> *mut LeanObject {
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    v___x_1463_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10;
    v___x_1464_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9_once),
        _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__9,
    );
    v___x_1465_ = lean_string_append(v___x_1464_, v___x_1463_);
    return v___x_1465_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonFileEvent_fromJson(
    mut v_json_1466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1472_: u8 = 0;
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1478_: u8 = 0;
    let mut v_a_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1482_: u8 = 0;
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1486_: u8 = 0;
    let mut v_a_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1493_: u8 = 0;
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1499_: u8 = 0;
    let mut v_a_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1503_: u8 = 0;
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1507_: u8 = 0;
    let mut v_a_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1511_: u8 = 0;
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: u8 = 0;
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1467_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0;
                lean_inc(v_json_1466_);
                v___x_1468_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceFolder_fromJson_spec__0(v_json_1466_, v___x_1467_);
                if lean_obj_tag(v___x_1468_) == 0 {
                    lean_dec(v_json_1466_);
                    v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
                    v_isSharedCheck_1478_ = (!lean_is_exclusive(v___x_1468_)) as u8;
                    if v_isSharedCheck_1478_ == 0 {
                        v___x_1471_ = v___x_1468_;
                        v_isShared_1472_ = v_isSharedCheck_1478_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1469_);
                        lean_dec(v___x_1468_);
                        v___x_1471_ = lean_box(0);
                        v_isShared_1472_ = v_isSharedCheck_1478_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_1468_) == 0 {
                        lean_dec(v_json_1466_);
                        v_a_1479_ = lean_ctor_get(v___x_1468_, 0);
                        v_isSharedCheck_1486_ = (!lean_is_exclusive(v___x_1468_)) as u8;
                        if v_isSharedCheck_1486_ == 0 {
                            v___x_1481_ = v___x_1468_;
                            v_isShared_1482_ = v_isSharedCheck_1486_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1479_);
                            lean_dec(v___x_1468_);
                            v___x_1481_ = lean_box(0);
                            v_isShared_1482_ = v_isSharedCheck_1486_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1487_ = lean_ctor_get(v___x_1468_, 0);
                        lean_inc(v_a_1487_);
                        lean_dec_ref_known(v___x_1468_, 1);
                        v___x_1488_ = l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6;
                        v___x_1489_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonFileEvent_fromJson_spec__0(v_json_1466_, v___x_1488_);
                        if lean_obj_tag(v___x_1489_) == 0 {
                            lean_dec(v_a_1487_);
                            v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
                            v_isSharedCheck_1499_ = (!lean_is_exclusive(v___x_1489_)) as u8;
                            if v_isSharedCheck_1499_ == 0 {
                                v___x_1492_ = v___x_1489_;
                                v_isShared_1493_ = v_isSharedCheck_1499_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_1490_);
                                lean_dec(v___x_1489_);
                                v___x_1492_ = lean_box(0);
                                v_isShared_1493_ = v_isSharedCheck_1499_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_1489_) == 0 {
                                lean_dec(v_a_1487_);
                                v_a_1500_ = lean_ctor_get(v___x_1489_, 0);
                                v_isSharedCheck_1507_ = (!lean_is_exclusive(v___x_1489_)) as u8;
                                if v_isSharedCheck_1507_ == 0 {
                                    v___x_1502_ = v___x_1489_;
                                    v_isShared_1503_ = v_isSharedCheck_1507_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_1500_);
                                    lean_dec(v___x_1489_);
                                    v___x_1502_ = lean_box(0);
                                    v_isShared_1503_ = v_isSharedCheck_1507_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_1508_ = lean_ctor_get(v___x_1489_, 0);
                                v_isSharedCheck_1517_ = (!lean_is_exclusive(v___x_1489_)) as u8;
                                if v_isSharedCheck_1517_ == 0 {
                                    v___x_1510_ = v___x_1489_;
                                    v_isShared_1511_ = v_isSharedCheck_1517_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_1508_);
                                    lean_dec(v___x_1489_);
                                    v___x_1510_ = lean_box(0);
                                    v_isShared_1511_ = v_isSharedCheck_1517_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1473_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__5,
                );
                v___x_1474_ = lean_string_append(v___x_1473_, v_a_1469_);
                lean_dec(v_a_1469_);
                if v_isShared_1472_ == 0 {
                    lean_ctor_set(v___x_1471_, 0, v___x_1474_);
                    v___x_1476_ = v___x_1471_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1474_);
                    v___x_1476_ = v_reuseFailAlloc_1477_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1476_;
            }
            3 => {
                if v_isShared_1482_ == 0 {
                    lean_ctor_set_tag(v___x_1481_, 0);
                    v___x_1484_ = v___x_1481_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
                    v___x_1484_ = v_reuseFailAlloc_1485_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1484_;
            }
            5 => {
                v___x_1494_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__10,
                );
                v___x_1495_ = lean_string_append(v___x_1494_, v_a_1490_);
                lean_dec(v_a_1490_);
                if v_isShared_1493_ == 0 {
                    lean_ctor_set(v___x_1492_, 0, v___x_1495_);
                    v___x_1497_ = v___x_1492_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1495_);
                    v___x_1497_ = v_reuseFailAlloc_1498_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1497_;
            }
            7 => {
                if v_isShared_1503_ == 0 {
                    lean_ctor_set_tag(v___x_1502_, 0);
                    v___x_1505_ = v___x_1502_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
                    v___x_1505_ = v_reuseFailAlloc_1506_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1505_;
            }
            9 => {
                v___x_1512_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_1512_, 0, v_a_1487_);
                v___x_1513_ = (lean_unbox(v_a_1508_) as u8);
                lean_dec(v_a_1508_);
                lean_ctor_set_uint8(
                    v___x_1512_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1513_,
                );
                if v_isShared_1511_ == 0 {
                    lean_ctor_set(v___x_1510_, 0, v___x_1512_);
                    v___x_1515_ = v___x_1510_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1512_);
                    v___x_1515_ = v_reuseFailAlloc_1516_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1515_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonFileEvent_toJson(
    mut v_x_1520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_uri_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1522_: u8 = 0;
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_uri_1521_ = lean_ctor_get(v_x_1520_, 0);
                v_type_1522_ = lean_ctor_get_uint8(
                    v_x_1520_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v___x_1523_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__0;
                lean_inc_ref(v_uri_1521_);
                v___x_1524_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1524_, 0, v_uri_1521_);
                v___x_1525_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1525_, 0, v___x_1523_);
                lean_ctor_set(v___x_1525_, 1, v___x_1524_);
                v___x_1526_ = lean_box(0);
                v___x_1527_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1527_, 0, v___x_1525_);
                lean_ctor_set(v___x_1527_, 1, v___x_1526_);
                v___x_1528_ = l_Lean_Lsp_instFromJsonFileEvent_fromJson___closed__6;
                match v_type_1522_ {
                    0 => {
                        v___x_1538_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1_once
                            ),
                            _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__1,
                        );
                        v___y_1530_ = v___x_1538_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_1539_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3_once
                            ),
                            _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__3,
                        );
                        v___y_1530_ = v___x_1539_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_1540_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5_once
                            ),
                            _init_l_Lean_Lsp_instToJsonFileChangeType___lam__0___closed__5,
                        );
                        v___y_1530_ = v___x_1540_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v___y_1530_);
                v___x_1531_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1531_, 0, v___x_1528_);
                lean_ctor_set(v___x_1531_, 1, v___y_1530_);
                v___x_1532_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1532_, 0, v___x_1531_);
                lean_ctor_set(v___x_1532_, 1, v___x_1526_);
                v___x_1533_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1533_, 0, v___x_1532_);
                lean_ctor_set(v___x_1533_, 1, v___x_1526_);
                v___x_1534_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1534_, 0, v___x_1527_);
                lean_ctor_set(v___x_1534_, 1, v___x_1533_);
                v___x_1535_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2;
                v___x_1536_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(v___x_1534_, v___x_1535_);
                v___x_1537_ = l_Lean_Json_mkObj(v___x_1536_);
                lean_dec(v___x_1536_);
                return v___x_1537_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonFileEvent_toJson___boxed(
    mut v_x_1541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1542_: *mut LeanObject = core::ptr::null_mut();
    v_res_1542_ = l_Lean_Lsp_instToJsonFileEvent_toJson(v_x_1541_);
    lean_dec_ref(v_x_1541_);
    return v_res_1542_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1(
    mut v_sz_1545_: usize,
    mut v_i_1546_: usize,
    mut v_bs_1547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1548_: u8 = 0;
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1555_: u8 = 0;
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1559_: u8 = 0;
    let mut v_a_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: usize = 0;
    let mut v___x_1564_: usize = 0;
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1548_ = lean_usize_dec_lt(v_i_1546_, v_sz_1545_);
                if v___x_1548_ == 0 {
                    v___x_1549_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1549_, 0, v_bs_1547_);
                    return v___x_1549_;
                } else {
                    v_v_1550_ = lean_array_uget_borrowed(v_bs_1547_, v_i_1546_);
                    lean_inc(v_v_1550_);
                    v___x_1551_ = l_Lean_Lsp_instFromJsonFileEvent_fromJson(v_v_1550_);
                    if lean_obj_tag(v___x_1551_) == 0 {
                        lean_dec_ref(v_bs_1547_);
                        v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
                        v_isSharedCheck_1559_ = (!lean_is_exclusive(v___x_1551_)) as u8;
                        if v_isSharedCheck_1559_ == 0 {
                            v___x_1554_ = v___x_1551_;
                            v_isShared_1555_ = v_isSharedCheck_1559_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1552_);
                            lean_dec(v___x_1551_);
                            v___x_1554_ = lean_box(0);
                            v_isShared_1555_ = v_isSharedCheck_1559_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1560_ = lean_ctor_get(v___x_1551_, 0);
                        lean_inc(v_a_1560_);
                        lean_dec_ref_known(v___x_1551_, 1);
                        v___x_1561_ = lean_unsigned_to_nat(0);
                        v_bs_x27_1562_ = lean_array_uset(v_bs_1547_, v_i_1546_, v___x_1561_);
                        v___x_1563_ = 1usize;
                        v___x_1564_ = lean_usize_add(v_i_1546_, v___x_1563_);
                        v___x_1565_ = lean_array_uset(v_bs_x27_1562_, v_i_1546_, v_a_1560_);
                        v_i_1546_ = v___x_1564_;
                        v_bs_1547_ = v___x_1565_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1555_ == 0 {
                    v___x_1557_ = v___x_1554_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
                    v___x_1557_ = v_reuseFailAlloc_1558_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1557_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1___boxed(
    mut v_sz_1567_: *mut LeanObject,
    mut v_i_1568_: *mut LeanObject,
    mut v_bs_1569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1570_: usize = 0;
    let mut v_i_boxed_1571_: usize = 0;
    let mut v_res_1572_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1570_ = lean_unbox_usize(v_sz_1567_);
    lean_dec(v_sz_1567_);
    v_i_boxed_1571_ = lean_unbox_usize(v_i_1568_);
    lean_dec(v_i_1568_);
    v_res_1572_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_1570_, v_i_boxed_1571_, v_bs_1569_);
    return v_res_1572_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0(
    mut v_x_1573_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1573_) == 4 {
        let mut v_elems_1574_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_1575_: usize = 0;
        let mut v___x_1576_: usize = 0;
        let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
        v_elems_1574_ = lean_ctor_get(v_x_1573_, 0);
        lean_inc_ref(v_elems_1574_);
        lean_dec_ref_known(v_x_1573_, 1);
        v_sz_1575_ = lean_array_size(v_elems_1574_);
        v___x_1576_ = 0usize;
        v___x_1577_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0_spec__1(v_sz_1575_, v___x_1576_, v_elems_1574_);
        return v___x_1577_;
    } else {
        let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
        v___x_1578_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__0;
        v___x_1579_ = lean_unsigned_to_nat(80);
        v___x_1580_ = l_Lean_Json_pretty(v_x_1573_, v___x_1579_);
        v___x_1581_ = lean_string_append(v___x_1578_, v___x_1580_);
        lean_dec_ref(v___x_1580_);
        v___x_1582_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesRegistrationOptions_fromJson_spec__0_spec__0___closed__1;
        v___x_1583_ = lean_string_append(v___x_1581_, v___x_1582_);
        v___x_1584_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1584_, 0, v___x_1583_);
        return v___x_1584_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0(
    mut v_j_1585_: *mut LeanObject,
    mut v_k_1586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    v___x_1587_ = l_Lean_Json_getObjValD(v_j_1585_, v_k_1586_);
    v___x_1588_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0_spec__0(v___x_1587_);
    return v___x_1588_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0___boxed(
    mut v_j_1589_: *mut LeanObject,
    mut v_k_1590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1591_: *mut LeanObject = core::ptr::null_mut();
    v_res_1591_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0(v_j_1589_, v_k_1590_);
    lean_dec_ref(v_k_1590_);
    return v_res_1591_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3()
-> *mut LeanObject {
    let mut v___x_1598_: u8 = 0;
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    v___x_1598_ = 1;
    v___x_1599_ = l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__2;
    v___x_1600_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1599_, v___x_1598_);
    return v___x_1600_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4()
-> *mut LeanObject {
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    v___x_1601_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__5;
    v___x_1602_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__3,
    );
    v___x_1603_ = lean_string_append(v___x_1602_, v___x_1601_);
    return v___x_1603_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6()
-> *mut LeanObject {
    let mut v___x_1606_: u8 = 0;
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    v___x_1606_ = 1;
    v___x_1607_ = l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__5;
    v___x_1608_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1607_, v___x_1606_);
    return v___x_1608_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7()
-> *mut LeanObject {
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    v___x_1609_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__6,
    );
    v___x_1610_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__4,
    );
    v___x_1611_ = lean_string_append(v___x_1610_, v___x_1609_);
    return v___x_1611_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8()
-> *mut LeanObject {
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    v___x_1612_ = l_Lean_Lsp_instFromJsonWorkspaceFolder_fromJson___closed__10;
    v___x_1613_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7_once
        ),
        _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__7,
    );
    v___x_1614_ = lean_string_append(v___x_1613_, v___x_1612_);
    return v___x_1614_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson(
    mut v_json_1615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1621_: u8 = 0;
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1627_: u8 = 0;
    let mut v_a_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1631_: u8 = 0;
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1635_: u8 = 0;
    let mut v_a_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1639_: u8 = 0;
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1643_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1616_ =
                    l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0;
                v___x_1617_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson_spec__0(v_json_1615_, v___x_1616_);
                if lean_obj_tag(v___x_1617_) == 0 {
                    v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
                    v_isSharedCheck_1627_ = (!lean_is_exclusive(v___x_1617_)) as u8;
                    if v_isSharedCheck_1627_ == 0 {
                        v___x_1620_ = v___x_1617_;
                        v_isShared_1621_ = v_isSharedCheck_1627_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1618_);
                        lean_dec(v___x_1617_);
                        v___x_1620_ = lean_box(0);
                        v_isShared_1621_ = v_isSharedCheck_1627_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_1617_) == 0 {
                        v_a_1628_ = lean_ctor_get(v___x_1617_, 0);
                        v_isSharedCheck_1635_ = (!lean_is_exclusive(v___x_1617_)) as u8;
                        if v_isSharedCheck_1635_ == 0 {
                            v___x_1630_ = v___x_1617_;
                            v_isShared_1631_ = v_isSharedCheck_1635_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1628_);
                            lean_dec(v___x_1617_);
                            v___x_1630_ = lean_box(0);
                            v_isShared_1631_ = v_isSharedCheck_1635_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1636_ = lean_ctor_get(v___x_1617_, 0);
                        v_isSharedCheck_1643_ = (!lean_is_exclusive(v___x_1617_)) as u8;
                        if v_isSharedCheck_1643_ == 0 {
                            v___x_1638_ = v___x_1617_;
                            v_isShared_1639_ = v_isSharedCheck_1643_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1636_);
                            lean_dec(v___x_1617_);
                            v___x_1638_ = lean_box(0);
                            v_isShared_1639_ = v_isSharedCheck_1643_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1622_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8), core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8_once), _init_l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__8);
                v___x_1623_ = lean_string_append(v___x_1622_, v_a_1618_);
                lean_dec(v_a_1618_);
                if v_isShared_1621_ == 0 {
                    lean_ctor_set(v___x_1620_, 0, v___x_1623_);
                    v___x_1625_ = v___x_1620_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1623_);
                    v___x_1625_ = v_reuseFailAlloc_1626_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1625_;
            }
            3 => {
                if v_isShared_1631_ == 0 {
                    lean_ctor_set_tag(v___x_1630_, 0);
                    v___x_1633_ = v___x_1630_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
                    v___x_1633_ = v_reuseFailAlloc_1634_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1633_;
            }
            5 => {
                if v_isShared_1639_ == 0 {
                    v___x_1641_ = v___x_1638_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
                    v___x_1641_ = v_reuseFailAlloc_1642_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1641_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0(
    mut v_sz_1646_: usize,
    mut v_i_1647_: usize,
    mut v_bs_1648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1649_: u8 = 0;
    let mut v_v_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: usize = 0;
    let mut v___x_1655_: usize = 0;
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1649_ = lean_usize_dec_lt(v_i_1647_, v_sz_1646_);
                if v___x_1649_ == 0 {
                    return v_bs_1648_;
                } else {
                    v_v_1650_ = lean_array_uget(v_bs_1648_, v_i_1647_);
                    v___x_1651_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1652_ = lean_array_uset(v_bs_1648_, v_i_1647_, v___x_1651_);
                    v___x_1653_ = l_Lean_Lsp_instToJsonFileEvent_toJson(v_v_1650_);
                    lean_dec(v_v_1650_);
                    v___x_1654_ = 1usize;
                    v___x_1655_ = lean_usize_add(v_i_1647_, v___x_1654_);
                    v___x_1656_ = lean_array_uset(v_bs_x27_1652_, v_i_1647_, v___x_1653_);
                    v_i_1647_ = v___x_1655_;
                    v_bs_1648_ = v___x_1656_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0___boxed(
    mut v_sz_1658_: *mut LeanObject,
    mut v_i_1659_: *mut LeanObject,
    mut v_bs_1660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1661_: usize = 0;
    let mut v_i_boxed_1662_: usize = 0;
    let mut v_res_1663_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1661_ = lean_unbox_usize(v_sz_1658_);
    lean_dec(v_sz_1658_);
    v_i_boxed_1662_ = lean_unbox_usize(v_i_1659_);
    lean_dec(v_i_1659_);
    v_res_1663_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0(v_sz_boxed_1661_, v_i_boxed_1662_, v_bs_1660_);
    return v_res_1663_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0(
    mut v_a_1664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_1665_: usize = 0;
    let mut v___x_1666_: usize = 0;
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    v_sz_1665_ = lean_array_size(v_a_1664_);
    v___x_1666_ = 0usize;
    v___x_1667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0_spec__0(v_sz_1665_, v___x_1666_, v_a_1664_);
    v___x_1668_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_1668_, 0, v___x_1667_);
    return v___x_1668_;
}
pub unsafe fn l_Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson(
    mut v_x_1669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    v___x_1670_ = l_Lean_Lsp_instFromJsonDidChangeWatchedFilesParams_fromJson___closed__0;
    v___x_1671_ =
        l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeWatchedFilesParams_toJson_spec__0(
            v_x_1669_,
        );
    v___x_1672_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1672_, 0, v___x_1670_);
    lean_ctor_set(v___x_1672_, 1, v___x_1671_);
    v___x_1673_ = lean_box(0);
    v___x_1674_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1674_, 0, v___x_1672_);
    lean_ctor_set(v___x_1674_, 1, v___x_1673_);
    v___x_1675_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1675_, 0, v___x_1674_);
    lean_ctor_set(v___x_1675_, 1, v___x_1673_);
    v___x_1676_ = l_Lean_Lsp_instToJsonWorkspaceFolder_toJson___closed__2;
    v___x_1677_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonWorkspaceFolder_toJson_spec__0(v___x_1675_, v___x_1676_);
    v___x_1678_ = l_Lean_Json_mkObj(v___x_1677_);
    lean_dec(v___x_1677_);
    return v___x_1678_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Lsp_Workspace(builtin: u8) -> *mut LeanObject {
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
    l_Lean_Lsp_FileSystemWatcher_create = _init_l_Lean_Lsp_FileSystemWatcher_create();
    lean_mark_persistent(l_Lean_Lsp_FileSystemWatcher_create);
    l_Lean_Lsp_FileSystemWatcher_change = _init_l_Lean_Lsp_FileSystemWatcher_change();
    lean_mark_persistent(l_Lean_Lsp_FileSystemWatcher_change);
    l_Lean_Lsp_FileSystemWatcher_delete = _init_l_Lean_Lsp_FileSystemWatcher_delete();
    lean_mark_persistent(l_Lean_Lsp_FileSystemWatcher_delete);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Lsp_Workspace(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Lsp_Workspace(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Lean_Data_Lsp_Workspace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Lsp_Workspace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_Lsp_Workspace(builtin);
}
