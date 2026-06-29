// Lean compiler output
// Module: LeanChecker
// Imports: Init Init Lean.CoreM Lean.Replay Lake.Load.Manifest
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_array_size, lean_array_uget_borrowed, lean_io_as_task, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_st_mk_ref, lean_st_ref_get,
    lean_string_append, lean_string_memcmp, lean_string_utf8_byte_size, lean_task_get_own,
    lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::{l_List_elem___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Name_capitalize, l_String_toName};
use crate::r#gen::Init::Prelude::{
    l_List_lengthTR___redArg, l_instBEqOfDecidableEq___redArg___lam__0___boxed,
    l_instDecidableEqString___boxed,
};
use crate::r#gen::Init::System::IO::{
    l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0,
    l_System_FilePath_pathExists,
};
use crate::r#gen::Init::initialize_Init;
use crate::r#gen::Lake::Load::Manifest::{initialize_Lake_Load_Manifest, l_Lake_Manifest_load_x3f};
use crate::r#gen::Lean::Class::l_List_elem___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__1;
use crate::r#gen::Lean::CoreM::initialize_Lean_CoreM;
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_isAnonymous, l_Lean_Name_isPrefixOf};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_constants, l_Lean_OLeanLevel_adjustFileName, l_Lean_finalizeImport,
    l_Lean_importModulesCore, l_Lean_instInhabitedImportState_default,
    l_Lean_instOrdOLeanLevel_ord, l_Lean_readModuleDataParts, l_Lean_withImportModules___redArg,
    l_List_toString___at___00Lean_Environment_AddConstAsyncResult_commitConst_spec__1,
    lean_environment_free_regions, lean_mk_empty_environment,
};
use crate::r#gen::Lean::Language::Basic::l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3;
use crate::r#gen::Lean::ReducibilityAttrs::l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2___redArg;
use crate::r#gen::Lean::Replay::{initialize_Lean_Replay, l_Lean_Environment_replay};
use crate::r#gen::Lean::Util::Path::{
    l_Lean_SearchPath_findAllWithExt, l_Lean_findOLean, l_Lean_findSysroot, l_Lean_initSearchPath,
    l_Lean_searchModuleNameOfFileName, l_Lean_searchPathRef,
};
static mut l_replayFromImports___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_replayFromImports___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_replayFromImports___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_replayFromImports___closed__1: u8 = 0;
pub static l_replayFromImports___closed__2_value: crate::leanh::LeanStringObject<27> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 114, 101, 97, 100, 32, 109, 111, 100,
            117, 108, 101, 32, 100, 97, 116, 97, 0,
        ],
    };
static mut l_replayFromImports___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_replayFromImports___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_replayFromImports___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 18,
        },
        m_objs: [core::ptr::addr_of!(l_replayFromImports___closed__2_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_replayFromImports___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_replayFromImports___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_replayFromImports___closed__4_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
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
            111, 98, 106, 101, 99, 116, 32, 102, 105, 108, 101, 32, 39, 0,
        ],
    };
static mut l_replayFromImports___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_replayFromImports___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_replayFromImports___closed__5_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [39, 32, 111, 102, 32, 109, 111, 100, 117, 108, 101, 32, 0],
    };
static mut l_replayFromImports___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_replayFromImports___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_replayFromImports___closed__6_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
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
            32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 101, 120, 105, 115, 116, 0,
        ],
    };
static mut l_replayFromImports___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_replayFromImports___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_replayFromFresh___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_replayFromFresh___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_replayFromFresh___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_replayFromFresh___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_getCurrentModule___closed__0_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
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
            108, 97, 107, 101, 45, 109, 97, 110, 105, 102, 101, 115, 116, 46, 106, 115, 111, 110, 0,
        ],
    };
static mut l_getCurrentModule___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_getCurrentModule___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_partition_loop___at___00main_spec__0___closed__0_value:
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
    m_data: [45, 0],
};
static mut l_List_partition_loop___at___00main_spec__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_partition_loop___at___00main_spec__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_List_partition_loop___at___00main_spec__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_partition_loop___at___00main_spec__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_List_mapM_loop___at___00main_spec__6___closed__0_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 114, 101, 115, 111, 108, 118, 101, 32, 109,
        111, 100, 117, 108, 101, 58, 32, 0,
    ],
};
static mut l_List_mapM_loop___at___00main_spec__6___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_mapM_loop___at___00main_spec__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__0_value:
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
    m_data: [114, 101, 112, 108, 97, 121, 105, 110, 103, 32, 0],
};
static mut l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__1_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
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
        32, 119, 105, 116, 104, 32, 45, 45, 102, 114, 101, 115, 104, 0,
    ],
};
static mut l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [45, 45, 102, 114, 101, 115, 104, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__0_value:
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
    m_data: [111, 108, 101, 97, 110, 0],
};
static mut l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__1_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 102, 105, 110, 100, 32, 97, 110, 121, 32,
        111, 108, 101, 97, 110, 115, 32, 102, 111, 114, 58, 32, 0,
    ],
};
static mut l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__0_value: crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [108, 101, 97, 110, 99, 104, 101, 99, 107, 101, 114, 32, 102, 111, 117, 110, 100, 32, 97, 32, 112, 114, 111, 98, 108, 101, 109, 32, 105, 110, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [108, 101, 97, 110, 0],
    };
static mut l_main___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__1_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_main___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__2_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_main___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__3_value: crate::leanh::LeanStringObject<61> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 61,
        m_capacity: 61,
        m_length: 60,
        m_data: [
            45, 45, 102, 114, 101, 115, 104, 32, 102, 108, 97, 103, 32, 105, 115, 32, 111, 110,
            108, 121, 32, 118, 97, 108, 105, 100, 32, 119, 104, 101, 110, 32, 115, 112, 101, 99,
            105, 102, 121, 105, 110, 103, 32, 97, 32, 115, 105, 110, 103, 108, 101, 32, 109, 111,
            100, 117, 108, 101, 58, 10, 0,
        ],
    };
static mut l_main___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__4_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [45, 118, 0],
    };
static mut l_main___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__5_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [45, 45, 118, 101, 114, 98, 111, 115, 101, 0],
    };
static mut l_main___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__5_value) as *mut crate::leanh::LeanObject;
pub static mut l_main___boxed__const__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(
    mut v_as_776_: *mut crate::leanh::LeanObject,
    mut v_sz_777_: usize,
    mut v_i_778_: usize,
    mut v_b_779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_781_: u8 = 0;
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_787_: u8 = 0;
    let mut v_array_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: u8 = 0;
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_798_: u8 = 0;
    let mut v_a_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: usize = 0;
    let mut v___x_809_: usize = 0;
    let mut v_reuseFailAlloc_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_813_: u8 = 0;
    let mut v_unused_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_781_ = lean_usize_dec_lt(v_i_778_, v_sz_777_);
                if v___x_781_ == 0 {
                    v___x_782_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_782_, 0, v_b_779_);
                    return v___x_782_;
                } else {
                    v_snd_783_ = crate::leanh::lean_ctor_get(v_b_779_, 1);
                    v_fst_784_ = crate::leanh::lean_ctor_get(v_b_779_, 0);
                    v_isSharedCheck_817_ = (!crate::leanh::lean_is_exclusive(v_b_779_)) as u8;
                    if v_isSharedCheck_817_ == 0 {
                        v___x_786_ = v_b_779_;
                        v_isShared_787_ = v_isSharedCheck_817_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_783_);
                        crate::leanh::lean_inc(v_fst_784_);
                        crate::leanh::lean_dec(v_b_779_);
                        v___x_786_ = crate::leanh::lean_box(0);
                        v_isShared_787_ = v_isSharedCheck_817_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_array_788_ = crate::leanh::lean_ctor_get(v_snd_783_, 0);
                v_start_789_ = crate::leanh::lean_ctor_get(v_snd_783_, 1);
                v_stop_790_ = crate::leanh::lean_ctor_get(v_snd_783_, 2);
                v___x_791_ = lean_nat_dec_lt(v_start_789_, v_stop_790_);
                if v___x_791_ == 0 {
                    if v_isShared_787_ == 0 {
                        v___x_793_ = v___x_786_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_795_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_795_, 0, v_fst_784_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_795_, 1, v_snd_783_);
                        v___x_793_ = v_reuseFailAlloc_795_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_stop_790_);
                    crate::leanh::lean_inc(v_start_789_);
                    crate::leanh::lean_inc_ref(v_array_788_);
                    v_isSharedCheck_813_ = (!crate::leanh::lean_is_exclusive(v_snd_783_)) as u8;
                    if v_isSharedCheck_813_ == 0 {
                        v_unused_814_ = crate::leanh::lean_ctor_get(v_snd_783_, 2);
                        crate::leanh::lean_dec(v_unused_814_);
                        v_unused_815_ = crate::leanh::lean_ctor_get(v_snd_783_, 1);
                        crate::leanh::lean_dec(v_unused_815_);
                        v_unused_816_ = crate::leanh::lean_ctor_get(v_snd_783_, 0);
                        crate::leanh::lean_dec(v_unused_816_);
                        v___x_797_ = v_snd_783_;
                        v_isShared_798_ = v_isSharedCheck_813_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_783_);
                        v___x_797_ = crate::leanh::lean_box(0);
                        v_isShared_798_ = v_isSharedCheck_813_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_794_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_794_, 0, v___x_793_);
                return v___x_794_;
            }
            3 => {
                v_a_799_ = lean_array_uget_borrowed(v_as_776_, v_i_778_);
                v___x_800_ = lean_array_fget(v_array_788_, v_start_789_);
                v___x_801_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_802_ = lean_nat_add(v_start_789_, v___x_801_);
                crate::leanh::lean_dec(v_start_789_);
                if v_isShared_798_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_797_, 1, v___x_802_);
                    v___x_804_ = v___x_797_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_812_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_812_, 0, v_array_788_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_802_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_812_, 2, v_stop_790_);
                    v___x_804_ = v_reuseFailAlloc_812_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc(v_a_799_);
                v___x_805_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2___redArg(v_fst_784_, v_a_799_, v___x_800_);
                if v_isShared_787_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_786_, 1, v___x_804_);
                    crate::leanh::lean_ctor_set(v___x_786_, 0, v___x_805_);
                    v___x_807_ = v___x_786_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_811_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_805_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_811_, 1, v___x_804_);
                    v___x_807_ = v_reuseFailAlloc_811_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_808_ = 1usize;
                v___x_809_ = lean_usize_add(v_i_778_, v___x_808_);
                v_i_778_ = v___x_809_;
                v_b_779_ = v___x_807_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0___boxed(
    mut v_as_818_: *mut crate::leanh::LeanObject,
    mut v_sz_819_: *mut crate::leanh::LeanObject,
    mut v_i_820_: *mut crate::leanh::LeanObject,
    mut v_b_821_: *mut crate::leanh::LeanObject,
    mut v___y_822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_823_: usize = 0;
    let mut v_i_boxed_824_: usize = 0;
    let mut v_res_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_823_ = crate::leanh::lean_unbox_usize(v_sz_819_);
    crate::leanh::lean_dec(v_sz_819_);
    v_i_boxed_824_ = crate::leanh::lean_unbox_usize(v_i_820_);
    crate::leanh::lean_dec(v_i_820_);
    v_res_825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(v_as_818_, v_sz_boxed_823_, v_i_boxed_824_, v_b_821_);
    crate::leanh::lean_dec_ref(v_as_818_);
    return v_res_825_;
}
pub unsafe fn _init_l_replayFromImports___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_826_ = crate::leanh::lean_box(0);
    v___x_827_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_828_ = lean_mk_array(v___x_827_, v___x_826_);
    return v___x_828_;
}
pub unsafe fn _init_l_replayFromImports___closed__1() -> u8 {
    let mut v___x_829_: u8 = 0;
    let mut v___x_830_: u8 = 0;
    v___x_829_ = 2;
    v___x_830_ = l_Lean_instOrdOLeanLevel_ord(v___x_829_, v___x_829_);
    return v___x_830_;
}
pub unsafe fn l_replayFromImports(
    mut v_module_837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_843_: u8 = 0;
    let mut v___x_844_: u8 = 0;
    let mut v___y_846_: u8 = 0;
    let mut v___y_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_848_: u8 = 0;
    let mut v___y_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_853_: u8 = 0;
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_imports_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: u32 = 0;
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_869_: u8 = 0;
    let mut v_constNames_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_constants_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_878_: usize = 0;
    let mut v___x_879_: usize = 0;
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_889_: u8 = 0;
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_893_: u8 = 0;
    let mut v_a_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_897_: u8 = 0;
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_901_: u8 = 0;
    let mut v_reuseFailAlloc_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_903_: u8 = 0;
    let mut v_unused_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_908_: u8 = 0;
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_912_: u8 = 0;
    let mut v_fnames_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_919_: u8 = 0;
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: u8 = 0;
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: u8 = 0;
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: u8 = 0;
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_932_: u8 = 0;
    let mut v_a_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_936_: u8 = 0;
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_940_: u8 = 0;
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: u8 = 0;
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: u8 = 0;
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: u8 = 0;
    let mut v___x_960_: u8 = 0;
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: u8 = 0;
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_965_: u8 = 0;
    let mut v_a_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_969_: u8 = 0;
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_973_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_module_837_);
                v___x_839_ = l_Lean_findOLean(v_module_837_);
                if crate::leanh::lean_obj_tag(v___x_839_) == 0 {
                    v_a_840_ = crate::leanh::lean_ctor_get(v___x_839_, 0);
                    v_isSharedCheck_965_ = (!crate::leanh::lean_is_exclusive(v___x_839_)) as u8;
                    if v_isSharedCheck_965_ == 0 {
                        v___x_842_ = v___x_839_;
                        v_isShared_843_ = v_isSharedCheck_965_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_840_);
                        crate::leanh::lean_dec(v___x_839_);
                        v___x_842_ = crate::leanh::lean_box(0);
                        v_isShared_843_ = v_isSharedCheck_965_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_module_837_);
                    v_a_966_ = crate::leanh::lean_ctor_get(v___x_839_, 0);
                    v_isSharedCheck_973_ = (!crate::leanh::lean_is_exclusive(v___x_839_)) as u8;
                    if v_isSharedCheck_973_ == 0 {
                        v___x_968_ = v___x_839_;
                        v_isShared_969_ = v_isSharedCheck_973_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_966_);
                        crate::leanh::lean_dec(v___x_839_);
                        v___x_968_ = crate::leanh::lean_box(0);
                        v_isShared_969_ = v_isSharedCheck_973_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v___x_844_ = l_System_FilePath_pathExists(v_a_840_);
                if v___x_844_ == 0 {
                    v___x_941_ = l_replayFromImports___closed__4;
                    v___x_942_ = lean_string_append(v___x_941_, v_a_840_);
                    crate::leanh::lean_dec(v_a_840_);
                    v___x_943_ = l_replayFromImports___closed__5;
                    v___x_944_ = lean_string_append(v___x_942_, v___x_943_);
                    v___x_945_ = 1;
                    v___x_946_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_module_837_,
                        v___x_945_,
                    );
                    v___x_947_ = lean_string_append(v___x_944_, v___x_946_);
                    crate::leanh::lean_dec_ref(v___x_946_);
                    v___x_948_ = l_replayFromImports___closed__6;
                    v___x_949_ = lean_string_append(v___x_947_, v___x_948_);
                    v___x_950_ = crate::leanh::lean_alloc_ctor(18, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_950_, 0, v___x_949_);
                    if v_isShared_843_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_842_, 1);
                        crate::leanh::lean_ctor_set(v___x_842_, 0, v___x_950_);
                        v___x_952_ = v___x_842_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_953_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
                        v___x_952_ = v_reuseFailAlloc_953_;
                        state = 16;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_842_);
                    crate::leanh::lean_dec(v_module_837_);
                    v___x_954_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_955_ = lean_mk_empty_array_with_capacity(v___x_954_);
                    crate::leanh::lean_inc_n(v_a_840_, 2);
                    v___x_956_ = lean_array_push(v___x_955_, v_a_840_);
                    v___x_957_ = 1;
                    v___x_958_ = l_Lean_OLeanLevel_adjustFileName(v_a_840_, v___x_957_);
                    v___x_959_ = l_System_FilePath_pathExists(v___x_958_);
                    if v___x_959_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_958_);
                        crate::leanh::lean_dec(v_a_840_);
                        v_fnames_914_ = v___x_956_;
                        state = 11;
                        continue;
                    } else {
                        v___x_960_ = 2;
                        v___x_961_ = l_Lean_OLeanLevel_adjustFileName(v_a_840_, v___x_960_);
                        v___x_962_ = l_System_FilePath_pathExists(v___x_961_);
                        v___x_963_ = lean_array_push(v___x_956_, v___x_958_);
                        if v___x_962_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_961_);
                            v_fnames_914_ = v___x_963_;
                            state = 11;
                            continue;
                        } else {
                            v___x_964_ = lean_array_push(v___x_963_, v___x_961_);
                            v_fnames_914_ = v___x_964_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_854_ = l_Lean_instInhabitedImportState_default;
                v___x_855_ = lean_st_mk_ref(v___x_854_);
                v_imports_856_ = crate::leanh::lean_ctor_get(v___y_850_, 0);
                crate::leanh::lean_inc_ref(v_imports_856_);
                crate::leanh::lean_dec_ref(v___y_850_);
                crate::leanh::lean_inc(v___y_847_);
                v___x_857_ = l_Lean_importModulesCore(
                    v_imports_856_,
                    v___y_848_,
                    v___y_847_,
                    v___y_853_,
                    v___x_855_,
                );
                if crate::leanh::lean_obj_tag(v___x_857_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_857_, 1);
                    v___x_858_ = lean_st_ref_get(v___x_855_);
                    crate::leanh::lean_dec(v___x_855_);
                    v___x_859_ = l_Lean_Options_empty;
                    v___x_860_ = 0;
                    v___x_861_ = l_Lean_finalizeImport(
                        v___x_858_,
                        v_imports_856_,
                        v___x_859_,
                        v___x_860_,
                        v___y_846_,
                        v___y_846_,
                        v___y_848_,
                        v___x_844_,
                    );
                    crate::leanh::lean_dec(v___x_858_);
                    if crate::leanh::lean_obj_tag(v___x_861_) == 0 {
                        v_a_862_ = crate::leanh::lean_ctor_get(v___x_861_, 0);
                        crate::leanh::lean_inc(v_a_862_);
                        crate::leanh::lean_dec_ref_known(v___x_861_, 1);
                        v___x_863_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_864_ = lean_nat_sub(v___y_851_, v___x_863_);
                        crate::leanh::lean_dec(v___y_851_);
                        v___x_865_ = lean_array_fget(v___y_852_, v___x_864_);
                        crate::leanh::lean_dec(v___x_864_);
                        crate::leanh::lean_dec_ref(v___y_852_);
                        v_fst_866_ = crate::leanh::lean_ctor_get(v___x_865_, 0);
                        v_isSharedCheck_903_ = (!crate::leanh::lean_is_exclusive(v___x_865_)) as u8;
                        if v_isSharedCheck_903_ == 0 {
                            v_unused_904_ = crate::leanh::lean_ctor_get(v___x_865_, 1);
                            crate::leanh::lean_dec(v_unused_904_);
                            v___x_868_ = v___x_865_;
                            v_isShared_869_ = v_isSharedCheck_903_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_fst_866_);
                            crate::leanh::lean_dec(v___x_865_);
                            v___x_868_ = crate::leanh::lean_box(0);
                            v_isShared_869_ = v_isSharedCheck_903_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_852_);
                        crate::leanh::lean_dec(v___y_851_);
                        crate::leanh::lean_dec(v___y_849_);
                        v_a_905_ = crate::leanh::lean_ctor_get(v___x_861_, 0);
                        v_isSharedCheck_912_ = (!crate::leanh::lean_is_exclusive(v___x_861_)) as u8;
                        if v_isSharedCheck_912_ == 0 {
                            v___x_907_ = v___x_861_;
                            v_isShared_908_ = v_isSharedCheck_912_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_905_);
                            crate::leanh::lean_dec(v___x_861_);
                            v___x_907_ = crate::leanh::lean_box(0);
                            v_isShared_908_ = v_isSharedCheck_912_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_imports_856_);
                    crate::leanh::lean_dec(v___x_855_);
                    crate::leanh::lean_dec_ref(v___y_852_);
                    crate::leanh::lean_dec(v___y_851_);
                    crate::leanh::lean_dec(v___y_849_);
                    return v___x_857_;
                }
            }
            3 => {
                v_constNames_870_ = crate::leanh::lean_ctor_get(v_fst_866_, 1);
                crate::leanh::lean_inc_ref(v_constNames_870_);
                v_constants_871_ = crate::leanh::lean_ctor_get(v_fst_866_, 2);
                crate::leanh::lean_inc_ref(v_constants_871_);
                crate::leanh::lean_dec(v_fst_866_);
                v___x_872_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_replayFromImports___closed__0),
                    core::ptr::addr_of_mut!(l_replayFromImports___closed__0_once),
                    _init_l_replayFromImports___closed__0,
                );
                crate::leanh::lean_inc(v___y_849_);
                v___x_873_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_873_, 0, v___y_849_);
                crate::leanh::lean_ctor_set(v___x_873_, 1, v___x_872_);
                v___x_874_ = lean_array_get_size(v_constants_871_);
                v___x_875_ = l_Array_toSubarray___redArg(v_constants_871_, v___y_849_, v___x_874_);
                if v_isShared_869_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_868_, 1, v___x_875_);
                    crate::leanh::lean_ctor_set(v___x_868_, 0, v___x_873_);
                    v___x_877_ = v___x_868_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_902_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_873_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_902_, 1, v___x_875_);
                    v___x_877_ = v_reuseFailAlloc_902_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_sz_878_ = lean_array_size(v_constNames_870_);
                v___x_879_ = 0usize;
                v___x_880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00replayFromImports_spec__0(v_constNames_870_, v_sz_878_, v___x_879_, v___x_877_);
                crate::leanh::lean_dec_ref(v_constNames_870_);
                if crate::leanh::lean_obj_tag(v___x_880_) == 0 {
                    v_a_881_ = crate::leanh::lean_ctor_get(v___x_880_, 0);
                    crate::leanh::lean_inc(v_a_881_);
                    crate::leanh::lean_dec_ref_known(v___x_880_, 1);
                    v_fst_882_ = crate::leanh::lean_ctor_get(v_a_881_, 0);
                    crate::leanh::lean_inc(v_fst_882_);
                    crate::leanh::lean_dec(v_a_881_);
                    v___x_883_ = l_Lean_Environment_replay(v_fst_882_, v_a_862_);
                    crate::leanh::lean_dec(v_fst_882_);
                    if crate::leanh::lean_obj_tag(v___x_883_) == 0 {
                        v_a_884_ = crate::leanh::lean_ctor_get(v___x_883_, 0);
                        crate::leanh::lean_inc(v_a_884_);
                        crate::leanh::lean_dec_ref_known(v___x_883_, 1);
                        v___x_885_ = lean_environment_free_regions(v_a_884_);
                        return v___x_885_;
                    } else {
                        v_a_886_ = crate::leanh::lean_ctor_get(v___x_883_, 0);
                        v_isSharedCheck_893_ = (!crate::leanh::lean_is_exclusive(v___x_883_)) as u8;
                        if v_isSharedCheck_893_ == 0 {
                            v___x_888_ = v___x_883_;
                            v_isShared_889_ = v_isSharedCheck_893_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_886_);
                            crate::leanh::lean_dec(v___x_883_);
                            v___x_888_ = crate::leanh::lean_box(0);
                            v_isShared_889_ = v_isSharedCheck_893_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_862_);
                    v_a_894_ = crate::leanh::lean_ctor_get(v___x_880_, 0);
                    v_isSharedCheck_901_ = (!crate::leanh::lean_is_exclusive(v___x_880_)) as u8;
                    if v_isSharedCheck_901_ == 0 {
                        v___x_896_ = v___x_880_;
                        v_isShared_897_ = v_isSharedCheck_901_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_894_);
                        crate::leanh::lean_dec(v___x_880_);
                        v___x_896_ = crate::leanh::lean_box(0);
                        v_isShared_897_ = v_isSharedCheck_901_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_889_ == 0 {
                    v___x_891_ = v___x_888_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_892_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
                    v___x_891_ = v_reuseFailAlloc_892_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_891_;
            }
            7 => {
                if v_isShared_897_ == 0 {
                    v___x_899_ = v___x_896_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_900_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
                    v___x_899_ = v_reuseFailAlloc_900_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_899_;
            }
            9 => {
                if v_isShared_908_ == 0 {
                    v___x_910_ = v___x_907_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_911_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
                    v___x_910_ = v_reuseFailAlloc_911_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_910_;
            }
            11 => {
                v___x_915_ = l_Lean_readModuleDataParts(v_fnames_914_);
                crate::leanh::lean_dec_ref(v_fnames_914_);
                if crate::leanh::lean_obj_tag(v___x_915_) == 0 {
                    v_a_916_ = crate::leanh::lean_ctor_get(v___x_915_, 0);
                    v_isSharedCheck_932_ = (!crate::leanh::lean_is_exclusive(v___x_915_)) as u8;
                    if v_isSharedCheck_932_ == 0 {
                        v___x_918_ = v___x_915_;
                        v_isShared_919_ = v_isSharedCheck_932_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_916_);
                        crate::leanh::lean_dec(v___x_915_);
                        v___x_918_ = crate::leanh::lean_box(0);
                        v_isShared_919_ = v_isSharedCheck_932_;
                        state = 12;
                        continue;
                    }
                } else {
                    v_a_933_ = crate::leanh::lean_ctor_get(v___x_915_, 0);
                    v_isSharedCheck_940_ = (!crate::leanh::lean_is_exclusive(v___x_915_)) as u8;
                    if v_isSharedCheck_940_ == 0 {
                        v___x_935_ = v___x_915_;
                        v_isShared_936_ = v_isSharedCheck_940_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_933_);
                        crate::leanh::lean_dec(v___x_915_);
                        v___x_935_ = crate::leanh::lean_box(0);
                        v_isShared_936_ = v_isSharedCheck_940_;
                        state = 14;
                        continue;
                    }
                }
            }
            12 => {
                v___x_920_ = lean_array_get_size(v_a_916_);
                v___x_921_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_922_ = lean_nat_dec_eq(v___x_920_, v___x_921_);
                if v___x_922_ == 0 {
                    crate::leanh::lean_del_object(v___x_918_);
                    v___x_923_ = lean_array_fget_borrowed(v_a_916_, v___x_921_);
                    v_fst_924_ = crate::leanh::lean_ctor_get(v___x_923_, 0);
                    crate::leanh::lean_inc(v_fst_924_);
                    v___x_925_ = 2;
                    v___x_926_ = crate::leanh::lean_box(1);
                    v___x_927_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_replayFromImports___closed__1),
                        core::ptr::addr_of_mut!(l_replayFromImports___closed__1_once),
                        _init_l_replayFromImports___closed__1,
                    );
                    if v___x_927_ == 0 {
                        v___y_846_ = v___x_922_;
                        v___y_847_ = v___x_926_;
                        v___y_848_ = v___x_925_;
                        v___y_849_ = v___x_921_;
                        v___y_850_ = v_fst_924_;
                        v___y_851_ = v___x_920_;
                        v___y_852_ = v_a_916_;
                        v___y_853_ = v___x_844_;
                        state = 2;
                        continue;
                    } else {
                        v___y_846_ = v___x_922_;
                        v___y_847_ = v___x_926_;
                        v___y_848_ = v___x_925_;
                        v___y_849_ = v___x_921_;
                        v___y_850_ = v_fst_924_;
                        v___y_851_ = v___x_920_;
                        v___y_852_ = v_a_916_;
                        v___y_853_ = v___x_922_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_916_);
                    v___x_928_ = l_replayFromImports___closed__3;
                    if v_isShared_919_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_918_, 1);
                        crate::leanh::lean_ctor_set(v___x_918_, 0, v___x_928_);
                        v___x_930_ = v___x_918_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_931_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
                        v___x_930_ = v_reuseFailAlloc_931_;
                        state = 13;
                        continue;
                    }
                }
            }
            13 => {
                return v___x_930_;
            }
            14 => {
                if v_isShared_936_ == 0 {
                    v___x_938_ = v___x_935_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_939_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
                    v___x_938_ = v_reuseFailAlloc_939_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_938_;
            }
            16 => {
                return v___x_952_;
            }
            17 => {
                if v_isShared_969_ == 0 {
                    v___x_971_ = v___x_968_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_972_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
                    v___x_971_ = v_reuseFailAlloc_972_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_971_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_replayFromImports___boxed(
    mut v_module_974_: *mut crate::leanh::LeanObject,
    mut v_a_975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_976_ = l_replayFromImports(v_module_974_);
    return v_res_976_;
}
pub unsafe fn l_replayFromFresh___lam__0(
    mut v_env_977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_979_: u32 = 0;
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2081_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_987_: u8 = 0;
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_992_: u8 = 0;
    let mut v_unused_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_997_: u8 = 0;
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1001_: u8 = 0;
    let mut v_a_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1005_: u8 = 0;
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1009_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_979_ = 0;
                v___x_980_ = lean_mk_empty_environment(v___x_979_);
                if crate::leanh::lean_obj_tag(v___x_980_) == 0 {
                    v_a_981_ = crate::leanh::lean_ctor_get(v___x_980_, 0);
                    crate::leanh::lean_inc(v_a_981_);
                    crate::leanh::lean_dec_ref_known(v___x_980_, 1);
                    v___x_982_ = l_Lean_Environment_constants(v_env_977_);
                    v_map_u2081_983_ = crate::leanh::lean_ctor_get(v___x_982_, 0);
                    crate::leanh::lean_inc_ref(v_map_u2081_983_);
                    crate::leanh::lean_dec_ref(v___x_982_);
                    v___x_984_ = l_Lean_Environment_replay(v_map_u2081_983_, v_a_981_);
                    crate::leanh::lean_dec_ref(v_map_u2081_983_);
                    if crate::leanh::lean_obj_tag(v___x_984_) == 0 {
                        v_isSharedCheck_992_ = (!crate::leanh::lean_is_exclusive(v___x_984_)) as u8;
                        if v_isSharedCheck_992_ == 0 {
                            v_unused_993_ = crate::leanh::lean_ctor_get(v___x_984_, 0);
                            crate::leanh::lean_dec(v_unused_993_);
                            v___x_986_ = v___x_984_;
                            v_isShared_987_ = v_isSharedCheck_992_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_984_);
                            v___x_986_ = crate::leanh::lean_box(0);
                            v_isShared_987_ = v_isSharedCheck_992_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_994_ = crate::leanh::lean_ctor_get(v___x_984_, 0);
                        v_isSharedCheck_1001_ =
                            (!crate::leanh::lean_is_exclusive(v___x_984_)) as u8;
                        if v_isSharedCheck_1001_ == 0 {
                            v___x_996_ = v___x_984_;
                            v_isShared_997_ = v_isSharedCheck_1001_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_994_);
                            crate::leanh::lean_dec(v___x_984_);
                            v___x_996_ = crate::leanh::lean_box(0);
                            v_isShared_997_ = v_isSharedCheck_1001_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_977_);
                    v_a_1002_ = crate::leanh::lean_ctor_get(v___x_980_, 0);
                    v_isSharedCheck_1009_ = (!crate::leanh::lean_is_exclusive(v___x_980_)) as u8;
                    if v_isSharedCheck_1009_ == 0 {
                        v___x_1004_ = v___x_980_;
                        v_isShared_1005_ = v_isSharedCheck_1009_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1002_);
                        crate::leanh::lean_dec(v___x_980_);
                        v___x_1004_ = crate::leanh::lean_box(0);
                        v_isShared_1005_ = v_isSharedCheck_1009_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_988_ = crate::leanh::lean_box(0);
                if v_isShared_987_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_986_, 0, v___x_988_);
                    v___x_990_ = v___x_986_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_991_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
                    v___x_990_ = v_reuseFailAlloc_991_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_990_;
            }
            3 => {
                if v_isShared_997_ == 0 {
                    v___x_999_ = v___x_996_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1000_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
                    v___x_999_ = v_reuseFailAlloc_1000_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_999_;
            }
            5 => {
                if v_isShared_1005_ == 0 {
                    v___x_1007_ = v___x_1004_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1008_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
                    v___x_1007_ = v_reuseFailAlloc_1008_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1007_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_replayFromFresh___lam__0___boxed(
    mut v_env_1010_: *mut crate::leanh::LeanObject,
    mut v___y_1011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1012_ = l_replayFromFresh___lam__0(v_env_1010_);
    return v_res_1012_;
}
pub unsafe fn l_replayFromFresh(
    mut v_module_1014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: u8 = 0;
    let mut v___x_1018_: u8 = 0;
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: u32 = 0;
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1016_ = l_replayFromFresh___closed__0;
    v___x_1017_ = 0;
    v___x_1018_ = 1;
    v___x_1019_ = crate::leanh::lean_alloc_ctor(0, 1, (3) as u32);
    crate::leanh::lean_ctor_set(v___x_1019_, 0, v_module_1014_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1019_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1017_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1019_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
        v___x_1018_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1019_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 2) as u32,
        v___x_1017_,
    );
    v___x_1020_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1021_ = lean_mk_empty_array_with_capacity(v___x_1020_);
    v___x_1022_ = lean_array_push(v___x_1021_, v___x_1019_);
    v___x_1023_ = l_Lean_Options_empty;
    v___x_1024_ = 0;
    v___x_1025_ =
        l_Lean_withImportModules___redArg(v___x_1022_, v___x_1023_, v___f_1016_, v___x_1024_);
    return v___x_1025_;
}
pub unsafe fn l_replayFromFresh___boxed(
    mut v_module_1026_: *mut crate::leanh::LeanObject,
    mut v_a_1027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1028_ = l_replayFromFresh(v_module_1026_);
    return v_res_1028_;
}
pub unsafe fn l_getCurrentModule() -> *mut crate::leanh::LeanObject {
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1036_: u8 = 0;
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1047_: u8 = 0;
    let mut v_a_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1051_: u8 = 0;
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1031_ = l_getCurrentModule___closed__0;
                v___x_1032_ = l_Lake_Manifest_load_x3f(v___x_1031_);
                if crate::leanh::lean_obj_tag(v___x_1032_) == 0 {
                    v_a_1033_ = crate::leanh::lean_ctor_get(v___x_1032_, 0);
                    v_isSharedCheck_1047_ = (!crate::leanh::lean_is_exclusive(v___x_1032_)) as u8;
                    if v_isSharedCheck_1047_ == 0 {
                        v___x_1035_ = v___x_1032_;
                        v_isShared_1036_ = v_isSharedCheck_1047_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1033_);
                        crate::leanh::lean_dec(v___x_1032_);
                        v___x_1035_ = crate::leanh::lean_box(0);
                        v_isShared_1036_ = v_isSharedCheck_1047_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1048_ = crate::leanh::lean_ctor_get(v___x_1032_, 0);
                    v_isSharedCheck_1055_ = (!crate::leanh::lean_is_exclusive(v___x_1032_)) as u8;
                    if v_isSharedCheck_1055_ == 0 {
                        v___x_1050_ = v___x_1032_;
                        v_isShared_1051_ = v_isSharedCheck_1055_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1048_);
                        crate::leanh::lean_dec(v___x_1032_);
                        v___x_1050_ = crate::leanh::lean_box(0);
                        v_isShared_1051_ = v_isSharedCheck_1055_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1033_) == 0 {
                    v___x_1037_ = crate::leanh::lean_box(0);
                    if v_isShared_1036_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1035_, 0, v___x_1037_);
                        v___x_1039_ = v___x_1035_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1040_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
                        v___x_1039_ = v_reuseFailAlloc_1040_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_1041_ = crate::leanh::lean_ctor_get(v_a_1033_, 0);
                    crate::leanh::lean_inc(v_val_1041_);
                    crate::leanh::lean_dec_ref_known(v_a_1033_, 1);
                    v_name_1042_ = crate::leanh::lean_ctor_get(v_val_1041_, 0);
                    crate::leanh::lean_inc(v_name_1042_);
                    crate::leanh::lean_dec(v_val_1041_);
                    v___x_1043_ = l_Lean_Name_capitalize(v_name_1042_);
                    if v_isShared_1036_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1035_, 0, v___x_1043_);
                        v___x_1045_ = v___x_1035_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1046_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1043_);
                        v___x_1045_ = v_reuseFailAlloc_1046_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1039_;
            }
            3 => {
                return v___x_1045_;
            }
            4 => {
                if v_isShared_1051_ == 0 {
                    v___x_1053_ = v___x_1050_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1054_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
                    v___x_1053_ = v_reuseFailAlloc_1054_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1053_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_getCurrentModule___boxed(
    mut v_a_1056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1057_ = l_getCurrentModule();
    return v_res_1057_;
}
pub unsafe fn _init_l_List_partition_loop___at___00main_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1059_ = l_List_partition_loop___at___00main_spec__0___closed__0;
    v___x_1060_ = lean_string_utf8_byte_size(v___x_1059_);
    return v___x_1060_;
}
pub unsafe fn l_List_partition_loop___at___00main_spec__0(
    mut v_a_1061_: *mut crate::leanh::LeanObject,
    mut v_a_1062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1067_: u8 = 0;
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1073_: u8 = 0;
    let mut v_head_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1078_: u8 = 0;
    let mut v_fst_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1083_: u8 = 0;
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: u8 = 0;
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: u8 = 0;
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1101_: u8 = 0;
    let mut v_isSharedCheck_1102_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1061_) == 0 {
                    v_fst_1063_ = crate::leanh::lean_ctor_get(v_a_1062_, 0);
                    v_snd_1064_ = crate::leanh::lean_ctor_get(v_a_1062_, 1);
                    v_isSharedCheck_1073_ = (!crate::leanh::lean_is_exclusive(v_a_1062_)) as u8;
                    if v_isSharedCheck_1073_ == 0 {
                        v___x_1066_ = v_a_1062_;
                        v_isShared_1067_ = v_isSharedCheck_1073_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1064_);
                        crate::leanh::lean_inc(v_fst_1063_);
                        crate::leanh::lean_dec(v_a_1062_);
                        v___x_1066_ = crate::leanh::lean_box(0);
                        v_isShared_1067_ = v_isSharedCheck_1073_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_head_1074_ = crate::leanh::lean_ctor_get(v_a_1061_, 0);
                    v_tail_1075_ = crate::leanh::lean_ctor_get(v_a_1061_, 1);
                    v_isSharedCheck_1102_ = (!crate::leanh::lean_is_exclusive(v_a_1061_)) as u8;
                    if v_isSharedCheck_1102_ == 0 {
                        v___x_1077_ = v_a_1061_;
                        v_isShared_1078_ = v_isSharedCheck_1102_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1075_);
                        crate::leanh::lean_inc(v_head_1074_);
                        crate::leanh::lean_dec(v_a_1061_);
                        v___x_1077_ = crate::leanh::lean_box(0);
                        v_isShared_1078_ = v_isSharedCheck_1102_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1068_ = l_List_reverse___redArg(v_fst_1063_);
                v___x_1069_ = l_List_reverse___redArg(v_snd_1064_);
                if v_isShared_1067_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1066_, 1, v___x_1069_);
                    crate::leanh::lean_ctor_set(v___x_1066_, 0, v___x_1068_);
                    v___x_1071_ = v___x_1066_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1072_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1068_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1072_, 1, v___x_1069_);
                    v___x_1071_ = v_reuseFailAlloc_1072_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1071_;
            }
            3 => {
                v_fst_1079_ = crate::leanh::lean_ctor_get(v_a_1062_, 0);
                v_snd_1080_ = crate::leanh::lean_ctor_get(v_a_1062_, 1);
                v_isSharedCheck_1101_ = (!crate::leanh::lean_is_exclusive(v_a_1062_)) as u8;
                if v_isSharedCheck_1101_ == 0 {
                    v___x_1082_ = v_a_1062_;
                    v_isShared_1083_ = v_isSharedCheck_1101_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1080_);
                    crate::leanh::lean_inc(v_fst_1079_);
                    crate::leanh::lean_dec(v_a_1062_);
                    v___x_1082_ = crate::leanh::lean_box(0);
                    v_isShared_1083_ = v_isSharedCheck_1101_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1092_ = l_List_partition_loop___at___00main_spec__0___closed__0;
                v___x_1093_ = lean_string_utf8_byte_size(v_head_1074_);
                v___x_1094_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_List_partition_loop___at___00main_spec__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_List_partition_loop___at___00main_spec__0___closed__1_once
                    ),
                    _init_l_List_partition_loop___at___00main_spec__0___closed__1,
                );
                v___x_1095_ = lean_nat_dec_le(v___x_1094_, v___x_1093_);
                if v___x_1095_ == 0 {
                    state = 5;
                    continue;
                } else {
                    v___x_1096_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1097_ = lean_string_memcmp(
                        v_head_1074_,
                        v___x_1092_,
                        v___x_1096_,
                        v___x_1096_,
                        v___x_1094_,
                    );
                    if v___x_1097_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_1082_);
                        crate::leanh::lean_del_object(v___x_1077_);
                        v___x_1098_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1098_, 0, v_head_1074_);
                        crate::leanh::lean_ctor_set(v___x_1098_, 1, v_fst_1079_);
                        v___x_1099_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1099_, 0, v___x_1098_);
                        crate::leanh::lean_ctor_set(v___x_1099_, 1, v_snd_1080_);
                        v_a_1061_ = v_tail_1075_;
                        v_a_1062_ = v___x_1099_;
                        state = 0;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_1078_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1077_, 1, v_snd_1080_);
                    v___x_1086_ = v___x_1077_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1091_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_head_1074_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_snd_1080_);
                    v___x_1086_ = v_reuseFailAlloc_1091_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1083_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1082_, 1, v___x_1086_);
                    v___x_1088_ = v___x_1082_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1090_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_fst_1079_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1090_, 1, v___x_1086_);
                    v___x_1088_ = v_reuseFailAlloc_1090_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_a_1061_ = v_tail_1075_;
                v_a_1062_ = v___x_1088_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0(
    mut v_head_1103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1109_: u8 = 0;
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1113_: u8 = 0;
    let mut v_a_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1117_: u8 = 0;
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1121_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1105_ = l_replayFromImports(v_head_1103_);
                if crate::leanh::lean_obj_tag(v___x_1105_) == 0 {
                    v_a_1106_ = crate::leanh::lean_ctor_get(v___x_1105_, 0);
                    v_isSharedCheck_1113_ = (!crate::leanh::lean_is_exclusive(v___x_1105_)) as u8;
                    if v_isSharedCheck_1113_ == 0 {
                        v___x_1108_ = v___x_1105_;
                        v_isShared_1109_ = v_isSharedCheck_1113_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1106_);
                        crate::leanh::lean_dec(v___x_1105_);
                        v___x_1108_ = crate::leanh::lean_box(0);
                        v_isShared_1109_ = v_isSharedCheck_1113_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1114_ = crate::leanh::lean_ctor_get(v___x_1105_, 0);
                    v_isSharedCheck_1121_ = (!crate::leanh::lean_is_exclusive(v___x_1105_)) as u8;
                    if v_isSharedCheck_1121_ == 0 {
                        v___x_1116_ = v___x_1105_;
                        v_isShared_1117_ = v_isSharedCheck_1121_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1114_);
                        crate::leanh::lean_dec(v___x_1105_);
                        v___x_1116_ = crate::leanh::lean_box(0);
                        v_isShared_1117_ = v_isSharedCheck_1121_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1109_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1108_, 1);
                    v___x_1111_ = v___x_1108_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1112_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
                    v___x_1111_ = v_reuseFailAlloc_1112_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1111_;
            }
            3 => {
                if v_isShared_1117_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1116_, 0);
                    v___x_1119_ = v___x_1116_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1120_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
                    v___x_1119_ = v_reuseFailAlloc_1120_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1119_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0___boxed(
    mut v_head_1122_: *mut crate::leanh::LeanObject,
    mut v___y_1123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1124_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0(v_head_1122_);
    return v_res_1124_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00main_spec__3___redArg(
    mut v_as_x27_1125_: *mut crate::leanh::LeanObject,
    mut v_b_1126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_1125_) == 0 {
                    v___x_1128_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1128_, 0, v_b_1126_);
                    return v___x_1128_;
                } else {
                    v_head_1129_ = crate::leanh::lean_ctor_get(v_as_x27_1125_, 0);
                    v_tail_1130_ = crate::leanh::lean_ctor_get(v_as_x27_1125_, 1);
                    crate::leanh::lean_inc_n(v_head_1129_, 2);
                    v___f_1131_ = crate::leanh::lean_alloc_closure(
                        l_List_forIn_x27_loop___at___00main_spec__3___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_1131_, 0, v_head_1129_);
                    v___x_1132_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1133_ = lean_io_as_task(v___f_1131_, v___x_1132_);
                    v___x_1134_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1134_, 0, v_head_1129_);
                    crate::leanh::lean_ctor_set(v___x_1134_, 1, v___x_1133_);
                    v___x_1135_ = lean_array_push(v_b_1126_, v___x_1134_);
                    v_as_x27_1125_ = v_tail_1130_;
                    v_b_1126_ = v___x_1135_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00main_spec__3___redArg___boxed(
    mut v_as_x27_1137_: *mut crate::leanh::LeanObject,
    mut v_b_1138_: *mut crate::leanh::LeanObject,
    mut v___y_1139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1140_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v_as_x27_1137_, v_b_1138_);
    crate::leanh::lean_dec(v_as_x27_1137_);
    return v_res_1140_;
}
pub unsafe fn l_List_mapM_loop___at___00main_spec__6(
    mut v_x_1142_: *mut crate::leanh::LeanObject,
    mut v_x_1143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1151_: u8 = 0;
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: u8 = 0;
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1162_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1142_) == 0 {
                    v___x_1145_ = l_List_reverse___redArg(v_x_1143_);
                    v___x_1146_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1146_, 0, v___x_1145_);
                    return v___x_1146_;
                } else {
                    v_head_1147_ = crate::leanh::lean_ctor_get(v_x_1142_, 0);
                    v_tail_1148_ = crate::leanh::lean_ctor_get(v_x_1142_, 1);
                    v_isSharedCheck_1162_ = (!crate::leanh::lean_is_exclusive(v_x_1142_)) as u8;
                    if v_isSharedCheck_1162_ == 0 {
                        v___x_1150_ = v_x_1142_;
                        v_isShared_1151_ = v_isSharedCheck_1162_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1148_);
                        crate::leanh::lean_inc(v_head_1147_);
                        crate::leanh::lean_dec(v_x_1142_);
                        v___x_1150_ = crate::leanh::lean_box(0);
                        v_isShared_1151_ = v_isSharedCheck_1162_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_head_1147_);
                v___x_1152_ = l_String_toName(v_head_1147_);
                v___x_1153_ = l_Lean_Name_isAnonymous(v___x_1152_);
                if v___x_1153_ == 0 {
                    crate::leanh::lean_dec(v_head_1147_);
                    if v_isShared_1151_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1150_, 1, v_x_1143_);
                        crate::leanh::lean_ctor_set(v___x_1150_, 0, v___x_1152_);
                        v___x_1155_ = v___x_1150_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1157_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1152_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_x_1143_);
                        v___x_1155_ = v_reuseFailAlloc_1157_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1152_);
                    crate::leanh::lean_del_object(v___x_1150_);
                    crate::leanh::lean_dec(v_tail_1148_);
                    crate::leanh::lean_dec(v_x_1143_);
                    v___x_1158_ = l_List_mapM_loop___at___00main_spec__6___closed__0;
                    v___x_1159_ = lean_string_append(v___x_1158_, v_head_1147_);
                    crate::leanh::lean_dec(v_head_1147_);
                    v___x_1160_ = crate::leanh::lean_alloc_ctor(18, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1160_, 0, v___x_1159_);
                    v___x_1161_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1161_, 0, v___x_1160_);
                    return v___x_1161_;
                }
            }
            2 => {
                v_x_1142_ = v_tail_1148_;
                v_x_1143_ = v___x_1155_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00main_spec__6___boxed(
    mut v_x_1163_: *mut crate::leanh::LeanObject,
    mut v_x_1164_: *mut crate::leanh::LeanObject,
    mut v___y_1165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1166_ = l_List_mapM_loop___at___00main_spec__6(v_x_1163_, v_x_1164_);
    return v_res_1166_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00main_spec__5___redArg(
    mut v___y_1169_: u8,
    mut v_as_x27_1170_: *mut crate::leanh::LeanObject,
    mut v_b_1171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_1170_) == 0 {
                    v___x_1173_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1173_, 0, v_b_1171_);
                    return v___x_1173_;
                } else {
                    v_head_1174_ = crate::leanh::lean_ctor_get(v_as_x27_1170_, 0);
                    v_tail_1175_ = crate::leanh::lean_ctor_get(v_as_x27_1170_, 1);
                    v___x_1176_ = crate::leanh::lean_box(0);
                    if v___y_1169_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_1180_ =
                            l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__0;
                        crate::leanh::lean_inc(v_head_1174_);
                        v___x_1181_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_head_1174_,
                                v___y_1169_,
                            );
                        v___x_1182_ = lean_string_append(v___x_1180_, v___x_1181_);
                        crate::leanh::lean_dec_ref(v___x_1181_);
                        v___x_1183_ =
                            l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__1;
                        v___x_1184_ = lean_string_append(v___x_1182_, v___x_1183_);
                        v___x_1185_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v___x_1184_);
                        if crate::leanh::lean_obj_tag(v___x_1185_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1185_, 1);
                            state = 1;
                            continue;
                        } else {
                            return v___x_1185_;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_head_1174_);
                v___x_1178_ = l_replayFromFresh(v_head_1174_);
                if crate::leanh::lean_obj_tag(v___x_1178_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1178_, 1);
                    v_as_x27_1170_ = v_tail_1175_;
                    v_b_1171_ = v___x_1176_;
                    state = 0;
                    continue;
                } else {
                    return v___x_1178_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00main_spec__5___redArg___boxed(
    mut v___y_1186_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1187_: *mut crate::leanh::LeanObject,
    mut v_b_1188_: *mut crate::leanh::LeanObject,
    mut v___y_1189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5439__boxed_1190_: u8 = 0;
    let mut v_res_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_5439__boxed_1190_ = (crate::leanh::lean_unbox(v___y_1186_) as u8);
    v_res_1191_ = l_List_forIn_x27_loop___at___00main_spec__5___redArg(
        v___y_5439__boxed_1190_,
        v_as_x27_1187_,
        v_b_1188_,
    );
    crate::leanh::lean_dec(v_as_x27_1187_);
    return v_res_1191_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1192_ = crate::leanh::lean_alloc_closure(
        l_instDecidableEqString___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_1193_ = crate::leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1193_, 0, v___x_1192_);
    return v___f_1193_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(
    mut v_val_1195_: *mut crate::leanh::LeanObject,
    mut v_a_1196_: *mut crate::leanh::LeanObject,
    mut v_fst_1197_: *mut crate::leanh::LeanObject,
    mut v_as_1198_: *mut crate::leanh::LeanObject,
    mut v_sz_1199_: usize,
    mut v_i_1200_: usize,
    mut v_b_1201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: usize = 0;
    let mut v___x_1206_: usize = 0;
    let mut v___x_1208_: u8 = 0;
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1221_: u8 = 0;
    let mut v_val_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: u8 = 0;
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: u8 = 0;
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: u8 = 0;
    let mut v___x_1234_: u8 = 0;
    let mut v_isSharedCheck_1235_: u8 = 0;
    let mut v_fst_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1240_: u8 = 0;
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1244_: u8 = 0;
    let mut v_a_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1248_: u8 = 0;
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1252_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1208_ = lean_usize_dec_lt(v_i_1200_, v_sz_1199_);
                if v___x_1208_ == 0 {
                    crate::leanh::lean_dec(v_fst_1197_);
                    v___x_1209_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1209_, 0, v_b_1201_);
                    return v___x_1209_;
                } else {
                    v_a_1210_ = lean_array_uget_borrowed(v_as_1198_, v_i_1200_);
                    crate::leanh::lean_inc(v_a_1210_);
                    v___x_1211_ = l_Lean_searchModuleNameOfFileName(v_a_1210_, v_val_1195_);
                    if crate::leanh::lean_obj_tag(v___x_1211_) == 0 {
                        v_a_1212_ = crate::leanh::lean_ctor_get(v___x_1211_, 0);
                        crate::leanh::lean_inc(v_a_1212_);
                        crate::leanh::lean_dec_ref_known(v___x_1211_, 1);
                        if crate::leanh::lean_obj_tag(v_a_1212_) == 1 {
                            v_fst_1217_ = crate::leanh::lean_ctor_get(v_b_1201_, 0);
                            v_snd_1218_ = crate::leanh::lean_ctor_get(v_b_1201_, 1);
                            v_isSharedCheck_1235_ =
                                (!crate::leanh::lean_is_exclusive(v_b_1201_)) as u8;
                            if v_isSharedCheck_1235_ == 0 {
                                v___x_1220_ = v_b_1201_;
                                v_isShared_1221_ = v_isSharedCheck_1235_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_1218_);
                                crate::leanh::lean_inc(v_fst_1217_);
                                crate::leanh::lean_dec(v_b_1201_);
                                v___x_1220_ = crate::leanh::lean_box(0);
                                v_isShared_1221_ = v_isSharedCheck_1235_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1212_);
                            v_fst_1236_ = crate::leanh::lean_ctor_get(v_b_1201_, 0);
                            v_snd_1237_ = crate::leanh::lean_ctor_get(v_b_1201_, 1);
                            v_isSharedCheck_1244_ =
                                (!crate::leanh::lean_is_exclusive(v_b_1201_)) as u8;
                            if v_isSharedCheck_1244_ == 0 {
                                v___x_1239_ = v_b_1201_;
                                v_isShared_1240_ = v_isSharedCheck_1244_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_1237_);
                                crate::leanh::lean_inc(v_fst_1236_);
                                crate::leanh::lean_dec(v_b_1201_);
                                v___x_1239_ = crate::leanh::lean_box(0);
                                v_isShared_1240_ = v_isSharedCheck_1244_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_1201_);
                        crate::leanh::lean_dec(v_fst_1197_);
                        v_a_1245_ = crate::leanh::lean_ctor_get(v___x_1211_, 0);
                        v_isSharedCheck_1252_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1211_)) as u8;
                        if v_isSharedCheck_1252_ == 0 {
                            v___x_1247_ = v___x_1211_;
                            v_isShared_1248_ = v_isSharedCheck_1252_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1245_);
                            crate::leanh::lean_dec(v___x_1211_);
                            v___x_1247_ = crate::leanh::lean_box(0);
                            v_isShared_1248_ = v_isSharedCheck_1252_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1205_ = 1usize;
                v___x_1206_ = lean_usize_add(v_i_1200_, v___x_1205_);
                v_i_1200_ = v___x_1206_;
                v_b_1201_ = v_a_1204_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1215_ = crate::leanh::lean_box((v___x_1208_) as usize);
                v___x_1216_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1216_, 0, v___y_1214_);
                crate::leanh::lean_ctor_set(v___x_1216_, 1, v___x_1215_);
                v_a_1204_ = v___x_1216_;
                state = 1;
                continue;
            }
            3 => {
                v_val_1222_ = crate::leanh::lean_ctor_get(v_a_1212_, 0);
                crate::leanh::lean_inc(v_val_1222_);
                crate::leanh::lean_dec_ref_known(v_a_1212_, 1);
                v___f_1231_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0);
                v___x_1232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1;
                crate::leanh::lean_inc(v_fst_1197_);
                v___x_1233_ = l_List_elem___redArg(v___f_1231_, v___x_1232_, v_fst_1197_);
                if v___x_1233_ == 0 {
                    v___x_1234_ = l_Lean_Name_isPrefixOf(v_a_1196_, v_val_1222_);
                    if v___x_1234_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_1220_);
                        crate::leanh::lean_dec(v_snd_1218_);
                        state = 4;
                        continue;
                    }
                } else {
                    state = 5;
                    continue;
                }
            }
            4 => {
                v___x_1224_ = l_List_elem___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__1(v_val_1222_, v_fst_1217_);
                if v___x_1224_ == 0 {
                    v___x_1225_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1225_, 0, v_val_1222_);
                    crate::leanh::lean_ctor_set(v___x_1225_, 1, v_fst_1217_);
                    v___y_1214_ = v___x_1225_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_1222_);
                    v___y_1214_ = v_fst_1217_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_1227_ = lean_name_eq(v_a_1196_, v_val_1222_);
                if v___x_1227_ == 0 {
                    crate::leanh::lean_dec(v_val_1222_);
                    if v_isShared_1221_ == 0 {
                        v___x_1229_ = v___x_1220_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1230_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_fst_1217_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_snd_1218_);
                        v___x_1229_ = v_reuseFailAlloc_1230_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1220_);
                    crate::leanh::lean_dec(v_snd_1218_);
                    state = 4;
                    continue;
                }
            }
            6 => {
                v_a_1204_ = v___x_1229_;
                state = 1;
                continue;
            }
            7 => {
                if v_isShared_1240_ == 0 {
                    v___x_1242_ = v___x_1239_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1243_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_fst_1236_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_snd_1237_);
                    v___x_1242_ = v_reuseFailAlloc_1243_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_a_1204_ = v___x_1242_;
                state = 1;
                continue;
            }
            9 => {
                if v_isShared_1248_ == 0 {
                    v___x_1250_ = v___x_1247_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1251_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
                    v___x_1250_ = v_reuseFailAlloc_1251_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1250_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___boxed(
    mut v_val_1253_: *mut crate::leanh::LeanObject,
    mut v_a_1254_: *mut crate::leanh::LeanObject,
    mut v_fst_1255_: *mut crate::leanh::LeanObject,
    mut v_as_1256_: *mut crate::leanh::LeanObject,
    mut v_sz_1257_: *mut crate::leanh::LeanObject,
    mut v_i_1258_: *mut crate::leanh::LeanObject,
    mut v_b_1259_: *mut crate::leanh::LeanObject,
    mut v___y_1260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1261_: usize = 0;
    let mut v_i_boxed_1262_: usize = 0;
    let mut v_res_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1261_ = crate::leanh::lean_unbox_usize(v_sz_1257_);
    crate::leanh::lean_dec(v_sz_1257_);
    v_i_boxed_1262_ = crate::leanh::lean_unbox_usize(v_i_1258_);
    crate::leanh::lean_dec(v_i_1258_);
    v_res_1263_ =
        l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(
            v_val_1253_,
            v_a_1254_,
            v_fst_1255_,
            v_as_1256_,
            v_sz_boxed_1261_,
            v_i_boxed_1262_,
            v_b_1259_,
        );
    crate::leanh::lean_dec_ref(v_as_1256_);
    crate::leanh::lean_dec(v_a_1254_);
    crate::leanh::lean_dec(v_val_1253_);
    return v_res_1263_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00main_spec__2___redArg(
    mut v_val_1266_: *mut crate::leanh::LeanObject,
    mut v_fst_1267_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1268_: *mut crate::leanh::LeanObject,
    mut v_b_1269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: u8 = 0;
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1280_: usize = 0;
    let mut v___x_1281_: usize = 0;
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1286_: u8 = 0;
    let mut v_snd_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: u8 = 0;
    let mut v___x_1289_: u8 = 0;
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1299_: u8 = 0;
    let mut v_a_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1303_: u8 = 0;
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1307_: u8 = 0;
    let mut v_a_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1311_: u8 = 0;
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1315_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_1268_) == 0 {
                    crate::leanh::lean_dec(v_fst_1267_);
                    v___x_1271_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1271_, 0, v_b_1269_);
                    return v___x_1271_;
                } else {
                    v_head_1272_ = crate::leanh::lean_ctor_get(v_as_x27_1268_, 0);
                    v_tail_1273_ = crate::leanh::lean_ctor_get(v_as_x27_1268_, 1);
                    v___x_1274_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__0;
                    v___x_1275_ = l_Lean_SearchPath_findAllWithExt(v_val_1266_, v___x_1274_);
                    if crate::leanh::lean_obj_tag(v___x_1275_) == 0 {
                        v_a_1276_ = crate::leanh::lean_ctor_get(v___x_1275_, 0);
                        crate::leanh::lean_inc(v_a_1276_);
                        crate::leanh::lean_dec_ref_known(v___x_1275_, 1);
                        v___x_1277_ = 0;
                        v___x_1278_ = crate::leanh::lean_box((v___x_1277_) as usize);
                        v___x_1279_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1279_, 0, v_b_1269_);
                        crate::leanh::lean_ctor_set(v___x_1279_, 1, v___x_1278_);
                        v_sz_1280_ = lean_array_size(v_a_1276_);
                        v___x_1281_ = 0usize;
                        crate::leanh::lean_inc(v_fst_1267_);
                        v___x_1282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1(v_val_1266_, v_head_1272_, v_fst_1267_, v_a_1276_, v_sz_1280_, v___x_1281_, v___x_1279_);
                        crate::leanh::lean_dec(v_a_1276_);
                        if crate::leanh::lean_obj_tag(v___x_1282_) == 0 {
                            v_a_1283_ = crate::leanh::lean_ctor_get(v___x_1282_, 0);
                            v_isSharedCheck_1299_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1282_)) as u8;
                            if v_isSharedCheck_1299_ == 0 {
                                v___x_1285_ = v___x_1282_;
                                v_isShared_1286_ = v_isSharedCheck_1299_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1283_);
                                crate::leanh::lean_dec(v___x_1282_);
                                v___x_1285_ = crate::leanh::lean_box(0);
                                v_isShared_1286_ = v_isSharedCheck_1299_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_1267_);
                            v_a_1300_ = crate::leanh::lean_ctor_get(v___x_1282_, 0);
                            v_isSharedCheck_1307_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1282_)) as u8;
                            if v_isSharedCheck_1307_ == 0 {
                                v___x_1302_ = v___x_1282_;
                                v_isShared_1303_ = v_isSharedCheck_1307_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1300_);
                                crate::leanh::lean_dec(v___x_1282_);
                                v___x_1302_ = crate::leanh::lean_box(0);
                                v_isShared_1303_ = v_isSharedCheck_1307_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_1269_);
                        crate::leanh::lean_dec(v_fst_1267_);
                        v_a_1308_ = crate::leanh::lean_ctor_get(v___x_1275_, 0);
                        v_isSharedCheck_1315_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1275_)) as u8;
                        if v_isSharedCheck_1315_ == 0 {
                            v___x_1310_ = v___x_1275_;
                            v_isShared_1311_ = v_isSharedCheck_1315_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1308_);
                            crate::leanh::lean_dec(v___x_1275_);
                            v___x_1310_ = crate::leanh::lean_box(0);
                            v_isShared_1311_ = v_isSharedCheck_1315_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_snd_1287_ = crate::leanh::lean_ctor_get(v_a_1283_, 1);
                v___x_1288_ = (crate::leanh::lean_unbox(v_snd_1287_) as u8);
                if v___x_1288_ == 0 {
                    crate::leanh::lean_dec(v_a_1283_);
                    crate::leanh::lean_dec(v_fst_1267_);
                    v___x_1289_ = 1;
                    v___x_1290_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg___closed__1;
                    crate::leanh::lean_inc(v_head_1272_);
                    v___x_1291_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_head_1272_,
                        v___x_1289_,
                    );
                    v___x_1292_ = lean_string_append(v___x_1290_, v___x_1291_);
                    crate::leanh::lean_dec_ref(v___x_1291_);
                    v___x_1293_ = crate::leanh::lean_alloc_ctor(18, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1293_, 0, v___x_1292_);
                    if v_isShared_1286_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1285_, 1);
                        crate::leanh::lean_ctor_set(v___x_1285_, 0, v___x_1293_);
                        v___x_1295_ = v___x_1285_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1296_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
                        v___x_1295_ = v_reuseFailAlloc_1296_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1285_);
                    v_fst_1297_ = crate::leanh::lean_ctor_get(v_a_1283_, 0);
                    crate::leanh::lean_inc(v_fst_1297_);
                    crate::leanh::lean_dec(v_a_1283_);
                    v_as_x27_1268_ = v_tail_1273_;
                    v_b_1269_ = v_fst_1297_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_1295_;
            }
            3 => {
                if v_isShared_1303_ == 0 {
                    v___x_1305_ = v___x_1302_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1306_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
                    v___x_1305_ = v_reuseFailAlloc_1306_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1305_;
            }
            5 => {
                if v_isShared_1311_ == 0 {
                    v___x_1313_ = v___x_1310_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1314_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
                    v___x_1313_ = v_reuseFailAlloc_1314_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1313_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00main_spec__2___redArg___boxed(
    mut v_val_1316_: *mut crate::leanh::LeanObject,
    mut v_fst_1317_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1318_: *mut crate::leanh::LeanObject,
    mut v_b_1319_: *mut crate::leanh::LeanObject,
    mut v___y_1320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1321_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(
        v_val_1316_,
        v_fst_1317_,
        v_as_x27_1318_,
        v_b_1319_,
    );
    crate::leanh::lean_dec(v_as_x27_1318_);
    crate::leanh::lean_dec(v_val_1316_);
    return v_res_1321_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4(
    mut v___y_1323_: u8,
    mut v_as_1324_: *mut crate::leanh::LeanObject,
    mut v_sz_1325_: usize,
    mut v_i_1326_: usize,
    mut v_b_1327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1329_: u8 = 0;
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1344_: u8 = 0;
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1348_: u8 = 0;
    let mut v_unused_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: usize = 0;
    let mut v___x_1351_: usize = 0;
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1329_ = lean_usize_dec_lt(v_i_1326_, v_sz_1325_);
                if v___x_1329_ == 0 {
                    v___x_1330_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1330_, 0, v_b_1327_);
                    return v___x_1330_;
                } else {
                    v_a_1331_ = lean_array_uget_borrowed(v_as_1324_, v_i_1326_);
                    v_fst_1332_ = crate::leanh::lean_ctor_get(v_a_1331_, 0);
                    v_snd_1333_ = crate::leanh::lean_ctor_get(v_a_1331_, 1);
                    v___x_1334_ = crate::leanh::lean_box(0);
                    if v___y_1323_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_1353_ =
                            l_List_forIn_x27_loop___at___00main_spec__5___redArg___closed__0;
                        crate::leanh::lean_inc(v_fst_1332_);
                        v___x_1354_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_fst_1332_,
                                v___y_1323_,
                            );
                        v___x_1355_ = lean_string_append(v___x_1353_, v___x_1354_);
                        crate::leanh::lean_dec_ref(v___x_1354_);
                        v___x_1356_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v___x_1355_);
                        if crate::leanh::lean_obj_tag(v___x_1356_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1356_, 1);
                            state = 1;
                            continue;
                        } else {
                            return v___x_1356_;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_snd_1333_);
                v___x_1336_ = lean_task_get_own(v_snd_1333_);
                if crate::leanh::lean_obj_tag(v___x_1336_) == 0 {
                    v_a_1337_ = crate::leanh::lean_ctor_get(v___x_1336_, 0);
                    crate::leanh::lean_inc(v_a_1337_);
                    crate::leanh::lean_dec_ref_known(v___x_1336_, 1);
                    v___x_1338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__0;
                    crate::leanh::lean_inc(v_fst_1332_);
                    v___x_1339_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_fst_1332_,
                        v___x_1329_,
                    );
                    v___x_1340_ = lean_string_append(v___x_1338_, v___x_1339_);
                    crate::leanh::lean_dec_ref(v___x_1339_);
                    v___x_1341_ =
                        l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(
                            v___x_1340_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1341_) == 0 {
                        v_isSharedCheck_1348_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1341_)) as u8;
                        if v_isSharedCheck_1348_ == 0 {
                            v_unused_1349_ = crate::leanh::lean_ctor_get(v___x_1341_, 0);
                            crate::leanh::lean_dec(v_unused_1349_);
                            v___x_1343_ = v___x_1341_;
                            v_isShared_1344_ = v_isSharedCheck_1348_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1341_);
                            v___x_1343_ = crate::leanh::lean_box(0);
                            v_isShared_1344_ = v_isSharedCheck_1348_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1337_);
                        return v___x_1341_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1336_);
                    v___x_1350_ = 1usize;
                    v___x_1351_ = lean_usize_add(v_i_1326_, v___x_1350_);
                    v_i_1326_ = v___x_1351_;
                    v_b_1327_ = v___x_1334_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v_isShared_1344_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1343_, 1);
                    crate::leanh::lean_ctor_set(v___x_1343_, 0, v_a_1337_);
                    v___x_1346_ = v___x_1343_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1347_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1337_);
                    v___x_1346_ = v_reuseFailAlloc_1347_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1346_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___boxed(
    mut v___y_1357_: *mut crate::leanh::LeanObject,
    mut v_as_1358_: *mut crate::leanh::LeanObject,
    mut v_sz_1359_: *mut crate::leanh::LeanObject,
    mut v_i_1360_: *mut crate::leanh::LeanObject,
    mut v_b_1361_: *mut crate::leanh::LeanObject,
    mut v___y_1362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5687__boxed_1363_: u8 = 0;
    let mut v_sz_boxed_1364_: usize = 0;
    let mut v_i_boxed_1365_: usize = 0;
    let mut v_res_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_5687__boxed_1363_ = (crate::leanh::lean_unbox(v___y_1357_) as u8);
    v_sz_boxed_1364_ = crate::leanh::lean_unbox_usize(v_sz_1359_);
    crate::leanh::lean_dec(v_sz_1359_);
    v_i_boxed_1365_ = crate::leanh::lean_unbox_usize(v_i_1360_);
    crate::leanh::lean_dec(v_i_1360_);
    v_res_1366_ =
        l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4(
            v___y_5687__boxed_1363_,
            v_as_1358_,
            v_sz_boxed_1364_,
            v_i_boxed_1365_,
            v_b_1361_,
        );
    crate::leanh::lean_dec_ref(v_as_1358_);
    return v_res_1366_;
}
pub unsafe fn _init_l_main___boxed__const__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1375_: u32 = 0;
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1375_ = 0;
    v___x_1376_ = crate::leanh::lean_box_uint32(v___x_1375_);
    return v___x_1376_;
}
pub unsafe fn _lean_main(
    mut v_args_1377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1393_: u8 = 0;
    let mut v___f_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1396_: u8 = 0;
    let mut v_targets_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1404_: u8 = 0;
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: u8 = 0;
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1411_: usize = 0;
    let mut v___x_1412_: usize = 0;
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1417_: u8 = 0;
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1421_: u8 = 0;
    let mut v_a_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1425_: u8 = 0;
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1429_: u8 = 0;
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: u8 = 0;
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1445_: u8 = 0;
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1449_: u8 = 0;
    let mut v_isSharedCheck_1450_: u8 = 0;
    let mut v_a_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1454_: u8 = 0;
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1458_: u8 = 0;
    let mut v___y_1460_: u8 = 0;
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1469_: u8 = 0;
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1473_: u8 = 0;
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1479_: u8 = 0;
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1483_: u8 = 0;
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: u8 = 0;
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: u8 = 0;
    let mut v_isSharedCheck_1488_: u8 = 0;
    let mut v_a_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1492_: u8 = 0;
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1496_: u8 = 0;
    let mut v_a_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1500_: u8 = 0;
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1504_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1382_ = l_main___closed__0;
                v___x_1383_ = l_Lean_findSysroot(v___x_1382_);
                if crate::leanh::lean_obj_tag(v___x_1383_) == 0 {
                    v_a_1384_ = crate::leanh::lean_ctor_get(v___x_1383_, 0);
                    crate::leanh::lean_inc(v_a_1384_);
                    crate::leanh::lean_dec_ref_known(v___x_1383_, 1);
                    v___x_1385_ = crate::leanh::lean_box(0);
                    v___x_1386_ = l_Lean_initSearchPath(v_a_1384_, v___x_1385_);
                    if crate::leanh::lean_obj_tag(v___x_1386_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1386_, 1);
                        v___x_1387_ = l_main___closed__1;
                        v___x_1388_ =
                            l_List_partition_loop___at___00main_spec__0(v_args_1377_, v___x_1387_);
                        v_fst_1389_ = crate::leanh::lean_ctor_get(v___x_1388_, 0);
                        v_snd_1390_ = crate::leanh::lean_ctor_get(v___x_1388_, 1);
                        v_isSharedCheck_1488_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1388_)) as u8;
                        if v_isSharedCheck_1488_ == 0 {
                            v___x_1392_ = v___x_1388_;
                            v_isShared_1393_ = v_isSharedCheck_1488_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1390_);
                            crate::leanh::lean_inc(v_fst_1389_);
                            crate::leanh::lean_dec(v___x_1388_);
                            v___x_1392_ = crate::leanh::lean_box(0);
                            v_isShared_1393_ = v_isSharedCheck_1488_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_args_1377_);
                        v_a_1489_ = crate::leanh::lean_ctor_get(v___x_1386_, 0);
                        v_isSharedCheck_1496_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1386_)) as u8;
                        if v_isSharedCheck_1496_ == 0 {
                            v___x_1491_ = v___x_1386_;
                            v_isShared_1492_ = v_isSharedCheck_1496_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1489_);
                            crate::leanh::lean_dec(v___x_1386_);
                            v___x_1491_ = crate::leanh::lean_box(0);
                            v_isShared_1492_ = v_isSharedCheck_1496_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_args_1377_);
                    v_a_1497_ = crate::leanh::lean_ctor_get(v___x_1383_, 0);
                    v_isSharedCheck_1504_ = (!crate::leanh::lean_is_exclusive(v___x_1383_)) as u8;
                    if v_isSharedCheck_1504_ == 0 {
                        v___x_1499_ = v___x_1383_;
                        v_isShared_1500_ = v_isSharedCheck_1504_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1497_);
                        crate::leanh::lean_dec(v___x_1383_);
                        v___x_1499_ = crate::leanh::lean_box(0);
                        v_isShared_1500_ = v_isSharedCheck_1504_;
                        state = 22;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1380_ = l_main___boxed__const__1;
                v___x_1381_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1381_, 0, v___x_1380_);
                return v___x_1381_;
            }
            2 => {
                v___f_1394_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__0);
                v___x_1484_ = l_main___closed__4;
                crate::leanh::lean_inc(v_fst_1389_);
                v___x_1485_ = l_List_elem___redArg(v___f_1394_, v___x_1484_, v_fst_1389_);
                if v___x_1485_ == 0 {
                    v___x_1486_ = l_main___closed__5;
                    crate::leanh::lean_inc(v_fst_1389_);
                    v___x_1487_ = l_List_elem___redArg(v___f_1394_, v___x_1486_, v_fst_1389_);
                    v___y_1460_ = v___x_1487_;
                    state = 14;
                    continue;
                } else {
                    v___y_1460_ = v___x_1485_;
                    state = 14;
                    continue;
                }
            }
            3 => {
                v___x_1398_ = l_Lean_searchPathRef;
                v___x_1399_ = lean_st_ref_get(v___x_1398_);
                crate::leanh::lean_inc(v_fst_1389_);
                v___x_1400_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(
                    v___x_1399_,
                    v_fst_1389_,
                    v_targets_1397_,
                    v___x_1385_,
                );
                crate::leanh::lean_dec(v_targets_1397_);
                crate::leanh::lean_dec(v___x_1399_);
                if crate::leanh::lean_obj_tag(v___x_1400_) == 0 {
                    v_a_1401_ = crate::leanh::lean_ctor_get(v___x_1400_, 0);
                    v_isSharedCheck_1450_ = (!crate::leanh::lean_is_exclusive(v___x_1400_)) as u8;
                    if v_isSharedCheck_1450_ == 0 {
                        v___x_1403_ = v___x_1400_;
                        v_isShared_1404_ = v_isSharedCheck_1450_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1401_);
                        crate::leanh::lean_dec(v___x_1400_);
                        v___x_1403_ = crate::leanh::lean_box(0);
                        v_isShared_1404_ = v_isSharedCheck_1450_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_1389_);
                    v_a_1451_ = crate::leanh::lean_ctor_get(v___x_1400_, 0);
                    v_isSharedCheck_1458_ = (!crate::leanh::lean_is_exclusive(v___x_1400_)) as u8;
                    if v_isSharedCheck_1458_ == 0 {
                        v___x_1453_ = v___x_1400_;
                        v_isShared_1454_ = v_isSharedCheck_1458_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1451_);
                        crate::leanh::lean_dec(v___x_1400_);
                        v___x_1453_ = crate::leanh::lean_box(0);
                        v_isShared_1454_ = v_isSharedCheck_1458_;
                        state = 12;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__1___closed__1;
                v___x_1406_ = l_List_elem___redArg(v___f_1394_, v___x_1405_, v_fst_1389_);
                if v___x_1406_ == 0 {
                    crate::leanh::lean_del_object(v___x_1403_);
                    v___x_1407_ = l_main___closed__2;
                    v___x_1408_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(
                        v_a_1401_,
                        v___x_1407_,
                    );
                    crate::leanh::lean_dec(v_a_1401_);
                    if crate::leanh::lean_obj_tag(v___x_1408_) == 0 {
                        v_a_1409_ = crate::leanh::lean_ctor_get(v___x_1408_, 0);
                        crate::leanh::lean_inc(v_a_1409_);
                        crate::leanh::lean_dec_ref_known(v___x_1408_, 1);
                        v___x_1410_ = crate::leanh::lean_box(0);
                        v_sz_1411_ = lean_array_size(v_a_1409_);
                        v___x_1412_ = 0usize;
                        v___x_1413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4(v___y_1396_, v_a_1409_, v_sz_1411_, v___x_1412_, v___x_1410_);
                        crate::leanh::lean_dec(v_a_1409_);
                        if crate::leanh::lean_obj_tag(v___x_1413_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1413_, 1);
                            state = 1;
                            continue;
                        } else {
                            v_a_1414_ = crate::leanh::lean_ctor_get(v___x_1413_, 0);
                            v_isSharedCheck_1421_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1413_)) as u8;
                            if v_isSharedCheck_1421_ == 0 {
                                v___x_1416_ = v___x_1413_;
                                v_isShared_1417_ = v_isSharedCheck_1421_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1414_);
                                crate::leanh::lean_dec(v___x_1413_);
                                v___x_1416_ = crate::leanh::lean_box(0);
                                v_isShared_1417_ = v_isSharedCheck_1421_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v_a_1422_ = crate::leanh::lean_ctor_get(v___x_1408_, 0);
                        v_isSharedCheck_1429_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1408_)) as u8;
                        if v_isSharedCheck_1429_ == 0 {
                            v___x_1424_ = v___x_1408_;
                            v_isShared_1425_ = v_isSharedCheck_1429_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1422_);
                            crate::leanh::lean_dec(v___x_1408_);
                            v___x_1424_ = crate::leanh::lean_box(0);
                            v_isShared_1425_ = v_isSharedCheck_1429_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v___x_1430_ = l_List_lengthTR___redArg(v_a_1401_);
                    v___x_1431_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1432_ = lean_nat_dec_eq(v___x_1430_, v___x_1431_);
                    crate::leanh::lean_dec(v___x_1430_);
                    if v___x_1432_ == 0 {
                        v___x_1433_ = l_main___closed__3;
                        v___x_1434_ = l_List_toString___at___00Lean_Environment_AddConstAsyncResult_commitConst_spec__1(v_a_1401_);
                        v___x_1435_ = lean_string_append(v___x_1433_, v___x_1434_);
                        crate::leanh::lean_dec_ref(v___x_1434_);
                        v___x_1436_ = crate::leanh::lean_alloc_ctor(18, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1436_, 0, v___x_1435_);
                        if v_isShared_1404_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_1403_, 1);
                            crate::leanh::lean_ctor_set(v___x_1403_, 0, v___x_1436_);
                            v___x_1438_ = v___x_1403_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_1439_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
                            v___x_1438_ = v_reuseFailAlloc_1439_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1403_);
                        v___x_1440_ = crate::leanh::lean_box(0);
                        v___x_1441_ = l_List_forIn_x27_loop___at___00main_spec__5___redArg(
                            v___y_1396_,
                            v_a_1401_,
                            v___x_1440_,
                        );
                        crate::leanh::lean_dec(v_a_1401_);
                        if crate::leanh::lean_obj_tag(v___x_1441_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1441_, 1);
                            state = 1;
                            continue;
                        } else {
                            v_a_1442_ = crate::leanh::lean_ctor_get(v___x_1441_, 0);
                            v_isSharedCheck_1449_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1441_)) as u8;
                            if v_isSharedCheck_1449_ == 0 {
                                v___x_1444_ = v___x_1441_;
                                v_isShared_1445_ = v_isSharedCheck_1449_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1442_);
                                crate::leanh::lean_dec(v___x_1441_);
                                v___x_1444_ = crate::leanh::lean_box(0);
                                v_isShared_1445_ = v_isSharedCheck_1449_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                }
            }
            5 => {
                if v_isShared_1417_ == 0 {
                    v___x_1419_ = v___x_1416_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1420_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
                    v___x_1419_ = v_reuseFailAlloc_1420_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1419_;
            }
            7 => {
                if v_isShared_1425_ == 0 {
                    v___x_1427_ = v___x_1424_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1428_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
                    v___x_1427_ = v_reuseFailAlloc_1428_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1427_;
            }
            9 => {
                return v___x_1438_;
            }
            10 => {
                if v_isShared_1445_ == 0 {
                    v___x_1447_ = v___x_1444_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1448_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
                    v___x_1447_ = v_reuseFailAlloc_1448_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1447_;
            }
            12 => {
                if v_isShared_1454_ == 0 {
                    v___x_1456_ = v___x_1453_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1457_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
                    v___x_1456_ = v_reuseFailAlloc_1457_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1456_;
            }
            14 => {
                if crate::leanh::lean_obj_tag(v_snd_1390_) == 0 {
                    v___x_1461_ = l_getCurrentModule();
                    if crate::leanh::lean_obj_tag(v___x_1461_) == 0 {
                        v_a_1462_ = crate::leanh::lean_ctor_get(v___x_1461_, 0);
                        crate::leanh::lean_inc(v_a_1462_);
                        crate::leanh::lean_dec_ref_known(v___x_1461_, 1);
                        if v_isShared_1393_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_1392_, 1);
                            crate::leanh::lean_ctor_set(v___x_1392_, 1, v___x_1385_);
                            crate::leanh::lean_ctor_set(v___x_1392_, 0, v_a_1462_);
                            v___x_1464_ = v___x_1392_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_1465_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1462_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1465_, 1, v___x_1385_);
                            v___x_1464_ = v_reuseFailAlloc_1465_;
                            state = 15;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1392_);
                        crate::leanh::lean_dec(v_fst_1389_);
                        v_a_1466_ = crate::leanh::lean_ctor_get(v___x_1461_, 0);
                        v_isSharedCheck_1473_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1461_)) as u8;
                        if v_isSharedCheck_1473_ == 0 {
                            v___x_1468_ = v___x_1461_;
                            v_isShared_1469_ = v_isSharedCheck_1473_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1466_);
                            crate::leanh::lean_dec(v___x_1461_);
                            v___x_1468_ = crate::leanh::lean_box(0);
                            v_isShared_1469_ = v_isSharedCheck_1473_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1392_);
                    v___x_1474_ = l_List_mapM_loop___at___00main_spec__6(v_snd_1390_, v___x_1385_);
                    if crate::leanh::lean_obj_tag(v___x_1474_) == 0 {
                        v_a_1475_ = crate::leanh::lean_ctor_get(v___x_1474_, 0);
                        crate::leanh::lean_inc(v_a_1475_);
                        crate::leanh::lean_dec_ref_known(v___x_1474_, 1);
                        v___y_1396_ = v___y_1460_;
                        v_targets_1397_ = v_a_1475_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_fst_1389_);
                        v_a_1476_ = crate::leanh::lean_ctor_get(v___x_1474_, 0);
                        v_isSharedCheck_1483_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1474_)) as u8;
                        if v_isSharedCheck_1483_ == 0 {
                            v___x_1478_ = v___x_1474_;
                            v_isShared_1479_ = v_isSharedCheck_1483_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1476_);
                            crate::leanh::lean_dec(v___x_1474_);
                            v___x_1478_ = crate::leanh::lean_box(0);
                            v_isShared_1479_ = v_isSharedCheck_1483_;
                            state = 18;
                            continue;
                        }
                    }
                }
            }
            15 => {
                v___y_1396_ = v___y_1460_;
                v_targets_1397_ = v___x_1464_;
                state = 3;
                continue;
            }
            16 => {
                if v_isShared_1469_ == 0 {
                    v___x_1471_ = v___x_1468_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1472_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
                    v___x_1471_ = v_reuseFailAlloc_1472_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1471_;
            }
            18 => {
                if v_isShared_1479_ == 0 {
                    v___x_1481_ = v___x_1478_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1482_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
                    v___x_1481_ = v_reuseFailAlloc_1482_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1481_;
            }
            20 => {
                if v_isShared_1492_ == 0 {
                    v___x_1494_ = v___x_1491_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1495_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
                    v___x_1494_ = v_reuseFailAlloc_1495_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1494_;
            }
            22 => {
                if v_isShared_1500_ == 0 {
                    v___x_1502_ = v___x_1499_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1503_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
                    v___x_1502_ = v_reuseFailAlloc_1503_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_1502_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_main___boxed(
    mut v_args_1505_: *mut crate::leanh::LeanObject,
    mut v_a_1506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1507_ = _lean_main(v_args_1505_);
    return v_res_1507_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00main_spec__2(
    mut v_val_1508_: *mut crate::leanh::LeanObject,
    mut v_fst_1509_: *mut crate::leanh::LeanObject,
    mut v_as_1510_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1511_: *mut crate::leanh::LeanObject,
    mut v_b_1512_: *mut crate::leanh::LeanObject,
    mut v_a_1513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1515_ = l_List_forIn_x27_loop___at___00main_spec__2___redArg(
        v_val_1508_,
        v_fst_1509_,
        v_as_x27_1511_,
        v_b_1512_,
    );
    return v___x_1515_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00main_spec__2___boxed(
    mut v_val_1516_: *mut crate::leanh::LeanObject,
    mut v_fst_1517_: *mut crate::leanh::LeanObject,
    mut v_as_1518_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1519_: *mut crate::leanh::LeanObject,
    mut v_b_1520_: *mut crate::leanh::LeanObject,
    mut v_a_1521_: *mut crate::leanh::LeanObject,
    mut v___y_1522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1523_ = l_List_forIn_x27_loop___at___00main_spec__2(
        v_val_1516_,
        v_fst_1517_,
        v_as_1518_,
        v_as_x27_1519_,
        v_b_1520_,
        v_a_1521_,
    );
    crate::leanh::lean_dec(v_as_x27_1519_);
    crate::leanh::lean_dec(v_as_1518_);
    crate::leanh::lean_dec(v_val_1516_);
    return v_res_1523_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00main_spec__3(
    mut v_as_1524_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1525_: *mut crate::leanh::LeanObject,
    mut v_b_1526_: *mut crate::leanh::LeanObject,
    mut v_a_1527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1529_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v_as_x27_1525_, v_b_1526_);
    return v___x_1529_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00main_spec__3___boxed(
    mut v_as_1530_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1531_: *mut crate::leanh::LeanObject,
    mut v_b_1532_: *mut crate::leanh::LeanObject,
    mut v_a_1533_: *mut crate::leanh::LeanObject,
    mut v___y_1534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1535_ = l_List_forIn_x27_loop___at___00main_spec__3(
        v_as_1530_,
        v_as_x27_1531_,
        v_b_1532_,
        v_a_1533_,
    );
    crate::leanh::lean_dec(v_as_x27_1531_);
    crate::leanh::lean_dec(v_as_1530_);
    return v_res_1535_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00main_spec__5(
    mut v___y_1536_: u8,
    mut v_as_1537_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1538_: *mut crate::leanh::LeanObject,
    mut v_b_1539_: *mut crate::leanh::LeanObject,
    mut v_a_1540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1542_ = l_List_forIn_x27_loop___at___00main_spec__5___redArg(
        v___y_1536_,
        v_as_x27_1538_,
        v_b_1539_,
    );
    return v___x_1542_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00main_spec__5___boxed(
    mut v___y_1543_: *mut crate::leanh::LeanObject,
    mut v_as_1544_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1545_: *mut crate::leanh::LeanObject,
    mut v_b_1546_: *mut crate::leanh::LeanObject,
    mut v_a_1547_: *mut crate::leanh::LeanObject,
    mut v___y_1548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6062__boxed_1549_: u8 = 0;
    let mut v_res_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_6062__boxed_1549_ = (crate::leanh::lean_unbox(v___y_1543_) as u8);
    v_res_1550_ = l_List_forIn_x27_loop___at___00main_spec__5(
        v___y_6062__boxed_1549_,
        v_as_1544_,
        v_as_x27_1545_,
        v_b_1546_,
        v_a_1547_,
    );
    crate::leanh::lean_dec(v_as_x27_1545_);
    crate::leanh::lean_dec(v_as_1544_);
    return v_res_1550_;
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_LeanChecker(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_CoreM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Replay(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Load_Manifest(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_main___boxed__const__1 = _init_l_main___boxed__const__1();
    crate::leanh::lean_mark_persistent(l_main___boxed__const__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
unsafe fn run_main(
    argc: core::ffi::c_int,
    argv: *mut *mut core::ffi::c_char,
) -> *mut crate::leanh::LeanObject {
    let mut args_list = crate::leanh::lean_box(0);
    let mut i = argc;
    while i > 1 {
        i -= 1;
        let arg_str = crate::leanh::lean_mk_string(*argv.add(i as usize));
        let mut fields = [arg_str, args_list];
        args_list = crate::leanh::lean_alloc_ctor(1, 2, 0);
        crate::leanh::lean_ctor_set(args_list, 0, arg_str);
        crate::leanh::lean_ctor_set(args_list, 1, fields[1]);
    }
    return _lean_main(args_list);
}
unsafe fn lean_rust_main(
    argc: core::ffi::c_int,
    mut argv: *mut *mut core::ffi::c_char,
) -> core::ffi::c_int {
    argv = crate::leanh::lean_setup_args(argc, argv);
    crate::leanh::lean_initialize();
    let res = initialize_LeanChecker(1 /* builtin */);
    crate::leanh::lean_io_mark_end_initialization();
    let mut ret_val = 1;
    if crate::leanh::lean_io_result_is_ok(res) {
        crate::leanh::lean_dec(res);
        crate::leanh::lean_init_task_manager();
        let main_res = crate::leanh::lean_run_main(run_main, argc, argv);
        crate::leanh::lean_finalize_task_manager();
        if crate::leanh::lean_io_result_is_ok(main_res) {
            ret_val =
                crate::leanh::lean_unbox_uint32(crate::leanh::lean_io_result_get_value(main_res))
                    as i32;
            crate::leanh::lean_dec(main_res);
        } else {
            crate::leanh::lean_io_result_show_error(main_res);
            crate::leanh::lean_dec(main_res);
        }
    } else {
        crate::leanh::lean_io_result_show_error(res);
        crate::leanh::lean_dec(res);
    }
    return ret_val;
}

fn main() {
    let c_args: Vec<std::ffi::CString> = std::env::args()
        .map(|arg| std::ffi::CString::new(arg).expect("process argument contains NUL byte"))
        .collect();
    let mut raw_args: Vec<*mut core::ffi::c_char> = c_args
        .iter()
        .map(|arg| arg.as_ptr() as *mut core::ffi::c_char)
        .collect();
    let argc = raw_args.len() as core::ffi::c_int;
    let code = unsafe { lean_rust_main(argc, raw_args.as_mut_ptr()) };
    std::process::exit(code);
}
