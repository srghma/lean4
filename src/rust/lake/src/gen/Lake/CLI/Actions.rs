// Lean compiler output
// Module: Lake.CLI.Actions
// Imports: Lake.Config.Workspace Lake.Build.Run Lake.Build.Actions Lake.Build.Targets Lake.Build.Module Lake.Util.Proc
use crate::ffi::{
    lean_array_get_size, lean_array_mk, lean_array_push, lean_array_size, lean_array_to_list,
    lean_array_uget_borrowed, lean_io_process_child_wait, lean_io_process_spawn,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_sub,
    lean_string_append, lean_string_utf8_byte_size, lean_string_utf8_get_fast,
    lean_string_utf8_next_fast, lean_uint32_dec_eq, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::List::Basic::{l_List_appendTR___redArg, l_List_isEmpty___redArg};
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_toString;
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Meta::Defs::l_String_toName;
use crate::r#gen::Init::System::FilePath::l_System_FilePath_normalize;
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Lake::Build::Actions::{
    initialize_Lake_Build_Actions, l_Lake_tar, l_Lake_untar, runtime_initialize_Lake_Build_Actions,
};
use crate::r#gen::Lake::Build::Facets::{l_Lake_LeanExe_exeFacet, l_Lake_LeanLib_defaultFacet};
use crate::r#gen::Lake::Build::Module::{
    initialize_Lake_Build_Module, l_Lake_prepareLeanCommand___boxed,
    runtime_initialize_Lake_Build_Module,
};
use crate::r#gen::Lake::Build::Run::{
    initialize_Lake_Build_Run, l_Lake_Workspace_runBuild___redArg,
    runtime_initialize_Lake_Build_Run,
};
use crate::r#gen::Lake::Build::Targets::{
    initialize_Lake_Build_Targets, runtime_initialize_Lake_Build_Targets,
};
use crate::r#gen::Lake::Config::Defaults::l_Lake_defaultLakeDir;
use crate::r#gen::Lake::Config::Kinds::l_Lake_LeanExe_keyword;
use crate::r#gen::Lake::Config::Package::l_Lake_Package_findTargetDecl_x3f;
use crate::r#gen::Lake::Config::Script::l_Lake_Script_run;
use crate::r#gen::Lake::Config::Workspace::{
    initialize_Lake_Config_Workspace, l_Lake_Workspace_augmentedEnvVars,
    l_Lake_Workspace_findLeanExe_x3f, runtime_initialize_Lake_Config_Workspace,
};
use crate::r#gen::Lake::Util::FilePath::l_Lake_joinRelative;
use crate::r#gen::Lake::Util::Proc::{
    initialize_Lake_Util_Proc, l_Lake_proc, runtime_initialize_Lake_Util_Proc,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
pub static l_Lake_env___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [65793 as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_env___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_env___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_exe___closed__0_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            117, 110, 107, 110, 111, 119, 110, 32, 101, 120, 101, 99, 117, 116, 97, 98, 108, 101,
            32, 96, 0,
        ],
    };
static mut l_Lake_exe___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_exe___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_exe___closed__1_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [96, 0],
    };
static mut l_Lake_exe___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_exe___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_pack___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [112, 97, 99, 107, 105, 110, 103, 32, 0],
    };
static mut l_Lake_Package_pack___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_pack___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_pack___closed__1_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lake_Package_pack___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_pack___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_unpack___closed__0_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [117, 110, 112, 97, 99, 107, 105, 110, 103, 32, 0],
    };
static mut l_Lake_Package_unpack___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_unpack___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_uploadRelease___closed__0_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [103, 104, 0],
    };
static mut l_Lake_Package_uploadRelease___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_uploadRelease___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_uploadRelease___closed__1_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lake_Package_uploadRelease___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_uploadRelease___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_uploadRelease___closed__2_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [117, 112, 108, 111, 97, 100, 105, 110, 103, 32, 0],
    };
static mut l_Lake_Package_uploadRelease___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_uploadRelease___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_uploadRelease___closed__3_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [58, 0],
    };
static mut l_Lake_Package_uploadRelease___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_uploadRelease___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_uploadRelease___closed__4_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [114, 101, 108, 101, 97, 115, 101, 0],
    };
static mut l_Lake_Package_uploadRelease___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_uploadRelease___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_uploadRelease___closed__5_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [117, 112, 108, 111, 97, 100, 0],
    };
static mut l_Lake_Package_uploadRelease___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_uploadRelease___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_uploadRelease___closed__6_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [45, 45, 99, 108, 111, 98, 98, 101, 114, 0],
    };
static mut l_Lake_Package_uploadRelease___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_uploadRelease___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_Package_uploadRelease___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Package_uploadRelease___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Package_uploadRelease___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Package_uploadRelease___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Package_uploadRelease___closed__9_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [45, 82, 0],
    };
static mut l_Lake_Package_uploadRelease___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_uploadRelease___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_Package_uploadRelease___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Package_uploadRelease___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_resolveDriver___closed__0_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [58, 32, 105, 110, 118, 97, 108, 105, 100, 32, 0],
    };
static mut l_Lake_Package_resolveDriver___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_resolveDriver___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_resolveDriver___closed__1_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [32, 100, 114, 105, 118, 101, 114, 32, 39, 0],
    };
static mut l_Lake_Package_resolveDriver___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_resolveDriver___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_resolveDriver___closed__2_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
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
            39, 32, 40, 116, 111, 111, 32, 109, 97, 110, 121, 32, 39, 47, 39, 41, 0,
        ],
    };
static mut l_Lake_Package_resolveDriver___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_resolveDriver___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_resolveDriver___closed__3_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [58, 32, 117, 110, 107, 110, 111, 119, 110, 32, 0],
    };
static mut l_Lake_Package_resolveDriver___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_resolveDriver___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_resolveDriver___closed__4_value: crate::leanh::LeanStringObject<18> =
    crate::leanh::LeanStringObject {
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
            32, 100, 114, 105, 118, 101, 114, 32, 112, 97, 99, 107, 97, 103, 101, 32, 39, 0,
        ],
    };
static mut l_Lake_Package_resolveDriver___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_resolveDriver___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_resolveDriver___closed__5_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_Package_resolveDriver___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_resolveDriver___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_resolveDriver___closed__6_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [58, 32, 110, 111, 32, 0],
    };
static mut l_Lake_Package_resolveDriver___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_resolveDriver___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_resolveDriver___closed__7_value: crate::leanh::LeanStringObject<19> =
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
            32, 100, 114, 105, 118, 101, 114, 32, 99, 111, 110, 102, 105, 103, 117, 114, 101, 100,
            0,
        ],
    };
static mut l_Lake_Package_resolveDriver___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_resolveDriver___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_test___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [116, 101, 115, 116, 0],
    };
static mut l_Lake_Package_test___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_test___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_test___closed__1_value: crate::leanh::LeanStringObject<54> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 54,
        m_capacity: 54,
        m_length: 53,
        m_data: [
            58, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 32, 99, 97, 110, 110, 111, 116, 32,
            98, 101, 32, 112, 97, 115, 115, 101, 100, 32, 116, 111, 32, 97, 32, 108, 105, 98, 114,
            97, 114, 121, 32, 116, 101, 115, 116, 32, 100, 114, 105, 118, 101, 114, 0,
        ],
    };
static mut l_Lake_Package_test___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_test___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_test___closed__2_value: crate::leanh::LeanStringObject<64> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 64,
        m_capacity: 64,
        m_length: 63,
        m_data: [
            58, 32, 105, 110, 118, 97, 108, 105, 100, 32, 116, 101, 115, 116, 32, 100, 114, 105,
            118, 101, 114, 58, 32, 117, 110, 107, 110, 111, 119, 110, 32, 115, 99, 114, 105, 112,
            116, 44, 32, 101, 120, 101, 99, 117, 116, 97, 98, 108, 101, 44, 32, 111, 114, 32, 108,
            105, 98, 114, 97, 114, 121, 32, 39, 0,
        ],
    };
static mut l_Lake_Package_test___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_test___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_test___closed__3_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [108, 101, 97, 110, 95, 108, 105, 98, 0],
    };
static mut l_Lake_Package_test___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_test___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_test___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_Package_test___closed__3_value)
                as *mut crate::leanh::LeanObject,
            12295998048739818339 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_test___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_test___closed__4_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Package_test___boxed__const__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Package_lint___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [108, 105, 110, 116, 0],
    };
static mut l_Lake_Package_lint___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_lint___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_lint___closed__1_value: crate::leanh::LeanStringObject<54> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 54,
        m_capacity: 54,
        m_length: 53,
        m_data: [
            58, 32, 105, 110, 118, 97, 108, 105, 100, 32, 108, 105, 110, 116, 32, 100, 114, 105,
            118, 101, 114, 58, 32, 117, 110, 107, 110, 111, 119, 110, 32, 115, 99, 114, 105, 112,
            116, 32, 111, 114, 32, 101, 120, 101, 99, 117, 116, 97, 98, 108, 101, 32, 39, 0,
        ],
    };
static mut l_Lake_Package_lint___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_lint___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_env(
    mut v_cmd_713_: *mut crate::leanh::LeanObject,
    mut v_args_714_: *mut crate::leanh::LeanObject,
    mut v_a_715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: u8 = 0;
    let mut v___x_721_: u8 = 0;
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_729_: u8 = 0;
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_733_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_715_);
                v___x_717_ = l_Lake_Workspace_augmentedEnvVars(v_a_715_);
                v___x_718_ = l_Lake_env___closed__0;
                v___x_719_ = crate::leanh::lean_box(0);
                v___x_720_ = 1;
                v___x_721_ = 0;
                v___x_722_ = crate::leanh::lean_alloc_ctor(0, 5, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_722_, 0, v___x_718_);
                crate::leanh::lean_ctor_set(v___x_722_, 1, v_cmd_713_);
                crate::leanh::lean_ctor_set(v___x_722_, 2, v_args_714_);
                crate::leanh::lean_ctor_set(v___x_722_, 3, v___x_719_);
                crate::leanh::lean_ctor_set(v___x_722_, 4, v___x_717_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_722_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___x_720_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_722_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_721_,
                );
                v___x_723_ = lean_io_process_spawn(v___x_722_);
                if crate::leanh::lean_obj_tag(v___x_723_) == 0 {
                    v_a_724_ = crate::leanh::lean_ctor_get(v___x_723_, 0);
                    crate::leanh::lean_inc(v_a_724_);
                    crate::leanh::lean_dec_ref_known(v___x_723_, 1);
                    v___x_725_ = lean_io_process_child_wait(v___x_718_, v_a_724_);
                    crate::leanh::lean_dec(v_a_724_);
                    return v___x_725_;
                } else {
                    v_a_726_ = crate::leanh::lean_ctor_get(v___x_723_, 0);
                    v_isSharedCheck_733_ = (!crate::leanh::lean_is_exclusive(v___x_723_)) as u8;
                    if v_isSharedCheck_733_ == 0 {
                        v___x_728_ = v___x_723_;
                        v_isShared_729_ = v_isSharedCheck_733_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_726_);
                        crate::leanh::lean_dec(v___x_723_);
                        v___x_728_ = crate::leanh::lean_box(0);
                        v_isShared_729_ = v_isSharedCheck_733_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_729_ == 0 {
                    v___x_731_ = v___x_728_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_732_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
                    v___x_731_ = v_reuseFailAlloc_732_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_env___boxed(
    mut v_cmd_734_: *mut crate::leanh::LeanObject,
    mut v_args_735_: *mut crate::leanh::LeanObject,
    mut v_a_736_: *mut crate::leanh::LeanObject,
    mut v_a_737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_738_ = l_Lake_env(v_cmd_734_, v_args_735_, v_a_736_);
    crate::leanh::lean_dec(v_a_736_);
    return v_res_738_;
}
pub unsafe fn l_Lake_exe___lam__0(
    mut v_val_739_: *mut crate::leanh::LeanObject,
    mut v___y_740_: *mut crate::leanh::LeanObject,
    mut v___y_741_: *mut crate::leanh::LeanObject,
    mut v___y_742_: *mut crate::leanh::LeanObject,
    mut v___y_743_: *mut crate::leanh::LeanObject,
    mut v___y_744_: *mut crate::leanh::LeanObject,
    mut v___y_745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkg_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkg_747_ = crate::leanh::lean_ctor_get(v_val_739_, 0);
    v_name_748_ = crate::leanh::lean_ctor_get(v_val_739_, 1);
    v_keyName_749_ = crate::leanh::lean_ctor_get(v_pkg_747_, 2);
    v___x_750_ = l_Lake_LeanExe_exeFacet;
    crate::leanh::lean_inc(v_name_748_);
    crate::leanh::lean_inc(v_keyName_749_);
    v___x_751_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_751_, 0, v_keyName_749_);
    crate::leanh::lean_ctor_set(v___x_751_, 1, v_name_748_);
    v___x_752_ = l_Lake_LeanExe_keyword;
    v___x_753_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_753_, 0, v___x_751_);
    crate::leanh::lean_ctor_set(v___x_753_, 1, v___x_752_);
    crate::leanh::lean_ctor_set(v___x_753_, 2, v_val_739_);
    crate::leanh::lean_ctor_set(v___x_753_, 3, v___x_750_);
    v___x_754_ = crate::leanh::lean_apply_7(
        v___y_740_,
        v___x_753_,
        v___y_741_,
        v___y_742_,
        v___y_743_,
        v___y_744_,
        v___y_745_,
        crate::leanh::lean_box(0),
    );
    return v___x_754_;
}
pub unsafe fn l_Lake_exe___lam__0___boxed(
    mut v_val_755_: *mut crate::leanh::LeanObject,
    mut v___y_756_: *mut crate::leanh::LeanObject,
    mut v___y_757_: *mut crate::leanh::LeanObject,
    mut v___y_758_: *mut crate::leanh::LeanObject,
    mut v___y_759_: *mut crate::leanh::LeanObject,
    mut v___y_760_: *mut crate::leanh::LeanObject,
    mut v___y_761_: *mut crate::leanh::LeanObject,
    mut v___y_762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_763_ = l_Lake_exe___lam__0(
        v_val_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_,
    );
    return v_res_763_;
}
pub unsafe fn l_Lake_exe(
    mut v_name_766_: *mut crate::leanh::LeanObject,
    mut v_args_767_: *mut crate::leanh::LeanObject,
    mut v_buildConfig_768_: *mut crate::leanh::LeanObject,
    mut v_a_769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_780_: u8 = 0;
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_784_: u8 = 0;
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: u8 = 0;
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_771_ = l_Lake_Workspace_findLeanExe_x3f(v_name_766_, v_a_769_);
                if crate::leanh::lean_obj_tag(v___x_771_) == 1 {
                    crate::leanh::lean_dec(v_name_766_);
                    v_val_772_ = crate::leanh::lean_ctor_get(v___x_771_, 0);
                    crate::leanh::lean_inc(v_val_772_);
                    crate::leanh::lean_dec_ref_known(v___x_771_, 1);
                    v___f_773_ = crate::leanh::lean_alloc_closure(
                        l_Lake_exe___lam__0___boxed as *mut core::ffi::c_void,
                        8,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_773_, 0, v_val_772_);
                    crate::leanh::lean_inc(v_a_769_);
                    v___x_774_ = l_Lake_Workspace_runBuild___redArg(
                        v_a_769_,
                        v___f_773_,
                        v_buildConfig_768_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_774_) == 0 {
                        v_a_775_ = crate::leanh::lean_ctor_get(v___x_774_, 0);
                        crate::leanh::lean_inc(v_a_775_);
                        crate::leanh::lean_dec_ref_known(v___x_774_, 1);
                        v___x_776_ = l_Lake_env(v_a_775_, v_args_767_, v_a_769_);
                        return v___x_776_;
                    } else {
                        crate::leanh::lean_dec_ref(v_args_767_);
                        v_a_777_ = crate::leanh::lean_ctor_get(v___x_774_, 0);
                        v_isSharedCheck_784_ = (!crate::leanh::lean_is_exclusive(v___x_774_)) as u8;
                        if v_isSharedCheck_784_ == 0 {
                            v___x_779_ = v___x_774_;
                            v_isShared_780_ = v_isSharedCheck_784_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_777_);
                            crate::leanh::lean_dec(v___x_774_);
                            v___x_779_ = crate::leanh::lean_box(0);
                            v_isShared_780_ = v_isSharedCheck_784_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_771_);
                    crate::leanh::lean_dec_ref(v_buildConfig_768_);
                    crate::leanh::lean_dec_ref(v_args_767_);
                    v___x_785_ = l_Lake_exe___closed__0;
                    v___x_786_ = 1;
                    v___x_787_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_766_,
                        v___x_786_,
                    );
                    v___x_788_ = lean_string_append(v___x_785_, v___x_787_);
                    crate::leanh::lean_dec_ref(v___x_787_);
                    v___x_789_ = l_Lake_exe___closed__1;
                    v___x_790_ = lean_string_append(v___x_788_, v___x_789_);
                    v___x_791_ = lean_mk_io_user_error(v___x_790_);
                    v___x_792_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_792_, 0, v___x_791_);
                    return v___x_792_;
                }
            }
            1 => {
                if v_isShared_780_ == 0 {
                    v___x_782_ = v___x_779_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_783_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
                    v___x_782_ = v_reuseFailAlloc_783_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_782_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_exe___boxed(
    mut v_name_793_: *mut crate::leanh::LeanObject,
    mut v_args_794_: *mut crate::leanh::LeanObject,
    mut v_buildConfig_795_: *mut crate::leanh::LeanObject,
    mut v_a_796_: *mut crate::leanh::LeanObject,
    mut v_a_797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_798_ = l_Lake_exe(v_name_793_, v_args_794_, v_buildConfig_795_, v_a_796_);
    crate::leanh::lean_dec(v_a_796_);
    return v_res_798_;
}
pub unsafe fn l_Lake_Package_pack(
    mut v_pkg_802_: *mut crate::leanh::LeanObject,
    mut v_file_803_: *mut crate::leanh::LeanObject,
    mut v_a_804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: u8 = 0;
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: u8 = 0;
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_806_ = crate::leanh::lean_ctor_get(v_pkg_802_, 6);
    crate::leanh::lean_inc_ref(v_config_806_);
    v_dir_807_ = crate::leanh::lean_ctor_get(v_pkg_802_, 4);
    crate::leanh::lean_inc_ref(v_dir_807_);
    crate::leanh::lean_dec_ref(v_pkg_802_);
    v_buildDir_808_ = crate::leanh::lean_ctor_get(v_config_806_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_808_);
    crate::leanh::lean_dec_ref(v_config_806_);
    v___x_809_ = l_Lake_Package_pack___closed__0;
    v___x_810_ = lean_string_append(v___x_809_, v_file_803_);
    v___x_811_ = 1;
    v___x_812_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_812_, 0, v___x_810_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_812_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_811_,
    );
    v___x_813_ = lean_array_push(v_a_804_, v___x_812_);
    v___x_814_ = l_System_FilePath_normalize(v_buildDir_808_);
    v___x_815_ = l_Lake_joinRelative(v_dir_807_, v___x_814_);
    v___x_816_ = 1;
    v___x_817_ = l_Lake_Package_pack___closed__1;
    v___x_818_ = l_Lake_tar(v___x_815_, v_file_803_, v___x_816_, v___x_817_, v___x_813_);
    return v___x_818_;
}
pub unsafe fn l_Lake_Package_pack___boxed(
    mut v_pkg_819_: *mut crate::leanh::LeanObject,
    mut v_file_820_: *mut crate::leanh::LeanObject,
    mut v_a_821_: *mut crate::leanh::LeanObject,
    mut v_a_822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_823_ = l_Lake_Package_pack(v_pkg_819_, v_file_820_, v_a_821_);
    return v_res_823_;
}
pub unsafe fn l_Lake_Package_unpack(
    mut v_pkg_825_: *mut crate::leanh::LeanObject,
    mut v_file_826_: *mut crate::leanh::LeanObject,
    mut v_a_827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: u8 = 0;
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: u8 = 0;
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_829_ = crate::leanh::lean_ctor_get(v_pkg_825_, 6);
    crate::leanh::lean_inc_ref(v_config_829_);
    v_dir_830_ = crate::leanh::lean_ctor_get(v_pkg_825_, 4);
    crate::leanh::lean_inc_ref(v_dir_830_);
    crate::leanh::lean_dec_ref(v_pkg_825_);
    v_buildDir_831_ = crate::leanh::lean_ctor_get(v_config_829_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_831_);
    crate::leanh::lean_dec_ref(v_config_829_);
    v___x_832_ = l_Lake_Package_unpack___closed__0;
    v___x_833_ = lean_string_append(v___x_832_, v_file_826_);
    v___x_834_ = 1;
    v___x_835_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_835_, 0, v___x_833_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_835_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_834_,
    );
    v___x_836_ = lean_array_push(v_a_827_, v___x_835_);
    v___x_837_ = l_System_FilePath_normalize(v_buildDir_831_);
    v___x_838_ = l_Lake_joinRelative(v_dir_830_, v___x_837_);
    v___x_839_ = 1;
    v___x_840_ = l_Lake_untar(v_file_826_, v___x_838_, v___x_839_, v___x_836_);
    return v___x_840_;
}
pub unsafe fn l_Lake_Package_unpack___boxed(
    mut v_pkg_841_: *mut crate::leanh::LeanObject,
    mut v_file_842_: *mut crate::leanh::LeanObject,
    mut v_a_843_: *mut crate::leanh::LeanObject,
    mut v_a_844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_845_ = l_Lake_Package_unpack(v_pkg_841_, v_file_842_, v_a_843_);
    return v_res_845_;
}
pub unsafe fn _init_l_Lake_Package_uploadRelease___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_854_ = l_Lake_Package_uploadRelease___closed__4;
    v___x_855_ = crate::leanh::lean_unsigned_to_nat(5);
    v___x_856_ = lean_mk_empty_array_with_capacity(v___x_855_);
    v___x_857_ = lean_array_push(v___x_856_, v___x_854_);
    return v___x_857_;
}
pub unsafe fn _init_l_Lake_Package_uploadRelease___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_858_ = l_Lake_Package_uploadRelease___closed__5;
    v___x_859_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_uploadRelease___closed__7),
        core::ptr::addr_of_mut!(l_Lake_Package_uploadRelease___closed__7_once),
        _init_l_Lake_Package_uploadRelease___closed__7,
    );
    v___x_860_ = lean_array_push(v___x_859_, v___x_858_);
    return v___x_860_;
}
pub unsafe fn _init_l_Lake_Package_uploadRelease___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_862_ = l_Lake_Package_uploadRelease___closed__9;
    v___x_863_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_864_ = lean_mk_empty_array_with_capacity(v___x_863_);
    v___x_865_ = lean_array_push(v___x_864_, v___x_862_);
    return v___x_865_;
}
pub unsafe fn l_Lake_Package_uploadRelease(
    mut v_pkg_866_: *mut crate::leanh::LeanObject,
    mut v_tag_867_: *mut crate::leanh::LeanObject,
    mut v_a_868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_args_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: u8 = 0;
    let mut v___x_878_: u8 = 0;
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildArchive_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_releaseRepo_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: u8 = 0;
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_dir_881_ = crate::leanh::lean_ctor_get(v_pkg_866_, 4);
                v_config_882_ = crate::leanh::lean_ctor_get(v_pkg_866_, 6);
                crate::leanh::lean_inc_ref(v_config_882_);
                v_buildArchive_883_ = crate::leanh::lean_ctor_get(v_pkg_866_, 20);
                crate::leanh::lean_inc_ref_n(v_buildArchive_883_, 2);
                v___x_884_ = l_Lake_defaultLakeDir;
                crate::leanh::lean_inc_ref(v_dir_881_);
                v___x_885_ = l_Lake_joinRelative(v_dir_881_, v___x_884_);
                v___x_886_ = l_Lake_joinRelative(v___x_885_, v_buildArchive_883_);
                crate::leanh::lean_inc_ref(v___x_886_);
                v___x_887_ = l_Lake_Package_pack(v_pkg_866_, v___x_886_, v_a_868_);
                if crate::leanh::lean_obj_tag(v___x_887_) == 0 {
                    v_a_888_ = crate::leanh::lean_ctor_get(v___x_887_, 1);
                    crate::leanh::lean_inc(v_a_888_);
                    crate::leanh::lean_dec_ref_known(v___x_887_, 2);
                    v_releaseRepo_889_ = crate::leanh::lean_ctor_get(v_config_882_, 10);
                    crate::leanh::lean_inc(v_releaseRepo_889_);
                    crate::leanh::lean_dec_ref(v_config_882_);
                    v___x_890_ = l_Lake_Package_uploadRelease___closed__2;
                    v___x_891_ = lean_string_append(v___x_890_, v_tag_867_);
                    v___x_892_ = l_Lake_Package_uploadRelease___closed__3;
                    v___x_893_ = lean_string_append(v___x_891_, v___x_892_);
                    v___x_894_ = lean_string_append(v___x_893_, v_buildArchive_883_);
                    crate::leanh::lean_dec_ref(v_buildArchive_883_);
                    v___x_895_ = 1;
                    v___x_896_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_896_, 0, v___x_894_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_896_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_895_,
                    );
                    v___x_897_ = lean_array_push(v_a_888_, v___x_896_);
                    v___x_898_ = l_Lake_Package_uploadRelease___closed__6;
                    v___x_899_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_Package_uploadRelease___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_Package_uploadRelease___closed__8_once),
                        _init_l_Lake_Package_uploadRelease___closed__8,
                    );
                    v___x_900_ = lean_array_push(v___x_899_, v_tag_867_);
                    v___x_901_ = lean_array_push(v___x_900_, v___x_886_);
                    v___x_902_ = lean_array_push(v___x_901_, v___x_898_);
                    if crate::leanh::lean_obj_tag(v_releaseRepo_889_) == 1 {
                        v_val_903_ = crate::leanh::lean_ctor_get(v_releaseRepo_889_, 0);
                        crate::leanh::lean_inc(v_val_903_);
                        crate::leanh::lean_dec_ref_known(v_releaseRepo_889_, 1);
                        v___x_904_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_Package_uploadRelease___closed__10),
                            core::ptr::addr_of_mut!(l_Lake_Package_uploadRelease___closed__10_once),
                            _init_l_Lake_Package_uploadRelease___closed__10,
                        );
                        v___x_905_ = lean_array_push(v___x_904_, v_val_903_);
                        v___x_906_ = l_Array_append___redArg(v___x_902_, v___x_905_);
                        crate::leanh::lean_dec_ref(v___x_905_);
                        v_args_871_ = v___x_906_;
                        v___y_872_ = v___x_897_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_releaseRepo_889_);
                        v_args_871_ = v___x_902_;
                        v___y_872_ = v___x_897_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_886_);
                    crate::leanh::lean_dec_ref(v_buildArchive_883_);
                    crate::leanh::lean_dec_ref(v_config_882_);
                    crate::leanh::lean_dec_ref(v_tag_867_);
                    return v___x_887_;
                }
            }
            1 => {
                v___x_873_ = l_Lake_env___closed__0;
                v___x_874_ = l_Lake_Package_uploadRelease___closed__0;
                v___x_875_ = crate::leanh::lean_box(0);
                v___x_876_ = l_Lake_Package_uploadRelease___closed__1;
                v___x_877_ = 1;
                v___x_878_ = 0;
                v___x_879_ = crate::leanh::lean_alloc_ctor(0, 5, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_879_, 0, v___x_873_);
                crate::leanh::lean_ctor_set(v___x_879_, 1, v___x_874_);
                crate::leanh::lean_ctor_set(v___x_879_, 2, v_args_871_);
                crate::leanh::lean_ctor_set(v___x_879_, 3, v___x_875_);
                crate::leanh::lean_ctor_set(v___x_879_, 4, v___x_876_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_879_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___x_877_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_879_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_878_,
                );
                v___x_880_ = l_Lake_proc(v___x_879_, v___x_878_, v___y_872_);
                return v___x_880_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_uploadRelease___boxed(
    mut v_pkg_907_: *mut crate::leanh::LeanObject,
    mut v_tag_908_: *mut crate::leanh::LeanObject,
    mut v_a_909_: *mut crate::leanh::LeanObject,
    mut v_a_910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_911_ = l_Lake_Package_uploadRelease(v_pkg_907_, v_tag_908_, v_a_909_);
    return v_res_911_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0(
    mut v_s_914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_915_ =
        l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0;
    return v___x_915_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___boxed(
    mut v_s_916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_917_ =
        l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0(v_s_916_);
    crate::leanh::lean_dec_ref(v_s_916_);
    return v_res_917_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2(
    mut v___x_921_: *mut crate::leanh::LeanObject,
    mut v_as_922_: *mut crate::leanh::LeanObject,
    mut v_sz_923_: usize,
    mut v_i_924_: usize,
    mut v_b_925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_926_: u8 = 0;
    let mut v_a_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_baseName_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: u8 = 0;
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: usize = 0;
    let mut v___x_933_: usize = 0;
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_926_ = lean_usize_dec_lt(v_i_924_, v_sz_923_);
                if v___x_926_ == 0 {
                    crate::leanh::lean_inc_ref(v_b_925_);
                    return v_b_925_;
                } else {
                    v_a_927_ = lean_array_uget_borrowed(v_as_922_, v_i_924_);
                    v_baseName_928_ = crate::leanh::lean_ctor_get(v_a_927_, 1);
                    v___x_929_ = crate::leanh::lean_box(0);
                    v___x_930_ = lean_name_eq(v_baseName_928_, v___x_921_);
                    if v___x_930_ == 0 {
                        v___x_931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2___closed__0;
                        v___x_932_ = 1usize;
                        v___x_933_ = lean_usize_add(v_i_924_, v___x_932_);
                        v_i_924_ = v___x_933_;
                        v_b_925_ = v___x_931_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_927_);
                        v___x_935_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_935_, 0, v_a_927_);
                        v___x_936_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_936_, 0, v___x_935_);
                        v___x_937_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_937_, 0, v___x_936_);
                        crate::leanh::lean_ctor_set(v___x_937_, 1, v___x_929_);
                        return v___x_937_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2___boxed(
    mut v___x_938_: *mut crate::leanh::LeanObject,
    mut v_as_939_: *mut crate::leanh::LeanObject,
    mut v_sz_940_: *mut crate::leanh::LeanObject,
    mut v_i_941_: *mut crate::leanh::LeanObject,
    mut v_b_942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_943_: usize = 0;
    let mut v_i_boxed_944_: usize = 0;
    let mut v_res_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_943_ = crate::leanh::lean_unbox_usize(v_sz_940_);
    crate::leanh::lean_dec(v_sz_940_);
    v_i_boxed_944_ = crate::leanh::lean_unbox_usize(v_i_941_);
    crate::leanh::lean_dec(v_i_941_);
    v_res_945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2(v___x_938_, v_as_939_, v_sz_boxed_943_, v_i_boxed_944_, v_b_942_);
    crate::leanh::lean_dec_ref(v_b_942_);
    crate::leanh::lean_dec_ref(v_as_939_);
    crate::leanh::lean_dec(v___x_938_);
    return v_res_945_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg(
    mut v_driver_946_: *mut crate::leanh::LeanObject,
    mut v___x_947_: *mut crate::leanh::LeanObject,
    mut v___x_948_: *mut crate::leanh::LeanObject,
    mut v_a_949_: *mut crate::leanh::LeanObject,
    mut v_b_950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_963_: u8 = 0;
    let mut v_startInclusive_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: u8 = 0;
    let mut v___x_968_: u32 = 0;
    let mut v___x_969_: u32 = 0;
    let mut v___x_970_: u8 = 0;
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_949_) == 0 {
                    v_currPos_959_ = crate::leanh::lean_ctor_get(v_a_949_, 0);
                    v_searcher_960_ = crate::leanh::lean_ctor_get(v_a_949_, 1);
                    v_isSharedCheck_986_ = (!crate::leanh::lean_is_exclusive(v_a_949_)) as u8;
                    if v_isSharedCheck_986_ == 0 {
                        v___x_962_ = v_a_949_;
                        v_isShared_963_ = v_isSharedCheck_986_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_960_);
                        crate::leanh::lean_inc(v_currPos_959_);
                        crate::leanh::lean_dec(v_a_949_);
                        v___x_962_ = crate::leanh::lean_box(0);
                        v_isShared_963_ = v_isSharedCheck_986_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_948_);
                    crate::leanh::lean_dec_ref(v_driver_946_);
                    return v_b_950_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_driver_946_);
                v___x_955_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_955_, 0, v_driver_946_);
                crate::leanh::lean_ctor_set(v___x_955_, 1, v_startInclusive_953_);
                crate::leanh::lean_ctor_set(v___x_955_, 2, v_endExclusive_954_);
                v___x_956_ = l_String_Slice_toString(v___x_955_);
                crate::leanh::lean_dec_ref_known(v___x_955_, 3);
                v___x_957_ = lean_array_push(v_b_950_, v___x_956_);
                v_a_949_ = v_it_952_;
                v_b_950_ = v___x_957_;
                state = 0;
                continue;
            }
            2 => {
                v_startInclusive_964_ = crate::leanh::lean_ctor_get(v___x_947_, 1);
                v_endExclusive_965_ = crate::leanh::lean_ctor_get(v___x_947_, 2);
                v___x_966_ = lean_nat_sub(v_endExclusive_965_, v_startInclusive_964_);
                v___x_967_ = lean_nat_dec_eq(v_searcher_960_, v___x_966_);
                crate::leanh::lean_dec(v___x_966_);
                if v___x_967_ == 0 {
                    v___x_968_ = 47;
                    v___x_969_ = lean_string_utf8_get_fast(v_driver_946_, v_searcher_960_);
                    v___x_970_ = lean_uint32_dec_eq(v___x_969_, v___x_968_);
                    if v___x_970_ == 0 {
                        v___x_971_ = lean_string_utf8_next_fast(v_driver_946_, v_searcher_960_);
                        crate::leanh::lean_dec(v_searcher_960_);
                        if v_isShared_963_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_962_, 1, v___x_971_);
                            v___x_973_ = v___x_962_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_975_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_975_, 0, v_currPos_959_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_975_, 1, v___x_971_);
                            v___x_973_ = v_reuseFailAlloc_975_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_976_ = lean_string_utf8_next_fast(v_driver_946_, v_searcher_960_);
                        v___x_977_ = lean_nat_sub(v___x_976_, v_searcher_960_);
                        v___x_978_ = lean_nat_add(v_searcher_960_, v___x_977_);
                        crate::leanh::lean_dec(v___x_977_);
                        v_slice_979_ = l_String_Slice_subslice_x21(
                            v___x_947_,
                            v_currPos_959_,
                            v_searcher_960_,
                        );
                        crate::leanh::lean_inc(v___x_978_);
                        if v_isShared_963_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_962_, 1, v___x_978_);
                            crate::leanh::lean_ctor_set(v___x_962_, 0, v___x_978_);
                            v_nextIt_981_ = v___x_962_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_984_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_978_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_984_, 1, v___x_978_);
                            v_nextIt_981_ = v_reuseFailAlloc_984_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_962_);
                    crate::leanh::lean_dec(v_searcher_960_);
                    v___x_985_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc(v___x_948_);
                    v_it_952_ = v___x_985_;
                    v_startInclusive_953_ = v_currPos_959_;
                    v_endExclusive_954_ = v___x_948_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_949_ = v___x_973_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_982_ = crate::leanh::lean_ctor_get(v_slice_979_, 0);
                crate::leanh::lean_inc(v_startInclusive_982_);
                v_endExclusive_983_ = crate::leanh::lean_ctor_get(v_slice_979_, 1);
                crate::leanh::lean_inc(v_endExclusive_983_);
                crate::leanh::lean_dec_ref(v_slice_979_);
                v_it_952_ = v_nextIt_981_;
                v_startInclusive_953_ = v_startInclusive_982_;
                v_endExclusive_954_ = v_endExclusive_983_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg___boxed(
    mut v_driver_987_: *mut crate::leanh::LeanObject,
    mut v___x_988_: *mut crate::leanh::LeanObject,
    mut v___x_989_: *mut crate::leanh::LeanObject,
    mut v_a_990_: *mut crate::leanh::LeanObject,
    mut v_b_991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_992_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg(v_driver_987_, v___x_988_, v___x_989_, v_a_990_, v_b_991_);
    crate::leanh::lean_dec_ref(v___x_988_);
    return v_res_992_;
}
pub unsafe fn l_Lake_Package_resolveDriver(
    mut v_pkg_1001_: *mut crate::leanh::LeanObject,
    mut v_kind_1002_: *mut crate::leanh::LeanObject,
    mut v_driver_1003_: *mut crate::leanh::LeanObject,
    mut v_a_1004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: u8 = 0;
    let mut v_baseName_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1031_: u8 = 0;
    let mut v_baseName_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packages_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1054_: usize = 0;
    let mut v___x_1055_: usize = 0;
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1060_: u8 = 0;
    let mut v_val_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1065_: u8 = 0;
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1072_: u8 = 0;
    let mut v_isSharedCheck_1073_: u8 = 0;
    let mut v_unused_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1075_: u8 = 0;
    let mut v_baseName_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: u8 = 0;
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1006_ = lean_string_utf8_byte_size(v_driver_1003_);
                v___x_1007_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1008_ = lean_nat_dec_eq(v___x_1006_, v___x_1007_);
                if v___x_1008_ == 0 {
                    crate::leanh::lean_inc_ref_n(v_driver_1003_, 2);
                    v___x_1022_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1022_, 0, v_driver_1003_);
                    crate::leanh::lean_ctor_set(v___x_1022_, 1, v___x_1007_);
                    crate::leanh::lean_ctor_set(v___x_1022_, 2, v___x_1006_);
                    v___x_1023_ =
                        l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0(
                            v___x_1022_,
                        );
                    v___x_1024_ = l_Lake_Package_pack___closed__1;
                    v___x_1025_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg(v_driver_1003_, v___x_1022_, v___x_1006_, v___x_1023_, v___x_1024_);
                    crate::leanh::lean_dec_ref_known(v___x_1022_, 3);
                    v___x_1026_ = lean_array_to_list(v___x_1025_);
                    if crate::leanh::lean_obj_tag(v___x_1026_) == 1 {
                        v_head_1027_ = crate::leanh::lean_ctor_get(v___x_1026_, 0);
                        v_tail_1028_ = crate::leanh::lean_ctor_get(v___x_1026_, 1);
                        v_isSharedCheck_1075_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1026_)) as u8;
                        if v_isSharedCheck_1075_ == 0 {
                            v___x_1030_ = v___x_1026_;
                            v_isShared_1031_ = v_isSharedCheck_1075_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_tail_1028_);
                            crate::leanh::lean_inc(v_head_1027_);
                            crate::leanh::lean_dec(v___x_1026_);
                            v___x_1030_ = crate::leanh::lean_box(0);
                            v_isShared_1031_ = v_isSharedCheck_1075_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1026_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_driver_1003_);
                    v_baseName_1076_ = crate::leanh::lean_ctor_get(v_pkg_1001_, 1);
                    crate::leanh::lean_inc(v_baseName_1076_);
                    crate::leanh::lean_dec_ref(v_pkg_1001_);
                    v___x_1077_ = 0;
                    v___x_1078_ = l_Lean_Name_toString(v_baseName_1076_, v___x_1077_);
                    v___x_1079_ = l_Lake_Package_resolveDriver___closed__6;
                    v___x_1080_ = lean_string_append(v___x_1078_, v___x_1079_);
                    v___x_1081_ = lean_string_append(v___x_1080_, v_kind_1002_);
                    v___x_1082_ = l_Lake_Package_resolveDriver___closed__7;
                    v___x_1083_ = lean_string_append(v___x_1081_, v___x_1082_);
                    v___x_1084_ = lean_mk_io_user_error(v___x_1083_);
                    v___x_1085_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1085_, 0, v___x_1084_);
                    return v___x_1085_;
                }
            }
            1 => {
                v_baseName_1010_ = crate::leanh::lean_ctor_get(v_pkg_1001_, 1);
                crate::leanh::lean_inc(v_baseName_1010_);
                crate::leanh::lean_dec_ref(v_pkg_1001_);
                v___x_1011_ = l_Lean_Name_toString(v_baseName_1010_, v___x_1008_);
                v___x_1012_ = l_Lake_Package_resolveDriver___closed__0;
                v___x_1013_ = lean_string_append(v___x_1011_, v___x_1012_);
                v___x_1014_ = lean_string_append(v___x_1013_, v_kind_1002_);
                v___x_1015_ = l_Lake_Package_resolveDriver___closed__1;
                v___x_1016_ = lean_string_append(v___x_1014_, v___x_1015_);
                v___x_1017_ = lean_string_append(v___x_1016_, v_driver_1003_);
                crate::leanh::lean_dec_ref(v_driver_1003_);
                v___x_1018_ = l_Lake_Package_resolveDriver___closed__2;
                v___x_1019_ = lean_string_append(v___x_1017_, v___x_1018_);
                v___x_1020_ = lean_mk_io_user_error(v___x_1019_);
                v___x_1021_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1021_, 0, v___x_1020_);
                return v___x_1021_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_tail_1028_) == 0 {
                    crate::leanh::lean_dec_ref(v_driver_1003_);
                    if v_isShared_1031_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1030_, 0);
                        crate::leanh::lean_ctor_set(v___x_1030_, 1, v_head_1027_);
                        crate::leanh::lean_ctor_set(v___x_1030_, 0, v_pkg_1001_);
                        v___x_1046_ = v___x_1030_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1048_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_pkg_1001_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_head_1027_);
                        v___x_1046_ = v_reuseFailAlloc_1048_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1030_);
                    v_tail_1049_ = crate::leanh::lean_ctor_get(v_tail_1028_, 1);
                    if crate::leanh::lean_obj_tag(v_tail_1049_) == 0 {
                        crate::leanh::lean_dec_ref(v_driver_1003_);
                        v_head_1050_ = crate::leanh::lean_ctor_get(v_tail_1028_, 0);
                        crate::leanh::lean_inc(v_head_1050_);
                        crate::leanh::lean_dec_ref_known(v_tail_1028_, 2);
                        v_packages_1051_ = crate::leanh::lean_ctor_get(v_a_1004_, 4);
                        crate::leanh::lean_inc(v_head_1027_);
                        v___x_1052_ = l_String_toName(v_head_1027_);
                        v___x_1053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2___closed__0;
                        v_sz_1054_ = lean_array_size(v_packages_1051_);
                        v___x_1055_ = 0usize;
                        v___x_1056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2(v___x_1052_, v_packages_1051_, v_sz_1054_, v___x_1055_, v___x_1053_);
                        crate::leanh::lean_dec(v___x_1052_);
                        v_fst_1057_ = crate::leanh::lean_ctor_get(v___x_1056_, 0);
                        v_isSharedCheck_1073_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1056_)) as u8;
                        if v_isSharedCheck_1073_ == 0 {
                            v_unused_1074_ = crate::leanh::lean_ctor_get(v___x_1056_, 1);
                            crate::leanh::lean_dec(v_unused_1074_);
                            v___x_1059_ = v___x_1056_;
                            v_isShared_1060_ = v_isSharedCheck_1073_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_fst_1057_);
                            crate::leanh::lean_dec(v___x_1056_);
                            v___x_1059_ = crate::leanh::lean_box(0);
                            v_isShared_1060_ = v_isSharedCheck_1073_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_tail_1028_, 2);
                        crate::leanh::lean_dec(v_head_1027_);
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                v_baseName_1033_ = crate::leanh::lean_ctor_get(v_pkg_1001_, 1);
                crate::leanh::lean_inc(v_baseName_1033_);
                crate::leanh::lean_dec_ref(v_pkg_1001_);
                v___x_1034_ = l_Lean_Name_toString(v_baseName_1033_, v___x_1008_);
                v___x_1035_ = l_Lake_Package_resolveDriver___closed__3;
                v___x_1036_ = lean_string_append(v___x_1034_, v___x_1035_);
                v___x_1037_ = lean_string_append(v___x_1036_, v_kind_1002_);
                v___x_1038_ = l_Lake_Package_resolveDriver___closed__4;
                v___x_1039_ = lean_string_append(v___x_1037_, v___x_1038_);
                v___x_1040_ = lean_string_append(v___x_1039_, v_head_1027_);
                crate::leanh::lean_dec(v_head_1027_);
                v___x_1041_ = l_Lake_Package_resolveDriver___closed__5;
                v___x_1042_ = lean_string_append(v___x_1040_, v___x_1041_);
                v___x_1043_ = lean_mk_io_user_error(v___x_1042_);
                v___x_1044_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1044_, 0, v___x_1043_);
                return v___x_1044_;
            }
            4 => {
                v___x_1047_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1047_, 0, v___x_1046_);
                return v___x_1047_;
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_fst_1057_) == 0 {
                    crate::leanh::lean_del_object(v___x_1059_);
                    crate::leanh::lean_dec(v_head_1050_);
                    state = 3;
                    continue;
                } else {
                    v_val_1061_ = crate::leanh::lean_ctor_get(v_fst_1057_, 0);
                    crate::leanh::lean_inc(v_val_1061_);
                    crate::leanh::lean_dec_ref_known(v_fst_1057_, 1);
                    if crate::leanh::lean_obj_tag(v_val_1061_) == 1 {
                        crate::leanh::lean_dec(v_head_1027_);
                        crate::leanh::lean_dec_ref(v_pkg_1001_);
                        v_val_1062_ = crate::leanh::lean_ctor_get(v_val_1061_, 0);
                        v_isSharedCheck_1072_ =
                            (!crate::leanh::lean_is_exclusive(v_val_1061_)) as u8;
                        if v_isSharedCheck_1072_ == 0 {
                            v___x_1064_ = v_val_1061_;
                            v_isShared_1065_ = v_isSharedCheck_1072_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1062_);
                            crate::leanh::lean_dec(v_val_1061_);
                            v___x_1064_ = crate::leanh::lean_box(0);
                            v_isShared_1065_ = v_isSharedCheck_1072_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_1061_);
                        crate::leanh::lean_del_object(v___x_1059_);
                        crate::leanh::lean_dec(v_head_1050_);
                        state = 3;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_1060_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1059_, 1, v_head_1050_);
                    crate::leanh::lean_ctor_set(v___x_1059_, 0, v_val_1062_);
                    v___x_1067_ = v___x_1059_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1071_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_val_1062_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_head_1050_);
                    v___x_1067_ = v_reuseFailAlloc_1071_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1065_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1064_, 0);
                    crate::leanh::lean_ctor_set(v___x_1064_, 0, v___x_1067_);
                    v___x_1069_ = v___x_1064_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1070_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
                    v___x_1069_ = v_reuseFailAlloc_1070_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1069_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_resolveDriver___boxed(
    mut v_pkg_1086_: *mut crate::leanh::LeanObject,
    mut v_kind_1087_: *mut crate::leanh::LeanObject,
    mut v_driver_1088_: *mut crate::leanh::LeanObject,
    mut v_a_1089_: *mut crate::leanh::LeanObject,
    mut v_a_1090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1091_ =
        l_Lake_Package_resolveDriver(v_pkg_1086_, v_kind_1087_, v_driver_1088_, v_a_1089_);
    crate::leanh::lean_dec(v_a_1089_);
    crate::leanh::lean_dec_ref(v_kind_1087_);
    return v_res_1091_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1(
    mut v_driver_1092_: *mut crate::leanh::LeanObject,
    mut v___x_1093_: *mut crate::leanh::LeanObject,
    mut v___x_1094_: *mut crate::leanh::LeanObject,
    mut v_inst_1095_: *mut crate::leanh::LeanObject,
    mut v_R_1096_: *mut crate::leanh::LeanObject,
    mut v_a_1097_: *mut crate::leanh::LeanObject,
    mut v_b_1098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1099_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg(v_driver_1092_, v___x_1093_, v___x_1094_, v_a_1097_, v_b_1098_);
    return v___x_1099_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___boxed(
    mut v_driver_1100_: *mut crate::leanh::LeanObject,
    mut v___x_1101_: *mut crate::leanh::LeanObject,
    mut v___x_1102_: *mut crate::leanh::LeanObject,
    mut v_inst_1103_: *mut crate::leanh::LeanObject,
    mut v_R_1104_: *mut crate::leanh::LeanObject,
    mut v_a_1105_: *mut crate::leanh::LeanObject,
    mut v_b_1106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1107_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1(v_driver_1100_, v___x_1101_, v___x_1102_, v_inst_1103_, v_R_1104_, v_a_1105_, v_b_1106_);
    crate::leanh::lean_dec_ref(v___x_1101_);
    return v_res_1107_;
}
pub unsafe fn l_Lake_Package_test___lam__0(
    mut v_keyName_1108_: *mut crate::leanh::LeanObject,
    mut v_name_1109_: *mut crate::leanh::LeanObject,
    mut v___x_1110_: *mut crate::leanh::LeanObject,
    mut v___x_1111_: *mut crate::leanh::LeanObject,
    mut v___y_1112_: *mut crate::leanh::LeanObject,
    mut v___y_1113_: *mut crate::leanh::LeanObject,
    mut v___y_1114_: *mut crate::leanh::LeanObject,
    mut v___y_1115_: *mut crate::leanh::LeanObject,
    mut v___y_1116_: *mut crate::leanh::LeanObject,
    mut v___y_1117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1119_ = l_Lake_LeanLib_defaultFacet;
    v___x_1120_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1120_, 0, v_keyName_1108_);
    crate::leanh::lean_ctor_set(v___x_1120_, 1, v_name_1109_);
    v___x_1121_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1121_, 0, v___x_1120_);
    crate::leanh::lean_ctor_set(v___x_1121_, 1, v___x_1110_);
    crate::leanh::lean_ctor_set(v___x_1121_, 2, v___x_1111_);
    crate::leanh::lean_ctor_set(v___x_1121_, 3, v___x_1119_);
    v___x_1122_ = crate::leanh::lean_apply_7(
        v___y_1112_,
        v___x_1121_,
        v___y_1113_,
        v___y_1114_,
        v___y_1115_,
        v___y_1116_,
        v___y_1117_,
        crate::leanh::lean_box(0),
    );
    return v___x_1122_;
}
pub unsafe fn l_Lake_Package_test___lam__0___boxed(
    mut v_keyName_1123_: *mut crate::leanh::LeanObject,
    mut v_name_1124_: *mut crate::leanh::LeanObject,
    mut v___x_1125_: *mut crate::leanh::LeanObject,
    mut v___x_1126_: *mut crate::leanh::LeanObject,
    mut v___y_1127_: *mut crate::leanh::LeanObject,
    mut v___y_1128_: *mut crate::leanh::LeanObject,
    mut v___y_1129_: *mut crate::leanh::LeanObject,
    mut v___y_1130_: *mut crate::leanh::LeanObject,
    mut v___y_1131_: *mut crate::leanh::LeanObject,
    mut v___y_1132_: *mut crate::leanh::LeanObject,
    mut v___y_1133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1134_ = l_Lake_Package_test___lam__0(
        v_keyName_1123_,
        v_name_1124_,
        v___x_1125_,
        v___x_1126_,
        v___y_1127_,
        v___y_1128_,
        v___y_1129_,
        v___y_1130_,
        v___y_1131_,
        v___y_1132_,
    );
    return v_res_1134_;
}
pub unsafe fn l_Lake_Package_test___lam__1(
    mut v_keyName_1135_: *mut crate::leanh::LeanObject,
    mut v_name_1136_: *mut crate::leanh::LeanObject,
    mut v___x_1137_: *mut crate::leanh::LeanObject,
    mut v___x_1138_: *mut crate::leanh::LeanObject,
    mut v___y_1139_: *mut crate::leanh::LeanObject,
    mut v___y_1140_: *mut crate::leanh::LeanObject,
    mut v___y_1141_: *mut crate::leanh::LeanObject,
    mut v___y_1142_: *mut crate::leanh::LeanObject,
    mut v___y_1143_: *mut crate::leanh::LeanObject,
    mut v___y_1144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1146_ = l_Lake_LeanExe_exeFacet;
    v___x_1147_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1147_, 0, v_keyName_1135_);
    crate::leanh::lean_ctor_set(v___x_1147_, 1, v_name_1136_);
    v___x_1148_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1148_, 0, v___x_1147_);
    crate::leanh::lean_ctor_set(v___x_1148_, 1, v___x_1137_);
    crate::leanh::lean_ctor_set(v___x_1148_, 2, v___x_1138_);
    crate::leanh::lean_ctor_set(v___x_1148_, 3, v___x_1146_);
    v___x_1149_ = crate::leanh::lean_apply_7(
        v___y_1139_,
        v___x_1148_,
        v___y_1140_,
        v___y_1141_,
        v___y_1142_,
        v___y_1143_,
        v___y_1144_,
        crate::leanh::lean_box(0),
    );
    return v___x_1149_;
}
pub unsafe fn l_Lake_Package_test___lam__1___boxed(
    mut v_keyName_1150_: *mut crate::leanh::LeanObject,
    mut v_name_1151_: *mut crate::leanh::LeanObject,
    mut v___x_1152_: *mut crate::leanh::LeanObject,
    mut v___x_1153_: *mut crate::leanh::LeanObject,
    mut v___y_1154_: *mut crate::leanh::LeanObject,
    mut v___y_1155_: *mut crate::leanh::LeanObject,
    mut v___y_1156_: *mut crate::leanh::LeanObject,
    mut v___y_1157_: *mut crate::leanh::LeanObject,
    mut v___y_1158_: *mut crate::leanh::LeanObject,
    mut v___y_1159_: *mut crate::leanh::LeanObject,
    mut v___y_1160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1161_ = l_Lake_Package_test___lam__1(
        v_keyName_1150_,
        v_name_1151_,
        v___x_1152_,
        v___x_1153_,
        v___y_1154_,
        v___y_1155_,
        v___y_1156_,
        v___y_1157_,
        v___y_1158_,
        v___y_1159_,
    );
    return v_res_1161_;
}
pub unsafe fn _init_l_Lake_Package_test___boxed__const__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1168_: u32 = 0;
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1168_ = 0;
    v___x_1169_ = crate::leanh::lean_box_uint32(v___x_1168_);
    return v___x_1169_;
}
pub unsafe fn l_Lake_Package_test(
    mut v_pkg_1170_: *mut crate::leanh::LeanObject,
    mut v_args_1171_: *mut crate::leanh::LeanObject,
    mut v_buildConfig_1172_: *mut crate::leanh::LeanObject,
    mut v_a_1173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_testDriver_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1182_: u8 = 0;
    let mut v_fst_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_testDriverArgs_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_baseName_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scripts_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: u8 = 0;
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: u8 = 0;
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: u8 = 0;
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: u8 = 0;
    let mut v___x_1220_: u8 = 0;
    let mut v_toLogConfig_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_oldMode_1222_: u8 = 0;
    let mut v_trustHash_1223_: u8 = 0;
    let mut v_noBuild_1224_: u8 = 0;
    let mut v_verbosity_1225_: u8 = 0;
    let mut v_showSuccess_1226_: u8 = 0;
    let mut v_outputsFile_x3f_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOptOverrides_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1231_: u8 = 0;
    let mut v_failLv_1232_: u8 = 0;
    let mut v_outLv_1233_: u8 = 0;
    let mut v_ansiMode_1234_: u8 = 0;
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1237_: u8 = 0;
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1248_: u8 = 0;
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1253_: u8 = 0;
    let mut v_unused_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1258_: u8 = 0;
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1262_: u8 = 0;
    let mut v_reuseFailAlloc_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1265_: u8 = 0;
    let mut v_unused_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1267_: u8 = 0;
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: u8 = 0;
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1291_: u8 = 0;
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1295_: u8 = 0;
    let mut v_isSharedCheck_1296_: u8 = 0;
    let mut v_a_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1300_: u8 = 0;
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1304_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_config_1175_ = crate::leanh::lean_ctor_get(v_pkg_1170_, 6);
                crate::leanh::lean_inc_ref(v_config_1175_);
                v_testDriver_1176_ = crate::leanh::lean_ctor_get(v_pkg_1170_, 21);
                crate::leanh::lean_inc_ref(v_testDriver_1176_);
                v___x_1177_ = l_Lake_Package_test___closed__0;
                v___x_1178_ = l_Lake_Package_resolveDriver(
                    v_pkg_1170_,
                    v___x_1177_,
                    v_testDriver_1176_,
                    v_a_1173_,
                );
                if crate::leanh::lean_obj_tag(v___x_1178_) == 0 {
                    v_a_1179_ = crate::leanh::lean_ctor_get(v___x_1178_, 0);
                    v_isSharedCheck_1296_ = (!crate::leanh::lean_is_exclusive(v___x_1178_)) as u8;
                    if v_isSharedCheck_1296_ == 0 {
                        v___x_1181_ = v___x_1178_;
                        v_isShared_1182_ = v_isSharedCheck_1296_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1179_);
                        crate::leanh::lean_dec(v___x_1178_);
                        v___x_1181_ = crate::leanh::lean_box(0);
                        v_isShared_1182_ = v_isSharedCheck_1296_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_config_1175_);
                    crate::leanh::lean_dec_ref(v_buildConfig_1172_);
                    crate::leanh::lean_dec(v_args_1171_);
                    v_a_1297_ = crate::leanh::lean_ctor_get(v___x_1178_, 0);
                    v_isSharedCheck_1304_ = (!crate::leanh::lean_is_exclusive(v___x_1178_)) as u8;
                    if v_isSharedCheck_1304_ == 0 {
                        v___x_1299_ = v___x_1178_;
                        v_isShared_1300_ = v_isSharedCheck_1304_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1297_);
                        crate::leanh::lean_dec(v___x_1178_);
                        v___x_1299_ = crate::leanh::lean_box(0);
                        v_isShared_1300_ = v_isSharedCheck_1304_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1183_ = crate::leanh::lean_ctor_get(v_a_1179_, 0);
                crate::leanh::lean_inc(v_fst_1183_);
                v_snd_1184_ = crate::leanh::lean_ctor_get(v_a_1179_, 1);
                crate::leanh::lean_inc_n(v_snd_1184_, 2);
                crate::leanh::lean_dec(v_a_1179_);
                v_testDriverArgs_1185_ = crate::leanh::lean_ctor_get(v_config_1175_, 13);
                crate::leanh::lean_inc_ref(v_testDriverArgs_1185_);
                crate::leanh::lean_dec_ref(v_config_1175_);
                v_baseName_1186_ = crate::leanh::lean_ctor_get(v_fst_1183_, 1);
                v_keyName_1187_ = crate::leanh::lean_ctor_get(v_fst_1183_, 2);
                crate::leanh::lean_inc(v_keyName_1187_);
                v_scripts_1188_ = crate::leanh::lean_ctor_get(v_fst_1183_, 17);
                v___x_1268_ = l_String_toName(v_snd_1184_);
                v___x_1269_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_scripts_1188_, v___x_1268_);
                if crate::leanh::lean_obj_tag(v___x_1269_) == 1 {
                    crate::leanh::lean_dec(v___x_1268_);
                    crate::leanh::lean_dec(v_keyName_1187_);
                    crate::leanh::lean_dec(v_snd_1184_);
                    crate::leanh::lean_dec(v_fst_1183_);
                    crate::leanh::lean_del_object(v___x_1181_);
                    crate::leanh::lean_dec_ref(v_buildConfig_1172_);
                    v_val_1270_ = crate::leanh::lean_ctor_get(v___x_1269_, 0);
                    crate::leanh::lean_inc(v_val_1270_);
                    crate::leanh::lean_dec_ref_known(v___x_1269_, 1);
                    v___x_1271_ = lean_array_to_list(v_testDriverArgs_1185_);
                    v___x_1272_ = l_List_appendTR___redArg(v___x_1271_, v_args_1171_);
                    v___x_1273_ = l_Lake_Script_run(v___x_1272_, v_val_1270_, v_a_1173_);
                    return v___x_1273_;
                } else {
                    crate::leanh::lean_dec(v___x_1269_);
                    v___x_1274_ = l_Lake_Package_findTargetDecl_x3f(v___x_1268_, v_fst_1183_);
                    crate::leanh::lean_dec(v___x_1268_);
                    if crate::leanh::lean_obj_tag(v___x_1274_) == 0 {
                        state = 5;
                        continue;
                    } else {
                        v_val_1275_ = crate::leanh::lean_ctor_get(v___x_1274_, 0);
                        crate::leanh::lean_inc(v_val_1275_);
                        crate::leanh::lean_dec_ref_known(v___x_1274_, 1);
                        v_name_1276_ = crate::leanh::lean_ctor_get(v_val_1275_, 1);
                        crate::leanh::lean_inc(v_name_1276_);
                        v_kind_1277_ = crate::leanh::lean_ctor_get(v_val_1275_, 2);
                        crate::leanh::lean_inc(v_kind_1277_);
                        v_config_1278_ = crate::leanh::lean_ctor_get(v_val_1275_, 3);
                        crate::leanh::lean_inc(v_config_1278_);
                        crate::leanh::lean_dec(v_val_1275_);
                        v___x_1279_ = l_Lake_LeanExe_keyword;
                        v___x_1280_ = lean_name_eq(v_kind_1277_, v___x_1279_);
                        crate::leanh::lean_dec(v_kind_1277_);
                        if v___x_1280_ == 0 {
                            crate::leanh::lean_dec(v_config_1278_);
                            crate::leanh::lean_dec(v_name_1276_);
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_snd_1184_);
                            crate::leanh::lean_del_object(v___x_1181_);
                            crate::leanh::lean_inc(v_name_1276_);
                            v___x_1281_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1281_, 0, v_fst_1183_);
                            crate::leanh::lean_ctor_set(v___x_1281_, 1, v_name_1276_);
                            crate::leanh::lean_ctor_set(v___x_1281_, 2, v_config_1278_);
                            v___f_1282_ = crate::leanh::lean_alloc_closure(
                                l_Lake_Package_test___lam__1___boxed as *mut core::ffi::c_void,
                                11,
                                4,
                            );
                            crate::leanh::lean_closure_set(v___f_1282_, 0, v_keyName_1187_);
                            crate::leanh::lean_closure_set(v___f_1282_, 1, v_name_1276_);
                            crate::leanh::lean_closure_set(v___f_1282_, 2, v___x_1279_);
                            crate::leanh::lean_closure_set(v___f_1282_, 3, v___x_1281_);
                            crate::leanh::lean_inc(v_a_1173_);
                            v___x_1283_ = l_Lake_Workspace_runBuild___redArg(
                                v_a_1173_,
                                v___f_1282_,
                                v_buildConfig_1172_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1283_) == 0 {
                                v_a_1284_ = crate::leanh::lean_ctor_get(v___x_1283_, 0);
                                crate::leanh::lean_inc(v_a_1284_);
                                crate::leanh::lean_dec_ref_known(v___x_1283_, 1);
                                v___x_1285_ = lean_array_mk(v_args_1171_);
                                v___x_1286_ =
                                    l_Array_append___redArg(v_testDriverArgs_1185_, v___x_1285_);
                                crate::leanh::lean_dec_ref(v___x_1285_);
                                v___x_1287_ = l_Lake_env(v_a_1284_, v___x_1286_, v_a_1173_);
                                return v___x_1287_;
                            } else {
                                crate::leanh::lean_dec_ref(v_testDriverArgs_1185_);
                                crate::leanh::lean_dec(v_args_1171_);
                                v_a_1288_ = crate::leanh::lean_ctor_get(v___x_1283_, 0);
                                v_isSharedCheck_1295_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1283_)) as u8;
                                if v_isSharedCheck_1295_ == 0 {
                                    v___x_1290_ = v___x_1283_;
                                    v_isShared_1291_ = v_isSharedCheck_1295_;
                                    state = 14;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1288_);
                                    crate::leanh::lean_dec(v___x_1283_);
                                    v___x_1290_ = crate::leanh::lean_box(0);
                                    v_isShared_1291_ = v_isSharedCheck_1295_;
                                    state = 14;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_1190_ = 0;
                v___x_1191_ = l_Lean_Name_toString(v_baseName_1186_, v___x_1190_);
                v___x_1192_ = l_Lake_Package_test___closed__1;
                v___x_1193_ = lean_string_append(v___x_1191_, v___x_1192_);
                v___x_1194_ = lean_mk_io_user_error(v___x_1193_);
                if v_isShared_1182_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1181_, 1);
                    crate::leanh::lean_ctor_set(v___x_1181_, 0, v___x_1194_);
                    v___x_1196_ = v___x_1181_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1197_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1194_);
                    v___x_1196_ = v_reuseFailAlloc_1197_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1196_;
            }
            4 => {
                v___x_1199_ = 0;
                v___x_1200_ = l_Lean_Name_toString(v_baseName_1186_, v___x_1199_);
                v___x_1201_ = l_Lake_Package_test___closed__2;
                v___x_1202_ = lean_string_append(v___x_1200_, v___x_1201_);
                v___x_1203_ = lean_string_append(v___x_1202_, v_snd_1184_);
                crate::leanh::lean_dec(v_snd_1184_);
                v___x_1204_ = l_Lake_Package_resolveDriver___closed__5;
                v___x_1205_ = lean_string_append(v___x_1203_, v___x_1204_);
                v___x_1206_ = lean_mk_io_user_error(v___x_1205_);
                v___x_1207_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1207_, 0, v___x_1206_);
                return v___x_1207_;
            }
            5 => {
                crate::leanh::lean_inc(v_snd_1184_);
                v___x_1209_ = l_String_toName(v_snd_1184_);
                v___x_1210_ = l_Lake_Package_findTargetDecl_x3f(v___x_1209_, v_fst_1183_);
                crate::leanh::lean_dec(v___x_1209_);
                if crate::leanh::lean_obj_tag(v___x_1210_) == 0 {
                    crate::leanh::lean_inc(v_baseName_1186_);
                    crate::leanh::lean_dec(v_keyName_1187_);
                    crate::leanh::lean_dec_ref(v_testDriverArgs_1185_);
                    crate::leanh::lean_dec(v_fst_1183_);
                    crate::leanh::lean_del_object(v___x_1181_);
                    crate::leanh::lean_dec_ref(v_buildConfig_1172_);
                    crate::leanh::lean_dec(v_args_1171_);
                    state = 4;
                    continue;
                } else {
                    v_val_1211_ = crate::leanh::lean_ctor_get(v___x_1210_, 0);
                    crate::leanh::lean_inc(v_val_1211_);
                    crate::leanh::lean_dec_ref_known(v___x_1210_, 1);
                    v_name_1212_ = crate::leanh::lean_ctor_get(v_val_1211_, 1);
                    crate::leanh::lean_inc(v_name_1212_);
                    v_kind_1213_ = crate::leanh::lean_ctor_get(v_val_1211_, 2);
                    crate::leanh::lean_inc(v_kind_1213_);
                    v_config_1214_ = crate::leanh::lean_ctor_get(v_val_1211_, 3);
                    crate::leanh::lean_inc(v_config_1214_);
                    crate::leanh::lean_dec(v_val_1211_);
                    v___x_1215_ = l_Lake_Package_test___closed__4;
                    v___x_1216_ = lean_name_eq(v_kind_1213_, v___x_1215_);
                    crate::leanh::lean_dec(v_kind_1213_);
                    if v___x_1216_ == 0 {
                        crate::leanh::lean_inc(v_baseName_1186_);
                        crate::leanh::lean_dec(v_config_1214_);
                        crate::leanh::lean_dec(v_name_1212_);
                        crate::leanh::lean_dec(v_keyName_1187_);
                        crate::leanh::lean_dec_ref(v_testDriverArgs_1185_);
                        crate::leanh::lean_dec(v_fst_1183_);
                        crate::leanh::lean_del_object(v___x_1181_);
                        crate::leanh::lean_dec_ref(v_buildConfig_1172_);
                        crate::leanh::lean_dec(v_args_1171_);
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_1184_);
                        v___x_1217_ = lean_array_get_size(v_testDriverArgs_1185_);
                        crate::leanh::lean_dec_ref(v_testDriverArgs_1185_);
                        v___x_1218_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1219_ = lean_nat_dec_eq(v___x_1217_, v___x_1218_);
                        if v___x_1219_ == 0 {
                            crate::leanh::lean_inc(v_baseName_1186_);
                            crate::leanh::lean_dec(v_config_1214_);
                            crate::leanh::lean_dec(v_name_1212_);
                            crate::leanh::lean_dec(v_keyName_1187_);
                            crate::leanh::lean_dec(v_fst_1183_);
                            crate::leanh::lean_dec_ref(v_buildConfig_1172_);
                            crate::leanh::lean_dec(v_args_1171_);
                            state = 2;
                            continue;
                        } else {
                            v___x_1220_ = l_List_isEmpty___redArg(v_args_1171_);
                            crate::leanh::lean_dec(v_args_1171_);
                            if v___x_1220_ == 0 {
                                crate::leanh::lean_inc(v_baseName_1186_);
                                crate::leanh::lean_dec(v_config_1214_);
                                crate::leanh::lean_dec(v_name_1212_);
                                crate::leanh::lean_dec(v_keyName_1187_);
                                crate::leanh::lean_dec(v_fst_1183_);
                                crate::leanh::lean_dec_ref(v_buildConfig_1172_);
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_1181_);
                                v_toLogConfig_1221_ =
                                    crate::leanh::lean_ctor_get(v_buildConfig_1172_, 0);
                                v_oldMode_1222_ = crate::leanh::lean_ctor_get_uint8(
                                    v_buildConfig_1172_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3)
                                        as u32,
                                );
                                v_trustHash_1223_ = crate::leanh::lean_ctor_get_uint8(
                                    v_buildConfig_1172_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1)
                                        as u32,
                                );
                                v_noBuild_1224_ = crate::leanh::lean_ctor_get_uint8(
                                    v_buildConfig_1172_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2)
                                        as u32,
                                );
                                v_verbosity_1225_ = crate::leanh::lean_ctor_get_uint8(
                                    v_buildConfig_1172_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 3)
                                        as u32,
                                );
                                v_showSuccess_1226_ = crate::leanh::lean_ctor_get_uint8(
                                    v_buildConfig_1172_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 4)
                                        as u32,
                                );
                                v_outputsFile_x3f_1227_ =
                                    crate::leanh::lean_ctor_get(v_buildConfig_1172_, 1);
                                v_leanOptOverrides_1228_ =
                                    crate::leanh::lean_ctor_get(v_buildConfig_1172_, 2);
                                v_isSharedCheck_1267_ =
                                    (!crate::leanh::lean_is_exclusive(v_buildConfig_1172_)) as u8;
                                if v_isSharedCheck_1267_ == 0 {
                                    v___x_1230_ = v_buildConfig_1172_;
                                    v_isShared_1231_ = v_isSharedCheck_1267_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_leanOptOverrides_1228_);
                                    crate::leanh::lean_inc(v_outputsFile_x3f_1227_);
                                    crate::leanh::lean_inc(v_toLogConfig_1221_);
                                    crate::leanh::lean_dec(v_buildConfig_1172_);
                                    v___x_1230_ = crate::leanh::lean_box(0);
                                    v_isShared_1231_ = v_isSharedCheck_1267_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            6 => {
                v_failLv_1232_ = crate::leanh::lean_ctor_get_uint8(
                    v_toLogConfig_1221_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_outLv_1233_ = crate::leanh::lean_ctor_get_uint8(
                    v_toLogConfig_1221_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                );
                v_ansiMode_1234_ = crate::leanh::lean_ctor_get_uint8(
                    v_toLogConfig_1221_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 2) as u32,
                );
                v_isSharedCheck_1265_ =
                    (!crate::leanh::lean_is_exclusive(v_toLogConfig_1221_)) as u8;
                if v_isSharedCheck_1265_ == 0 {
                    v_unused_1266_ = crate::leanh::lean_ctor_get(v_toLogConfig_1221_, 0);
                    crate::leanh::lean_dec(v_unused_1266_);
                    v___x_1236_ = v_toLogConfig_1221_;
                    v_isShared_1237_ = v_isSharedCheck_1265_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_toLogConfig_1221_);
                    v___x_1236_ = crate::leanh::lean_box(0);
                    v_isShared_1237_ = v_isSharedCheck_1265_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                crate::leanh::lean_inc(v_name_1212_);
                v___x_1238_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1238_, 0, v_fst_1183_);
                crate::leanh::lean_ctor_set(v___x_1238_, 1, v_name_1212_);
                crate::leanh::lean_ctor_set(v___x_1238_, 2, v_config_1214_);
                v___f_1239_ = crate::leanh::lean_alloc_closure(
                    l_Lake_Package_test___lam__0___boxed as *mut core::ffi::c_void,
                    11,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_1239_, 0, v_keyName_1187_);
                crate::leanh::lean_closure_set(v___f_1239_, 1, v_name_1212_);
                crate::leanh::lean_closure_set(v___f_1239_, 2, v___x_1215_);
                crate::leanh::lean_closure_set(v___f_1239_, 3, v___x_1238_);
                v___x_1240_ = crate::leanh::lean_box(0);
                if v_isShared_1237_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1236_, 0, v___x_1240_);
                    v___x_1242_ = v___x_1236_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1264_ = crate::leanh::lean_alloc_ctor(0, 1, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1240_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1264_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_failLv_1232_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1264_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                        v_outLv_1233_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1264_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 2) as u32,
                        v_ansiMode_1234_,
                    );
                    v___x_1242_ = v_reuseFailAlloc_1264_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_1231_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1230_, 0, v___x_1242_);
                    v___x_1244_ = v___x_1230_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1263_ = crate::leanh::lean_alloc_ctor(0, 3, (5) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1242_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_outputsFile_x3f_1227_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1263_,
                        2,
                        v_leanOptOverrides_1228_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1263_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_oldMode_1222_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1263_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_trustHash_1223_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1263_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
                        v_noBuild_1224_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1263_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 3) as u32,
                        v_verbosity_1225_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1263_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 4) as u32,
                        v_showSuccess_1226_,
                    );
                    v___x_1244_ = v_reuseFailAlloc_1263_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_inc(v_a_1173_);
                v___x_1245_ =
                    l_Lake_Workspace_runBuild___redArg(v_a_1173_, v___f_1239_, v___x_1244_);
                if crate::leanh::lean_obj_tag(v___x_1245_) == 0 {
                    v_isSharedCheck_1253_ = (!crate::leanh::lean_is_exclusive(v___x_1245_)) as u8;
                    if v_isSharedCheck_1253_ == 0 {
                        v_unused_1254_ = crate::leanh::lean_ctor_get(v___x_1245_, 0);
                        crate::leanh::lean_dec(v_unused_1254_);
                        v___x_1247_ = v___x_1245_;
                        v_isShared_1248_ = v_isSharedCheck_1253_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1245_);
                        v___x_1247_ = crate::leanh::lean_box(0);
                        v_isShared_1248_ = v_isSharedCheck_1253_;
                        state = 10;
                        continue;
                    }
                } else {
                    v_a_1255_ = crate::leanh::lean_ctor_get(v___x_1245_, 0);
                    v_isSharedCheck_1262_ = (!crate::leanh::lean_is_exclusive(v___x_1245_)) as u8;
                    if v_isSharedCheck_1262_ == 0 {
                        v___x_1257_ = v___x_1245_;
                        v_isShared_1258_ = v_isSharedCheck_1262_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1255_);
                        crate::leanh::lean_dec(v___x_1245_);
                        v___x_1257_ = crate::leanh::lean_box(0);
                        v_isShared_1258_ = v_isSharedCheck_1262_;
                        state = 12;
                        continue;
                    }
                }
            }
            10 => {
                v___x_1249_ = l_Lake_Package_test___boxed__const__1;
                if v_isShared_1248_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1247_, 0, v___x_1249_);
                    v___x_1251_ = v___x_1247_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1252_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1249_);
                    v___x_1251_ = v_reuseFailAlloc_1252_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1251_;
            }
            12 => {
                if v_isShared_1258_ == 0 {
                    v___x_1260_ = v___x_1257_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1261_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1255_);
                    v___x_1260_ = v_reuseFailAlloc_1261_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1260_;
            }
            14 => {
                if v_isShared_1291_ == 0 {
                    v___x_1293_ = v___x_1290_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1294_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
                    v___x_1293_ = v_reuseFailAlloc_1294_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1293_;
            }
            16 => {
                if v_isShared_1300_ == 0 {
                    v___x_1302_ = v___x_1299_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1303_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
                    v___x_1302_ = v_reuseFailAlloc_1303_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1302_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_test___boxed(
    mut v_pkg_1305_: *mut crate::leanh::LeanObject,
    mut v_args_1306_: *mut crate::leanh::LeanObject,
    mut v_buildConfig_1307_: *mut crate::leanh::LeanObject,
    mut v_a_1308_: *mut crate::leanh::LeanObject,
    mut v_a_1309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1310_ = l_Lake_Package_test(v_pkg_1305_, v_args_1306_, v_buildConfig_1307_, v_a_1308_);
    crate::leanh::lean_dec(v_a_1308_);
    return v_res_1310_;
}
pub unsafe fn l_Lake_Package_lint(
    mut v_pkg_1313_: *mut crate::leanh::LeanObject,
    mut v_args_1314_: *mut crate::leanh::LeanObject,
    mut v_buildConfig_1315_: *mut crate::leanh::LeanObject,
    mut v_a_1316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lintDriver_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1325_: u8 = 0;
    let mut v_fst_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lintDriverArgs_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_baseName_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scripts_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: u8 = 0;
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: u8 = 0;
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1367_: u8 = 0;
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1371_: u8 = 0;
    let mut v_isSharedCheck_1372_: u8 = 0;
    let mut v_a_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1376_: u8 = 0;
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_config_1318_ = crate::leanh::lean_ctor_get(v_pkg_1313_, 6);
                crate::leanh::lean_inc_ref(v_config_1318_);
                v_lintDriver_1319_ = crate::leanh::lean_ctor_get(v_pkg_1313_, 22);
                crate::leanh::lean_inc_ref(v_lintDriver_1319_);
                v___x_1320_ = l_Lake_Package_lint___closed__0;
                v___x_1321_ = l_Lake_Package_resolveDriver(
                    v_pkg_1313_,
                    v___x_1320_,
                    v_lintDriver_1319_,
                    v_a_1316_,
                );
                if crate::leanh::lean_obj_tag(v___x_1321_) == 0 {
                    v_a_1322_ = crate::leanh::lean_ctor_get(v___x_1321_, 0);
                    v_isSharedCheck_1372_ = (!crate::leanh::lean_is_exclusive(v___x_1321_)) as u8;
                    if v_isSharedCheck_1372_ == 0 {
                        v___x_1324_ = v___x_1321_;
                        v_isShared_1325_ = v_isSharedCheck_1372_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1322_);
                        crate::leanh::lean_dec(v___x_1321_);
                        v___x_1324_ = crate::leanh::lean_box(0);
                        v_isShared_1325_ = v_isSharedCheck_1372_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_config_1318_);
                    crate::leanh::lean_dec_ref(v_buildConfig_1315_);
                    crate::leanh::lean_dec(v_args_1314_);
                    v_a_1373_ = crate::leanh::lean_ctor_get(v___x_1321_, 0);
                    v_isSharedCheck_1380_ = (!crate::leanh::lean_is_exclusive(v___x_1321_)) as u8;
                    if v_isSharedCheck_1380_ == 0 {
                        v___x_1375_ = v___x_1321_;
                        v_isShared_1376_ = v_isSharedCheck_1380_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1373_);
                        crate::leanh::lean_dec(v___x_1321_);
                        v___x_1375_ = crate::leanh::lean_box(0);
                        v_isShared_1376_ = v_isSharedCheck_1380_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1326_ = crate::leanh::lean_ctor_get(v_a_1322_, 0);
                crate::leanh::lean_inc(v_fst_1326_);
                v_snd_1327_ = crate::leanh::lean_ctor_get(v_a_1322_, 1);
                crate::leanh::lean_inc_n(v_snd_1327_, 2);
                crate::leanh::lean_dec(v_a_1322_);
                v_lintDriverArgs_1328_ = crate::leanh::lean_ctor_get(v_config_1318_, 15);
                crate::leanh::lean_inc_ref(v_lintDriverArgs_1328_);
                crate::leanh::lean_dec_ref(v_config_1318_);
                v_baseName_1329_ = crate::leanh::lean_ctor_get(v_fst_1326_, 1);
                v_keyName_1330_ = crate::leanh::lean_ctor_get(v_fst_1326_, 2);
                crate::leanh::lean_inc(v_keyName_1330_);
                v_scripts_1331_ = crate::leanh::lean_ctor_get(v_fst_1326_, 17);
                v___x_1344_ = l_String_toName(v_snd_1327_);
                v___x_1345_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_scripts_1331_, v___x_1344_);
                if crate::leanh::lean_obj_tag(v___x_1345_) == 1 {
                    crate::leanh::lean_dec(v___x_1344_);
                    crate::leanh::lean_dec(v_keyName_1330_);
                    crate::leanh::lean_dec(v_snd_1327_);
                    crate::leanh::lean_dec(v_fst_1326_);
                    crate::leanh::lean_del_object(v___x_1324_);
                    crate::leanh::lean_dec_ref(v_buildConfig_1315_);
                    v_val_1346_ = crate::leanh::lean_ctor_get(v___x_1345_, 0);
                    crate::leanh::lean_inc(v_val_1346_);
                    crate::leanh::lean_dec_ref_known(v___x_1345_, 1);
                    v___x_1347_ = lean_array_to_list(v_lintDriverArgs_1328_);
                    v___x_1348_ = l_List_appendTR___redArg(v___x_1347_, v_args_1314_);
                    v___x_1349_ = l_Lake_Script_run(v___x_1348_, v_val_1346_, v_a_1316_);
                    return v___x_1349_;
                } else {
                    crate::leanh::lean_dec(v___x_1345_);
                    v___x_1350_ = l_Lake_Package_findTargetDecl_x3f(v___x_1344_, v_fst_1326_);
                    crate::leanh::lean_dec(v___x_1344_);
                    if crate::leanh::lean_obj_tag(v___x_1350_) == 0 {
                        crate::leanh::lean_inc(v_baseName_1329_);
                        crate::leanh::lean_dec(v_keyName_1330_);
                        crate::leanh::lean_dec_ref(v_lintDriverArgs_1328_);
                        crate::leanh::lean_dec(v_fst_1326_);
                        crate::leanh::lean_dec_ref(v_buildConfig_1315_);
                        crate::leanh::lean_dec(v_args_1314_);
                        state = 2;
                        continue;
                    } else {
                        v_val_1351_ = crate::leanh::lean_ctor_get(v___x_1350_, 0);
                        crate::leanh::lean_inc(v_val_1351_);
                        crate::leanh::lean_dec_ref_known(v___x_1350_, 1);
                        v_name_1352_ = crate::leanh::lean_ctor_get(v_val_1351_, 1);
                        crate::leanh::lean_inc(v_name_1352_);
                        v_kind_1353_ = crate::leanh::lean_ctor_get(v_val_1351_, 2);
                        crate::leanh::lean_inc(v_kind_1353_);
                        v_config_1354_ = crate::leanh::lean_ctor_get(v_val_1351_, 3);
                        crate::leanh::lean_inc(v_config_1354_);
                        crate::leanh::lean_dec(v_val_1351_);
                        v___x_1355_ = l_Lake_LeanExe_keyword;
                        v___x_1356_ = lean_name_eq(v_kind_1353_, v___x_1355_);
                        crate::leanh::lean_dec(v_kind_1353_);
                        if v___x_1356_ == 0 {
                            crate::leanh::lean_inc(v_baseName_1329_);
                            crate::leanh::lean_dec(v_config_1354_);
                            crate::leanh::lean_dec(v_name_1352_);
                            crate::leanh::lean_dec(v_keyName_1330_);
                            crate::leanh::lean_dec_ref(v_lintDriverArgs_1328_);
                            crate::leanh::lean_dec(v_fst_1326_);
                            crate::leanh::lean_dec_ref(v_buildConfig_1315_);
                            crate::leanh::lean_dec(v_args_1314_);
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_snd_1327_);
                            crate::leanh::lean_del_object(v___x_1324_);
                            crate::leanh::lean_inc(v_name_1352_);
                            v___x_1357_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1357_, 0, v_fst_1326_);
                            crate::leanh::lean_ctor_set(v___x_1357_, 1, v_name_1352_);
                            crate::leanh::lean_ctor_set(v___x_1357_, 2, v_config_1354_);
                            v___f_1358_ = crate::leanh::lean_alloc_closure(
                                l_Lake_Package_test___lam__1___boxed as *mut core::ffi::c_void,
                                11,
                                4,
                            );
                            crate::leanh::lean_closure_set(v___f_1358_, 0, v_keyName_1330_);
                            crate::leanh::lean_closure_set(v___f_1358_, 1, v_name_1352_);
                            crate::leanh::lean_closure_set(v___f_1358_, 2, v___x_1355_);
                            crate::leanh::lean_closure_set(v___f_1358_, 3, v___x_1357_);
                            crate::leanh::lean_inc(v_a_1316_);
                            v___x_1359_ = l_Lake_Workspace_runBuild___redArg(
                                v_a_1316_,
                                v___f_1358_,
                                v_buildConfig_1315_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1359_) == 0 {
                                v_a_1360_ = crate::leanh::lean_ctor_get(v___x_1359_, 0);
                                crate::leanh::lean_inc(v_a_1360_);
                                crate::leanh::lean_dec_ref_known(v___x_1359_, 1);
                                v___x_1361_ = lean_array_mk(v_args_1314_);
                                v___x_1362_ =
                                    l_Array_append___redArg(v_lintDriverArgs_1328_, v___x_1361_);
                                crate::leanh::lean_dec_ref(v___x_1361_);
                                v___x_1363_ = l_Lake_env(v_a_1360_, v___x_1362_, v_a_1316_);
                                return v___x_1363_;
                            } else {
                                crate::leanh::lean_dec_ref(v_lintDriverArgs_1328_);
                                crate::leanh::lean_dec(v_args_1314_);
                                v_a_1364_ = crate::leanh::lean_ctor_get(v___x_1359_, 0);
                                v_isSharedCheck_1371_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1359_)) as u8;
                                if v_isSharedCheck_1371_ == 0 {
                                    v___x_1366_ = v___x_1359_;
                                    v_isShared_1367_ = v_isSharedCheck_1371_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1364_);
                                    crate::leanh::lean_dec(v___x_1359_);
                                    v___x_1366_ = crate::leanh::lean_box(0);
                                    v_isShared_1367_ = v_isSharedCheck_1371_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_1333_ = 0;
                v___x_1334_ = l_Lean_Name_toString(v_baseName_1329_, v___x_1333_);
                v___x_1335_ = l_Lake_Package_lint___closed__1;
                v___x_1336_ = lean_string_append(v___x_1334_, v___x_1335_);
                v___x_1337_ = lean_string_append(v___x_1336_, v_snd_1327_);
                crate::leanh::lean_dec(v_snd_1327_);
                v___x_1338_ = l_Lake_Package_resolveDriver___closed__5;
                v___x_1339_ = lean_string_append(v___x_1337_, v___x_1338_);
                v___x_1340_ = lean_mk_io_user_error(v___x_1339_);
                if v_isShared_1325_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1324_, 1);
                    crate::leanh::lean_ctor_set(v___x_1324_, 0, v___x_1340_);
                    v___x_1342_ = v___x_1324_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1343_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
                    v___x_1342_ = v_reuseFailAlloc_1343_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1342_;
            }
            4 => {
                if v_isShared_1367_ == 0 {
                    v___x_1369_ = v___x_1366_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1370_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
                    v___x_1369_ = v_reuseFailAlloc_1370_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1369_;
            }
            6 => {
                if v_isShared_1376_ == 0 {
                    v___x_1378_ = v___x_1375_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1379_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
                    v___x_1378_ = v_reuseFailAlloc_1379_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1378_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_lint___boxed(
    mut v_pkg_1381_: *mut crate::leanh::LeanObject,
    mut v_args_1382_: *mut crate::leanh::LeanObject,
    mut v_buildConfig_1383_: *mut crate::leanh::LeanObject,
    mut v_a_1384_: *mut crate::leanh::LeanObject,
    mut v_a_1385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1386_ = l_Lake_Package_lint(v_pkg_1381_, v_args_1382_, v_buildConfig_1383_, v_a_1384_);
    crate::leanh::lean_dec(v_a_1384_);
    return v_res_1386_;
}
pub unsafe fn l_Lake_Workspace_evalLeanFile(
    mut v_ws_1387_: *mut crate::leanh::LeanObject,
    mut v_leanFile_1388_: *mut crate::leanh::LeanObject,
    mut v_moreArgs_1389_: *mut crate::leanh::LeanObject,
    mut v_buildConfig_1390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toStdioConfig_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1402_: u8 = 0;
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1406_: u8 = 0;
    let mut v_a_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1410_: u8 = 0;
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1414_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1392_ = crate::leanh::lean_alloc_closure(
                    l_Lake_prepareLeanCommand___boxed as *mut core::ffi::c_void,
                    9,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_1392_, 0, v_leanFile_1388_);
                crate::leanh::lean_closure_set(v___x_1392_, 1, v_moreArgs_1389_);
                v___x_1393_ = l_Lake_Workspace_runBuild___redArg(
                    v_ws_1387_,
                    v___x_1392_,
                    v_buildConfig_1390_,
                );
                if crate::leanh::lean_obj_tag(v___x_1393_) == 0 {
                    v_a_1394_ = crate::leanh::lean_ctor_get(v___x_1393_, 0);
                    crate::leanh::lean_inc_n(v_a_1394_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1393_, 1);
                    v___x_1395_ = lean_io_process_spawn(v_a_1394_);
                    if crate::leanh::lean_obj_tag(v___x_1395_) == 0 {
                        v_a_1396_ = crate::leanh::lean_ctor_get(v___x_1395_, 0);
                        crate::leanh::lean_inc(v_a_1396_);
                        crate::leanh::lean_dec_ref_known(v___x_1395_, 1);
                        v_toStdioConfig_1397_ = crate::leanh::lean_ctor_get(v_a_1394_, 0);
                        crate::leanh::lean_inc_ref(v_toStdioConfig_1397_);
                        crate::leanh::lean_dec(v_a_1394_);
                        v___x_1398_ = lean_io_process_child_wait(v_toStdioConfig_1397_, v_a_1396_);
                        crate::leanh::lean_dec(v_a_1396_);
                        crate::leanh::lean_dec_ref(v_toStdioConfig_1397_);
                        return v___x_1398_;
                    } else {
                        crate::leanh::lean_dec(v_a_1394_);
                        v_a_1399_ = crate::leanh::lean_ctor_get(v___x_1395_, 0);
                        v_isSharedCheck_1406_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1395_)) as u8;
                        if v_isSharedCheck_1406_ == 0 {
                            v___x_1401_ = v___x_1395_;
                            v_isShared_1402_ = v_isSharedCheck_1406_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1399_);
                            crate::leanh::lean_dec(v___x_1395_);
                            v___x_1401_ = crate::leanh::lean_box(0);
                            v_isShared_1402_ = v_isSharedCheck_1406_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_1407_ = crate::leanh::lean_ctor_get(v___x_1393_, 0);
                    v_isSharedCheck_1414_ = (!crate::leanh::lean_is_exclusive(v___x_1393_)) as u8;
                    if v_isSharedCheck_1414_ == 0 {
                        v___x_1409_ = v___x_1393_;
                        v_isShared_1410_ = v_isSharedCheck_1414_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1407_);
                        crate::leanh::lean_dec(v___x_1393_);
                        v___x_1409_ = crate::leanh::lean_box(0);
                        v_isShared_1410_ = v_isSharedCheck_1414_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1402_ == 0 {
                    v___x_1404_ = v___x_1401_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1405_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
                    v___x_1404_ = v_reuseFailAlloc_1405_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1404_;
            }
            3 => {
                if v_isShared_1410_ == 0 {
                    v___x_1412_ = v___x_1409_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1413_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
                    v___x_1412_ = v_reuseFailAlloc_1413_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1412_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Workspace_evalLeanFile___boxed(
    mut v_ws_1415_: *mut crate::leanh::LeanObject,
    mut v_leanFile_1416_: *mut crate::leanh::LeanObject,
    mut v_moreArgs_1417_: *mut crate::leanh::LeanObject,
    mut v_buildConfig_1418_: *mut crate::leanh::LeanObject,
    mut v_a_1419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1420_ = l_Lake_Workspace_evalLeanFile(
        v_ws_1415_,
        v_leanFile_1416_,
        v_moreArgs_1417_,
        v_buildConfig_1418_,
    );
    return v_res_1420_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_CLI_Actions(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Workspace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Run(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Actions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Targets(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Module(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Proc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lake_Package_test___boxed__const__1 = _init_l_Lake_Package_test___boxed__const__1();
    crate::leanh::lean_mark_persistent(l_Lake_Package_test___boxed__const__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_CLI_Actions(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_CLI_Actions(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Workspace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Run(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Actions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Targets(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Module(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Proc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_CLI_Actions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_CLI_Actions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_CLI_Actions(builtin);
}
