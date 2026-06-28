// Lean compiler output
// Module: Lake.Util.Git
// Imports: Init.Data.ToString Lake.Util.Proc Init.Data.String.TakeDrop Init.Data.String.Search Lake.Util.String
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::FindPos::l_String_Slice_Pos_prevn;
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::{l_String_Slice_toString, l_String_Slice_trimAscii};
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::Data::ToString::{
    initialize_Init_Data_ToString, runtime_initialize_Init_Data_ToString,
};
use crate::r#gen::Init::System::IO::l_System_FilePath_isDir;
use crate::r#gen::Lake::Util::Proc::{
    initialize_Lake_Util_Proc, l_Lake_captureProc_x3f, l_Lake_captureProc_x27, l_Lake_proc,
    l_Lake_testProc, runtime_initialize_Lake_Util_Proc,
};
use crate::r#gen::Lake::Util::String::{
    initialize_Lake_Util_String, l_Lake_isHex, runtime_initialize_Lake_Util_String,
};
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_extract, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_sub, lean_string_utf8_byte_size,
    lean_uint32_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lake_Git_defaultRemote___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [111, 114, 105, 103, 105, 110, 0],
};
static mut l_Lake_Git_defaultRemote___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Git_defaultRemote___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Git_defaultRemote: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Git_defaultRemote___closed__0_value) as *mut LeanObject;
pub static l_Lake_Git_upstreamBranch___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [109, 97, 115, 116, 101, 114, 0],
};
static mut l_Lake_Git_upstreamBranch___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Git_upstreamBranch___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Git_upstreamBranch: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Git_upstreamBranch___closed__0_value) as *mut LeanObject;
pub static l_Lake_Git_filterUrl_x3f___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [46, 103, 105, 116, 0],
};
static mut l_Lake_Git_filterUrl_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Git_filterUrl_x3f___closed__0_value) as *mut LeanObject;
static mut l_Lake_Git_filterUrl_x3f___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Git_filterUrl_x3f___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Git_filterUrl_x3f___closed__2_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [103, 105, 116, 0],
};
static mut l_Lake_Git_filterUrl_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Git_filterUrl_x3f___closed__2_value) as *mut LeanObject;
static mut l_Lake_Git_filterUrl_x3f___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Git_filterUrl_x3f___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_GitRev_head___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [72, 69, 65, 68, 0],
};
static mut l_Lake_GitRev_head___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRev_head___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_GitRev_head: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRev_head___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRev_fetchHead___closed__0_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [70, 69, 84, 67, 72, 95, 72, 69, 65, 68, 0],
};
static mut l_Lake_GitRev_fetchHead___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRev_fetchHead___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_GitRev_fetchHead: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRev_fetchHead___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRev_withRemote___closed__0_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [47, 0],
};
static mut l_Lake_GitRev_withRemote___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRev_withRemote___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRepo_instCoeFilePath___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_GitRepo_instCoeFilePath___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_GitRepo_instCoeFilePath___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_instCoeFilePath___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_GitRepo_instCoeFilePath: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_instCoeFilePath___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_GitRepo_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_instCoeFilePath___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRepo_cwd___closed__0_value: LeanStringObject<2> = LeanStringObject {
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
static mut l_Lake_GitRepo_cwd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_cwd___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_GitRepo_cwd: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_cwd___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRepo_captureGit___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [65793 as *mut LeanObject],
};
static mut l_Lake_GitRepo_captureGit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_captureGit___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRepo_captureGit___closed__1_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lake_GitRepo_captureGit___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_captureGit___closed__1_value) as *mut LeanObject;
pub static l_Lake_GitRepo_clone___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [99, 108, 111, 110, 101, 0],
};
static mut l_Lake_GitRepo_clone___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_clone___closed__0_value) as *mut LeanObject;
static mut l_Lake_GitRepo_clone___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_clone___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_GitRepo_quietInit___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [105, 110, 105, 116, 0],
};
static mut l_Lake_GitRepo_quietInit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_quietInit___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRepo_quietInit___closed__1_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [45, 113, 0],
};
static mut l_Lake_GitRepo_quietInit___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_quietInit___closed__1_value) as *mut LeanObject;
pub static l_Lake_GitRepo_quietInit___closed__2_value: LeanArrayObject<2> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 2,
    m_capacity: 2,
    m_data: [
        core::ptr::addr_of!(l_Lake_GitRepo_quietInit___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_GitRepo_quietInit___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lake_GitRepo_quietInit___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_quietInit___closed__2_value) as *mut LeanObject;
pub static l_Lake_GitRepo_bareInit___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [45, 45, 98, 97, 114, 101, 0],
};
static mut l_Lake_GitRepo_bareInit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_bareInit___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRepo_bareInit___closed__1_value: LeanArrayObject<3> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 3,
    m_capacity: 3,
    m_data: [
        core::ptr::addr_of!(l_Lake_GitRepo_quietInit___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_GitRepo_bareInit___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_GitRepo_quietInit___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lake_GitRepo_bareInit___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_bareInit___closed__1_value) as *mut LeanObject;
pub static l_Lake_GitRepo_insideWorkTree___closed__0_value: LeanStringObject<10> =
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
        m_data: [114, 101, 118, 45, 112, 97, 114, 115, 101, 0],
    };
static mut l_Lake_GitRepo_insideWorkTree___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_insideWorkTree___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRepo_insideWorkTree___closed__1_value: LeanStringObject<22> =
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
            45, 45, 105, 115, 45, 105, 110, 115, 105, 100, 101, 45, 119, 111, 114, 107, 45, 116,
            114, 101, 101, 0,
        ],
    };
static mut l_Lake_GitRepo_insideWorkTree___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_insideWorkTree___closed__1_value) as *mut LeanObject;
pub static l_Lake_GitRepo_insideWorkTree___closed__2_value: LeanArrayObject<2> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 2,
    m_capacity: 2,
    m_data: [
        core::ptr::addr_of!(l_Lake_GitRepo_insideWorkTree___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_GitRepo_insideWorkTree___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lake_GitRepo_insideWorkTree___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_insideWorkTree___closed__2_value) as *mut LeanObject;
pub static l_Lake_GitRepo_fetch___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [102, 101, 116, 99, 104, 0],
};
static mut l_Lake_GitRepo_fetch___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_fetch___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRepo_fetch___closed__1_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [45, 45, 116, 97, 103, 115, 0],
};
static mut l_Lake_GitRepo_fetch___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_fetch___closed__1_value) as *mut LeanObject;
pub static l_Lake_GitRepo_fetch___closed__2_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [45, 45, 102, 111, 114, 99, 101, 0],
};
static mut l_Lake_GitRepo_fetch___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_fetch___closed__2_value) as *mut LeanObject;
static mut l_Lake_GitRepo_fetch___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_fetch___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_GitRepo_fetch___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_fetch___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_GitRepo_fetch___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_fetch___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_GitRepo_addWorktreeDetach___closed__0_value: LeanStringObject<9> =
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
        m_data: [119, 111, 114, 107, 116, 114, 101, 101, 0],
    };
static mut l_Lake_GitRepo_addWorktreeDetach___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_addWorktreeDetach___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRepo_addWorktreeDetach___closed__1_value: LeanStringObject<4> =
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
        m_data: [97, 100, 100, 0],
    };
static mut l_Lake_GitRepo_addWorktreeDetach___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_addWorktreeDetach___closed__1_value) as *mut LeanObject;
pub static l_Lake_GitRepo_addWorktreeDetach___closed__2_value: LeanStringObject<9> =
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
        m_data: [45, 45, 100, 101, 116, 97, 99, 104, 0],
    };
static mut l_Lake_GitRepo_addWorktreeDetach___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_addWorktreeDetach___closed__2_value) as *mut LeanObject;
static mut l_Lake_GitRepo_addWorktreeDetach___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_addWorktreeDetach___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_GitRepo_addWorktreeDetach___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_addWorktreeDetach___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_GitRepo_addWorktreeDetach___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_addWorktreeDetach___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_GitRepo_checkoutBranch___closed__0_value: LeanStringObject<9> =
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
        m_data: [99, 104, 101, 99, 107, 111, 117, 116, 0],
    };
static mut l_Lake_GitRepo_checkoutBranch___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_checkoutBranch___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRepo_checkoutBranch___closed__1_value: LeanStringObject<3> =
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
        m_data: [45, 66, 0],
    };
static mut l_Lake_GitRepo_checkoutBranch___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_checkoutBranch___closed__1_value) as *mut LeanObject;
static mut l_Lake_GitRepo_checkoutBranch___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_checkoutBranch___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_GitRepo_checkoutBranch___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_checkoutBranch___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_GitRepo_checkoutDetach___closed__0_value: LeanStringObject<3> =
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
        m_data: [45, 45, 0],
    };
static mut l_Lake_GitRepo_checkoutDetach___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_checkoutDetach___closed__0_value) as *mut LeanObject;
static mut l_Lake_GitRepo_checkoutDetach___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_checkoutDetach___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_GitRepo_checkoutDetach___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_checkoutDetach___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_GitRepo_clean___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [99, 108, 101, 97, 110, 0],
};
static mut l_Lake_GitRepo_clean___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_clean___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRepo_clean___closed__1_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [45, 120, 102, 0],
};
static mut l_Lake_GitRepo_clean___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_clean___closed__1_value) as *mut LeanObject;
pub static l_Lake_GitRepo_clean___closed__2_value: LeanArrayObject<2> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 2,
    m_capacity: 2,
    m_data: [
        core::ptr::addr_of!(l_Lake_GitRepo_clean___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_GitRepo_clean___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lake_GitRepo_clean___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_clean___closed__2_value) as *mut LeanObject;
pub static l_Lake_GitRepo_resolveRevision_x3f___closed__0_value: LeanStringObject<9> =
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
        m_data: [45, 45, 118, 101, 114, 105, 102, 121, 0],
    };
static mut l_Lake_GitRepo_resolveRevision_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_resolveRevision_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRepo_resolveRevision_x3f___closed__1_value: LeanStringObject<17> =
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
            45, 45, 101, 110, 100, 45, 111, 102, 45, 111, 112, 116, 105, 111, 110, 115, 0,
        ],
    };
static mut l_Lake_GitRepo_resolveRevision_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_resolveRevision_x3f___closed__1_value) as *mut LeanObject;
static mut l_Lake_GitRepo_resolveRevision_x3f___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_resolveRevision_x3f___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_GitRepo_resolveRevision_x3f___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_resolveRevision_x3f___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_GitRepo_resolveRevision_x3f___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_resolveRevision_x3f___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_GitRepo_findCommit_x3f___closed__0_value: LeanStringObject<10> =
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
        m_data: [94, 123, 99, 111, 109, 109, 105, 116, 125, 0],
    };
static mut l_Lake_GitRepo_findCommit_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_findCommit_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRepo_resolveRevision___closed__0_value: LeanStringObject<23> =
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
            58, 32, 114, 101, 118, 105, 115, 105, 111, 110, 32, 110, 111, 116, 32, 102, 111, 117,
            110, 100, 32, 39, 0,
        ],
    };
static mut l_Lake_GitRepo_resolveRevision___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_resolveRevision___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRepo_resolveRevision___closed__1_value: LeanStringObject<2> =
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
static mut l_Lake_GitRepo_resolveRevision___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_resolveRevision___closed__1_value) as *mut LeanObject;
pub static l_Lake_GitRepo_getHeadRevision___closed__0_value: LeanStringObject<114> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 114,
        m_capacity: 114,
        m_length: 113,
        m_data: [
            58, 32, 99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 114, 101, 115, 111, 108, 118,
            101, 32, 39, 72, 69, 65, 68, 39, 32, 116, 111, 32, 97, 32, 99, 111, 109, 109, 105, 116,
            59, 32, 116, 104, 101, 32, 114, 101, 112, 111, 115, 105, 116, 111, 114, 121, 32, 109,
            97, 121, 32, 98, 101, 32, 99, 111, 114, 114, 117, 112, 116, 44, 32, 115, 111, 32, 121,
            111, 117, 32, 109, 97, 121, 32, 110, 101, 101, 100, 32, 116, 111, 32, 114, 101, 109,
            111, 118, 101, 32, 105, 116, 32, 97, 110, 100, 32, 116, 114, 121, 32, 97, 103, 97, 105,
            110, 0,
        ],
    };
static mut l_Lake_GitRepo_getHeadRevision___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_getHeadRevision___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRepo_fetchRevision_x3f___closed__0_value: LeanStringObject<10> =
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
        m_data: [45, 45, 114, 101, 102, 101, 116, 99, 104, 0],
    };
static mut l_Lake_GitRepo_fetchRevision_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_fetchRevision_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRepo_fetchRevision_x3f___closed__1_value: LeanStringObject<16> =
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
            45, 45, 102, 105, 108, 116, 101, 114, 61, 116, 114, 101, 101, 58, 48, 0,
        ],
    };
static mut l_Lake_GitRepo_fetchRevision_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_fetchRevision_x3f___closed__1_value) as *mut LeanObject;
static mut l_Lake_GitRepo_fetchRevision_x3f___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_fetchRevision_x3f___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_GitRepo_fetchRevision_x3f___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_fetchRevision_x3f___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_GitRepo_fetchRevision_x3f___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_fetchRevision_x3f___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_GitRepo_fetchRevision_x3f___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_fetchRevision_x3f___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_GitRepo_fetchRevision_x3f___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_fetchRevision_x3f___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_GitRepo_fetchRevision_x3f___closed__7_value: LeanStringObject<110> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 110,
        m_capacity: 110,
        m_length: 109,
        m_data: [
            58, 32, 99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 114, 101, 115, 111, 108, 118,
            101, 32, 39, 70, 69, 84, 67, 72, 95, 72, 69, 65, 68, 39, 32, 116, 111, 32, 97, 32, 99,
            111, 109, 109, 105, 116, 32, 97, 102, 116, 101, 114, 32, 102, 101, 116, 99, 104, 105,
            110, 103, 59, 32, 116, 104, 105, 115, 32, 109, 97, 121, 32, 98, 101, 32, 97, 110, 32,
            105, 115, 115, 117, 101, 32, 119, 105, 116, 104, 32, 76, 97, 107, 101, 59, 32, 112,
            108, 101, 97, 115, 101, 32, 114, 101, 112, 111, 114, 116, 32, 105, 116, 0,
        ],
    };
static mut l_Lake_GitRepo_fetchRevision_x3f___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_fetchRevision_x3f___closed__7_value) as *mut LeanObject;
pub static l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRepo_getHeadRevisions___closed__0_value: LeanStringObject<9> =
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
        m_data: [114, 101, 118, 45, 108, 105, 115, 116, 0],
    };
static mut l_Lake_GitRepo_getHeadRevisions___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_getHeadRevisions___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRepo_getHeadRevisions___closed__1_value: LeanArrayObject<2> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 2,
        m_capacity: 2,
        m_data: [
            core::ptr::addr_of!(l_Lake_GitRepo_getHeadRevisions___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_GitRev_head___closed__0_value) as *mut LeanObject,
        ],
    };
static mut l_Lake_GitRepo_getHeadRevisions___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_getHeadRevisions___closed__1_value) as *mut LeanObject;
pub static l_Lake_GitRepo_getHeadRevisions___closed__2_value: LeanStringObject<3> =
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
        m_data: [45, 110, 0],
    };
static mut l_Lake_GitRepo_getHeadRevisions___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_getHeadRevisions___closed__2_value) as *mut LeanObject;
static mut l_Lake_GitRepo_getHeadRevisions___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_getHeadRevisions___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_GitRepo_branchExists___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [115, 104, 111, 119, 45, 114, 101, 102, 0],
};
static mut l_Lake_GitRepo_branchExists___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_branchExists___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRepo_branchExists___closed__1_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [114, 101, 102, 115, 47, 104, 101, 97, 100, 115, 47, 0],
};
static mut l_Lake_GitRepo_branchExists___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_branchExists___closed__1_value) as *mut LeanObject;
static mut l_Lake_GitRepo_branchExists___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_branchExists___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_GitRepo_branchExists___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_branchExists___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_GitRepo_revisionExists___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_revisionExists___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_GitRepo_revisionExists___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_revisionExists___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_GitRepo_getTags___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [116, 97, 103, 0],
};
static mut l_Lake_GitRepo_getTags___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_getTags___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRepo_getTags___closed__1_value: LeanArrayObject<1> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 1,
    m_capacity: 1,
    m_data: [core::ptr::addr_of!(l_Lake_GitRepo_getTags___closed__0_value) as *mut LeanObject],
};
static mut l_Lake_GitRepo_getTags___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_getTags___closed__1_value) as *mut LeanObject;
pub static l_Lake_GitRepo_findTag_x3f___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [100, 101, 115, 99, 114, 105, 98, 101, 0],
};
static mut l_Lake_GitRepo_findTag_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_findTag_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRepo_findTag_x3f___closed__1_value: LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [45, 45, 101, 120, 97, 99, 116, 45, 109, 97, 116, 99, 104, 0],
};
static mut l_Lake_GitRepo_findTag_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_findTag_x3f___closed__1_value) as *mut LeanObject;
static mut l_Lake_GitRepo_findTag_x3f___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_findTag_x3f___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_GitRepo_findTag_x3f___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_findTag_x3f___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_GitRepo_findTag_x3f___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_findTag_x3f___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_GitRepo_getRemoteUrl_x3f___closed__0_value: LeanStringObject<7> =
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
        m_data: [114, 101, 109, 111, 116, 101, 0],
    };
static mut l_Lake_GitRepo_getRemoteUrl_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_getRemoteUrl_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRepo_getRemoteUrl_x3f___closed__1_value: LeanStringObject<8> =
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
        m_data: [103, 101, 116, 45, 117, 114, 108, 0],
    };
static mut l_Lake_GitRepo_getRemoteUrl_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_getRemoteUrl_x3f___closed__1_value) as *mut LeanObject;
static mut l_Lake_GitRepo_getRemoteUrl_x3f___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_getRemoteUrl_x3f___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_GitRepo_getRemoteUrl_x3f___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_getRemoteUrl_x3f___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_GitRepo_addRemote___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_addRemote___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_GitRepo_addRemote___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_addRemote___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_GitRepo_setRemoteUrl___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [115, 101, 116, 45, 117, 114, 108, 0],
};
static mut l_Lake_GitRepo_setRemoteUrl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_setRemoteUrl___closed__0_value) as *mut LeanObject;
static mut l_Lake_GitRepo_setRemoteUrl___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_GitRepo_setRemoteUrl___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_GitRepo_hasNoDiff___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [100, 105, 102, 102, 0],
};
static mut l_Lake_GitRepo_hasNoDiff___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_hasNoDiff___closed__0_value) as *mut LeanObject;
pub static l_Lake_GitRepo_hasNoDiff___closed__1_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [45, 45, 101, 120, 105, 116, 45, 99, 111, 100, 101, 0],
};
static mut l_Lake_GitRepo_hasNoDiff___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_hasNoDiff___closed__1_value) as *mut LeanObject;
pub static l_Lake_GitRepo_hasNoDiff___closed__2_value: LeanArrayObject<3> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 3,
    m_capacity: 3,
    m_data: [
        core::ptr::addr_of!(l_Lake_GitRepo_hasNoDiff___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_GitRepo_hasNoDiff___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_GitRev_head___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lake_GitRepo_hasNoDiff___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_GitRepo_hasNoDiff___closed__2_value) as *mut LeanObject;
pub unsafe fn _init_l_Lake_Git_filterUrl_x3f___closed__1() -> *mut LeanObject {
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    v___x_1020_ = l_Lake_Git_filterUrl_x3f___closed__0;
    v___x_1021_ = lean_string_utf8_byte_size(v___x_1020_);
    return v___x_1021_;
}
pub unsafe fn _init_l_Lake_Git_filterUrl_x3f___closed__3() -> *mut LeanObject {
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    v___x_1023_ = l_Lake_Git_filterUrl_x3f___closed__2;
    v___x_1024_ = lean_string_utf8_byte_size(v___x_1023_);
    return v___x_1024_;
}
pub unsafe fn l_Lake_Git_filterUrl_x3f(mut v_url_1025_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: u8 = 0;
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: u8 = 0;
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: u8 = 0;
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: u8 = 0;
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1041_ = l_Lake_Git_filterUrl_x3f___closed__2;
                v___x_1042_ = lean_string_utf8_byte_size(v_url_1025_);
                v___x_1043_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_Git_filterUrl_x3f___closed__3),
                    core::ptr::addr_of_mut!(l_Lake_Git_filterUrl_x3f___closed__3_once),
                    _init_l_Lake_Git_filterUrl_x3f___closed__3,
                );
                v___x_1044_ = lean_nat_dec_le(v___x_1043_, v___x_1042_);
                if v___x_1044_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_1045_ = lean_unsigned_to_nat(0);
                    v___x_1046_ = lean_string_memcmp(
                        v_url_1025_,
                        v___x_1041_,
                        v___x_1045_,
                        v___x_1045_,
                        v___x_1043_,
                    );
                    if v___x_1046_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_url_1025_);
                        v___x_1047_ = lean_box(0);
                        return v___x_1047_;
                    }
                }
            }
            1 => {
                v___x_1027_ = l_Lake_Git_filterUrl_x3f___closed__0;
                v___x_1028_ = lean_string_utf8_byte_size(v_url_1025_);
                v___x_1029_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_Git_filterUrl_x3f___closed__1),
                    core::ptr::addr_of_mut!(l_Lake_Git_filterUrl_x3f___closed__1_once),
                    _init_l_Lake_Git_filterUrl_x3f___closed__1,
                );
                v___x_1030_ = lean_nat_dec_le(v___x_1029_, v___x_1028_);
                if v___x_1030_ == 0 {
                    v___x_1031_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1031_, 0, v_url_1025_);
                    return v___x_1031_;
                } else {
                    v___x_1032_ = lean_unsigned_to_nat(0);
                    v___x_1033_ = lean_nat_sub(v___x_1028_, v___x_1029_);
                    v___x_1034_ = lean_string_memcmp(
                        v_url_1025_,
                        v___x_1027_,
                        v___x_1033_,
                        v___x_1032_,
                        v___x_1029_,
                    );
                    lean_dec(v___x_1033_);
                    if v___x_1034_ == 0 {
                        v___x_1035_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1035_, 0, v_url_1025_);
                        return v___x_1035_;
                    } else {
                        v___x_1036_ = lean_unsigned_to_nat(4);
                        lean_inc_ref(v_url_1025_);
                        v___x_1037_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_1037_, 0, v_url_1025_);
                        lean_ctor_set(v___x_1037_, 1, v___x_1032_);
                        lean_ctor_set(v___x_1037_, 2, v___x_1028_);
                        v___x_1038_ =
                            l_String_Slice_Pos_prevn(v___x_1037_, v___x_1028_, v___x_1036_);
                        lean_dec_ref_known(v___x_1037_, 3);
                        v___x_1039_ =
                            lean_string_utf8_extract(v_url_1025_, v___x_1032_, v___x_1038_);
                        lean_dec(v___x_1038_);
                        lean_dec_ref(v_url_1025_);
                        v___x_1040_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1040_, 0, v___x_1039_);
                        return v___x_1040_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Git_isFullObjectName(mut v_rev_1048_: *mut LeanObject) -> u8 {
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: u8 = 0;
    v___x_1049_ = lean_string_utf8_byte_size(v_rev_1048_);
    v___x_1050_ = lean_unsigned_to_nat(40);
    v___x_1051_ = lean_nat_dec_eq(v___x_1049_, v___x_1050_);
    if v___x_1051_ == 0 {
        return v___x_1051_;
    } else {
        let mut v___x_1052_: u8 = 0;
        v___x_1052_ = l_Lake_isHex(v_rev_1048_);
        return v___x_1052_;
    }
}
pub unsafe fn l_Lake_Git_isFullObjectName___boxed(
    mut v_rev_1053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1054_: u8 = 0;
    let mut v_r_1055_: *mut LeanObject = core::ptr::null_mut();
    v_res_1054_ = l_Lake_Git_isFullObjectName(v_rev_1053_);
    lean_dec_ref(v_rev_1053_);
    v_r_1055_ = lean_box((v_res_1054_) as usize);
    return v_r_1055_;
}
pub unsafe fn l_Lake_GitRev_isFullSha1(mut v_rev_1060_: *mut LeanObject) -> u8 {
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: u8 = 0;
    v___x_1061_ = lean_string_utf8_byte_size(v_rev_1060_);
    v___x_1062_ = lean_unsigned_to_nat(40);
    v___x_1063_ = lean_nat_dec_eq(v___x_1061_, v___x_1062_);
    if v___x_1063_ == 0 {
        return v___x_1063_;
    } else {
        let mut v___x_1064_: u8 = 0;
        v___x_1064_ = l_Lake_isHex(v_rev_1060_);
        return v___x_1064_;
    }
}
pub unsafe fn l_Lake_GitRev_isFullSha1___boxed(
    mut v_rev_1065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1066_: u8 = 0;
    let mut v_r_1067_: *mut LeanObject = core::ptr::null_mut();
    v_res_1066_ = l_Lake_GitRev_isFullSha1(v_rev_1065_);
    lean_dec_ref(v_rev_1065_);
    v_r_1067_ = lean_box((v_res_1066_) as usize);
    return v_r_1067_;
}
pub unsafe fn l_Lake_GitRev_withRemote(
    mut v_remote_1069_: *mut LeanObject,
    mut v_rev_1070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    v___x_1071_ = l_Lake_GitRev_withRemote___closed__0;
    v___x_1072_ = lean_string_append(v_remote_1069_, v___x_1071_);
    v___x_1073_ = lean_string_append(v___x_1072_, v_rev_1070_);
    return v___x_1073_;
}
pub unsafe fn l_Lake_GitRev_withRemote___boxed(
    mut v_remote_1074_: *mut LeanObject,
    mut v_rev_1075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1076_: *mut LeanObject = core::ptr::null_mut();
    v_res_1076_ = l_Lake_GitRev_withRemote(v_remote_1074_, v_rev_1075_);
    lean_dec_ref(v_rev_1075_);
    return v_res_1076_;
}
pub unsafe fn l_Lake_GitRepo_instCoeFilePath___lam__0(
    mut v_x_1077_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_x_1077_);
    return v_x_1077_;
}
pub unsafe fn l_Lake_GitRepo_instCoeFilePath___lam__0___boxed(
    mut v_x_1078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1079_: *mut LeanObject = core::ptr::null_mut();
    v_res_1079_ = l_Lake_GitRepo_instCoeFilePath___lam__0(v_x_1078_);
    lean_dec_ref(v_x_1078_);
    return v_res_1079_;
}
pub unsafe fn l_Lake_GitRepo_dirExists(mut v_repo_1085_: *mut LeanObject) -> u8 {
    let mut v___x_1087_: u8 = 0;
    v___x_1087_ = l_System_FilePath_isDir(v_repo_1085_);
    return v___x_1087_;
}
pub unsafe fn l_Lake_GitRepo_dirExists___boxed(
    mut v_repo_1088_: *mut LeanObject,
    mut v_a_1089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1090_: u8 = 0;
    let mut v_r_1091_: *mut LeanObject = core::ptr::null_mut();
    v_res_1090_ = l_Lake_GitRepo_dirExists(v_repo_1088_);
    lean_dec_ref(v_repo_1088_);
    v_r_1091_ = lean_box((v_res_1090_) as usize);
    return v_r_1091_;
}
pub unsafe fn l_Lake_GitRepo_captureGit(
    mut v_args_1096_: *mut LeanObject,
    mut v_repo_1097_: *mut LeanObject,
    mut v_a_1098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: u8 = 0;
    let mut v___x_1106_: u8 = 0;
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1113_: u8 = 0;
    let mut v_stdout_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1125_: u8 = 0;
    let mut v_a_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1130_: u8 = 0;
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1134_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1100_ = l_Lake_GitRepo_captureGit___closed__0;
                v___x_1101_ = l_Lake_Git_filterUrl_x3f___closed__2;
                v___x_1102_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1102_, 0, v_repo_1097_);
                v___x_1103_ = lean_unsigned_to_nat(0);
                v___x_1104_ = l_Lake_GitRepo_captureGit___closed__1;
                v___x_1105_ = 1;
                v___x_1106_ = 0;
                v___x_1107_ = lean_alloc_ctor(0, 5, (2) as u32);
                lean_ctor_set(v___x_1107_, 0, v___x_1100_);
                lean_ctor_set(v___x_1107_, 1, v___x_1101_);
                lean_ctor_set(v___x_1107_, 2, v_args_1096_);
                lean_ctor_set(v___x_1107_, 3, v___x_1102_);
                lean_ctor_set(v___x_1107_, 4, v___x_1104_);
                lean_ctor_set_uint8(
                    v___x_1107_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___x_1105_,
                );
                lean_ctor_set_uint8(
                    v___x_1107_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___x_1106_,
                );
                v___x_1108_ = l_Lake_captureProc_x27(v___x_1107_, v_a_1098_);
                if lean_obj_tag(v___x_1108_) == 0 {
                    v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
                    v_a_1110_ = lean_ctor_get(v___x_1108_, 1);
                    v_isSharedCheck_1125_ = (!lean_is_exclusive(v___x_1108_)) as u8;
                    if v_isSharedCheck_1125_ == 0 {
                        v___x_1112_ = v___x_1108_;
                        v_isShared_1113_ = v_isSharedCheck_1125_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1110_);
                        lean_inc(v_a_1109_);
                        lean_dec(v___x_1108_);
                        v___x_1112_ = lean_box(0);
                        v_isShared_1113_ = v_isSharedCheck_1125_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1126_ = lean_ctor_get(v___x_1108_, 0);
                    v_a_1127_ = lean_ctor_get(v___x_1108_, 1);
                    v_isSharedCheck_1134_ = (!lean_is_exclusive(v___x_1108_)) as u8;
                    if v_isSharedCheck_1134_ == 0 {
                        v___x_1129_ = v___x_1108_;
                        v_isShared_1130_ = v_isSharedCheck_1134_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1127_);
                        lean_inc(v_a_1126_);
                        lean_dec(v___x_1108_);
                        v___x_1129_ = lean_box(0);
                        v_isShared_1130_ = v_isSharedCheck_1134_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_stdout_1114_ = lean_ctor_get(v_a_1109_, 0);
                lean_inc_ref(v_stdout_1114_);
                lean_dec(v_a_1109_);
                v___x_1115_ = lean_string_utf8_byte_size(v_stdout_1114_);
                v___x_1116_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1116_, 0, v_stdout_1114_);
                lean_ctor_set(v___x_1116_, 1, v___x_1103_);
                lean_ctor_set(v___x_1116_, 2, v___x_1115_);
                v___x_1117_ = l_String_Slice_trimAscii(v___x_1116_);
                v_str_1118_ = lean_ctor_get(v___x_1117_, 0);
                lean_inc_ref(v_str_1118_);
                v_startInclusive_1119_ = lean_ctor_get(v___x_1117_, 1);
                lean_inc(v_startInclusive_1119_);
                v_endExclusive_1120_ = lean_ctor_get(v___x_1117_, 2);
                lean_inc(v_endExclusive_1120_);
                lean_dec_ref(v___x_1117_);
                v___x_1121_ = lean_string_utf8_extract(
                    v_str_1118_,
                    v_startInclusive_1119_,
                    v_endExclusive_1120_,
                );
                lean_dec(v_endExclusive_1120_);
                lean_dec(v_startInclusive_1119_);
                lean_dec_ref(v_str_1118_);
                if v_isShared_1113_ == 0 {
                    lean_ctor_set(v___x_1112_, 0, v___x_1121_);
                    v___x_1123_ = v___x_1112_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
                    lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_a_1110_);
                    v___x_1123_ = v_reuseFailAlloc_1124_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1123_;
            }
            3 => {
                if v_isShared_1130_ == 0 {
                    v___x_1132_ = v___x_1129_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1126_);
                    lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_a_1127_);
                    v___x_1132_ = v_reuseFailAlloc_1133_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1132_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_GitRepo_captureGit___boxed(
    mut v_args_1135_: *mut LeanObject,
    mut v_repo_1136_: *mut LeanObject,
    mut v_a_1137_: *mut LeanObject,
    mut v_a_1138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1139_: *mut LeanObject = core::ptr::null_mut();
    v_res_1139_ = l_Lake_GitRepo_captureGit(v_args_1135_, v_repo_1136_, v_a_1137_);
    return v_res_1139_;
}
pub unsafe fn l_Lake_GitRepo_captureGit_x3f(
    mut v_args_1140_: *mut LeanObject,
    mut v_repo_1141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: u8 = 0;
    let mut v___x_1148_: u8 = 0;
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    v___x_1143_ = l_Lake_GitRepo_captureGit___closed__0;
    v___x_1144_ = l_Lake_Git_filterUrl_x3f___closed__2;
    v___x_1145_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1145_, 0, v_repo_1141_);
    v___x_1146_ = l_Lake_GitRepo_captureGit___closed__1;
    v___x_1147_ = 1;
    v___x_1148_ = 0;
    v___x_1149_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_1149_, 0, v___x_1143_);
    lean_ctor_set(v___x_1149_, 1, v___x_1144_);
    lean_ctor_set(v___x_1149_, 2, v_args_1140_);
    lean_ctor_set(v___x_1149_, 3, v___x_1145_);
    lean_ctor_set(v___x_1149_, 4, v___x_1146_);
    lean_ctor_set_uint8(
        v___x_1149_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_1147_,
    );
    lean_ctor_set_uint8(
        v___x_1149_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_1148_,
    );
    v___x_1150_ = l_Lake_captureProc_x3f(v___x_1149_);
    return v___x_1150_;
}
pub unsafe fn l_Lake_GitRepo_captureGit_x3f___boxed(
    mut v_args_1151_: *mut LeanObject,
    mut v_repo_1152_: *mut LeanObject,
    mut v_a_1153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1154_: *mut LeanObject = core::ptr::null_mut();
    v_res_1154_ = l_Lake_GitRepo_captureGit_x3f(v_args_1151_, v_repo_1152_);
    return v_res_1154_;
}
pub unsafe fn l_Lake_GitRepo_execGit(
    mut v_args_1155_: *mut LeanObject,
    mut v_repo_1156_: *mut LeanObject,
    mut v_a_1157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: u8 = 0;
    let mut v___x_1164_: u8 = 0;
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    v___x_1159_ = l_Lake_GitRepo_captureGit___closed__0;
    v___x_1160_ = l_Lake_Git_filterUrl_x3f___closed__2;
    v___x_1161_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1161_, 0, v_repo_1156_);
    v___x_1162_ = l_Lake_GitRepo_captureGit___closed__1;
    v___x_1163_ = 1;
    v___x_1164_ = 0;
    v___x_1165_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_1165_, 0, v___x_1159_);
    lean_ctor_set(v___x_1165_, 1, v___x_1160_);
    lean_ctor_set(v___x_1165_, 2, v_args_1155_);
    lean_ctor_set(v___x_1165_, 3, v___x_1161_);
    lean_ctor_set(v___x_1165_, 4, v___x_1162_);
    lean_ctor_set_uint8(
        v___x_1165_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_1163_,
    );
    lean_ctor_set_uint8(
        v___x_1165_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_1164_,
    );
    v___x_1166_ = l_Lake_proc(v___x_1165_, v___x_1163_, v_a_1157_);
    return v___x_1166_;
}
pub unsafe fn l_Lake_GitRepo_execGit___boxed(
    mut v_args_1167_: *mut LeanObject,
    mut v_repo_1168_: *mut LeanObject,
    mut v_a_1169_: *mut LeanObject,
    mut v_a_1170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1171_: *mut LeanObject = core::ptr::null_mut();
    v_res_1171_ = l_Lake_GitRepo_execGit(v_args_1167_, v_repo_1168_, v_a_1169_);
    return v_res_1171_;
}
pub unsafe fn l_Lake_GitRepo_testGit(
    mut v_args_1172_: *mut LeanObject,
    mut v_repo_1173_: *mut LeanObject,
) -> u8 {
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: u8 = 0;
    let mut v___x_1180_: u8 = 0;
    let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: u8 = 0;
    v___x_1175_ = l_Lake_GitRepo_captureGit___closed__0;
    v___x_1176_ = l_Lake_Git_filterUrl_x3f___closed__2;
    v___x_1177_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1177_, 0, v_repo_1173_);
    v___x_1178_ = l_Lake_GitRepo_captureGit___closed__1;
    v___x_1179_ = 1;
    v___x_1180_ = 0;
    v___x_1181_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_1181_, 0, v___x_1175_);
    lean_ctor_set(v___x_1181_, 1, v___x_1176_);
    lean_ctor_set(v___x_1181_, 2, v_args_1172_);
    lean_ctor_set(v___x_1181_, 3, v___x_1177_);
    lean_ctor_set(v___x_1181_, 4, v___x_1178_);
    lean_ctor_set_uint8(
        v___x_1181_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_1179_,
    );
    lean_ctor_set_uint8(
        v___x_1181_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_1180_,
    );
    v___x_1182_ = l_Lake_testProc(v___x_1181_);
    return v___x_1182_;
}
pub unsafe fn l_Lake_GitRepo_testGit___boxed(
    mut v_args_1183_: *mut LeanObject,
    mut v_repo_1184_: *mut LeanObject,
    mut v_a_1185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1186_: u8 = 0;
    let mut v_r_1187_: *mut LeanObject = core::ptr::null_mut();
    v_res_1186_ = l_Lake_GitRepo_testGit(v_args_1183_, v_repo_1184_);
    v_r_1187_ = lean_box((v_res_1186_) as usize);
    return v_r_1187_;
}
pub unsafe fn _init_l_Lake_GitRepo_clone___closed__1() -> *mut LeanObject {
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    v___x_1189_ = l_Lake_GitRepo_clone___closed__0;
    v___x_1190_ = lean_unsigned_to_nat(3);
    v___x_1191_ = lean_mk_empty_array_with_capacity(v___x_1190_);
    v___x_1192_ = lean_array_push(v___x_1191_, v___x_1189_);
    return v___x_1192_;
}
pub unsafe fn l_Lake_GitRepo_clone(
    mut v_url_1193_: *mut LeanObject,
    mut v_repo_1194_: *mut LeanObject,
    mut v_a_1195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: u8 = 0;
    let mut v___x_1205_: u8 = 0;
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    v___x_1197_ = l_Lake_GitRepo_captureGit___closed__0;
    v___x_1198_ = l_Lake_Git_filterUrl_x3f___closed__2;
    v___x_1199_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_clone___closed__1),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_clone___closed__1_once),
        _init_l_Lake_GitRepo_clone___closed__1,
    );
    v___x_1200_ = lean_array_push(v___x_1199_, v_url_1193_);
    v___x_1201_ = lean_array_push(v___x_1200_, v_repo_1194_);
    v___x_1202_ = lean_box(0);
    v___x_1203_ = l_Lake_GitRepo_captureGit___closed__1;
    v___x_1204_ = 1;
    v___x_1205_ = 0;
    v___x_1206_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_1206_, 0, v___x_1197_);
    lean_ctor_set(v___x_1206_, 1, v___x_1198_);
    lean_ctor_set(v___x_1206_, 2, v___x_1201_);
    lean_ctor_set(v___x_1206_, 3, v___x_1202_);
    lean_ctor_set(v___x_1206_, 4, v___x_1203_);
    lean_ctor_set_uint8(
        v___x_1206_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_1204_,
    );
    lean_ctor_set_uint8(
        v___x_1206_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_1205_,
    );
    v___x_1207_ = l_Lake_proc(v___x_1206_, v___x_1204_, v_a_1195_);
    return v___x_1207_;
}
pub unsafe fn l_Lake_GitRepo_clone___boxed(
    mut v_url_1208_: *mut LeanObject,
    mut v_repo_1209_: *mut LeanObject,
    mut v_a_1210_: *mut LeanObject,
    mut v_a_1211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1212_: *mut LeanObject = core::ptr::null_mut();
    v_res_1212_ = l_Lake_GitRepo_clone(v_url_1208_, v_repo_1209_, v_a_1210_);
    return v_res_1212_;
}
pub unsafe fn l_Lake_GitRepo_quietInit(
    mut v_repo_1221_: *mut LeanObject,
    mut v_a_1222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: u8 = 0;
    let mut v___x_1230_: u8 = 0;
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    v___x_1224_ = l_Lake_GitRepo_quietInit___closed__2;
    v___x_1225_ = l_Lake_GitRepo_captureGit___closed__0;
    v___x_1226_ = l_Lake_Git_filterUrl_x3f___closed__2;
    v___x_1227_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1227_, 0, v_repo_1221_);
    v___x_1228_ = l_Lake_GitRepo_captureGit___closed__1;
    v___x_1229_ = 1;
    v___x_1230_ = 0;
    v___x_1231_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_1231_, 0, v___x_1225_);
    lean_ctor_set(v___x_1231_, 1, v___x_1226_);
    lean_ctor_set(v___x_1231_, 2, v___x_1224_);
    lean_ctor_set(v___x_1231_, 3, v___x_1227_);
    lean_ctor_set(v___x_1231_, 4, v___x_1228_);
    lean_ctor_set_uint8(
        v___x_1231_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_1229_,
    );
    lean_ctor_set_uint8(
        v___x_1231_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_1230_,
    );
    v___x_1232_ = l_Lake_proc(v___x_1231_, v___x_1229_, v_a_1222_);
    return v___x_1232_;
}
pub unsafe fn l_Lake_GitRepo_quietInit___boxed(
    mut v_repo_1233_: *mut LeanObject,
    mut v_a_1234_: *mut LeanObject,
    mut v_a_1235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1236_: *mut LeanObject = core::ptr::null_mut();
    v_res_1236_ = l_Lake_GitRepo_quietInit(v_repo_1233_, v_a_1234_);
    return v_res_1236_;
}
pub unsafe fn l_Lake_GitRepo_bareInit(
    mut v_repo_1246_: *mut LeanObject,
    mut v_a_1247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: u8 = 0;
    let mut v___x_1255_: u8 = 0;
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    v___x_1249_ = l_Lake_GitRepo_bareInit___closed__1;
    v___x_1250_ = l_Lake_GitRepo_captureGit___closed__0;
    v___x_1251_ = l_Lake_Git_filterUrl_x3f___closed__2;
    v___x_1252_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1252_, 0, v_repo_1246_);
    v___x_1253_ = l_Lake_GitRepo_captureGit___closed__1;
    v___x_1254_ = 1;
    v___x_1255_ = 0;
    v___x_1256_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_1256_, 0, v___x_1250_);
    lean_ctor_set(v___x_1256_, 1, v___x_1251_);
    lean_ctor_set(v___x_1256_, 2, v___x_1249_);
    lean_ctor_set(v___x_1256_, 3, v___x_1252_);
    lean_ctor_set(v___x_1256_, 4, v___x_1253_);
    lean_ctor_set_uint8(
        v___x_1256_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_1254_,
    );
    lean_ctor_set_uint8(
        v___x_1256_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_1255_,
    );
    v___x_1257_ = l_Lake_proc(v___x_1256_, v___x_1254_, v_a_1247_);
    return v___x_1257_;
}
pub unsafe fn l_Lake_GitRepo_bareInit___boxed(
    mut v_repo_1258_: *mut LeanObject,
    mut v_a_1259_: *mut LeanObject,
    mut v_a_1260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1261_: *mut LeanObject = core::ptr::null_mut();
    v_res_1261_ = l_Lake_GitRepo_bareInit(v_repo_1258_, v_a_1259_);
    return v_res_1261_;
}
pub unsafe fn l_Lake_GitRepo_insideWorkTree(mut v_repo_1270_: *mut LeanObject) -> u8 {
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: u8 = 0;
    let mut v___x_1278_: u8 = 0;
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: u8 = 0;
    v___x_1272_ = l_Lake_GitRepo_insideWorkTree___closed__2;
    v___x_1273_ = l_Lake_GitRepo_captureGit___closed__0;
    v___x_1274_ = l_Lake_Git_filterUrl_x3f___closed__2;
    v___x_1275_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1275_, 0, v_repo_1270_);
    v___x_1276_ = l_Lake_GitRepo_captureGit___closed__1;
    v___x_1277_ = 1;
    v___x_1278_ = 0;
    v___x_1279_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_1279_, 0, v___x_1273_);
    lean_ctor_set(v___x_1279_, 1, v___x_1274_);
    lean_ctor_set(v___x_1279_, 2, v___x_1272_);
    lean_ctor_set(v___x_1279_, 3, v___x_1275_);
    lean_ctor_set(v___x_1279_, 4, v___x_1276_);
    lean_ctor_set_uint8(
        v___x_1279_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_1277_,
    );
    lean_ctor_set_uint8(
        v___x_1279_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_1278_,
    );
    v___x_1280_ = l_Lake_testProc(v___x_1279_);
    return v___x_1280_;
}
pub unsafe fn l_Lake_GitRepo_insideWorkTree___boxed(
    mut v_repo_1281_: *mut LeanObject,
    mut v_a_1282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1283_: u8 = 0;
    let mut v_r_1284_: *mut LeanObject = core::ptr::null_mut();
    v_res_1283_ = l_Lake_GitRepo_insideWorkTree(v_repo_1281_);
    v_r_1284_ = lean_box((v_res_1283_) as usize);
    return v_r_1284_;
}
pub unsafe fn _init_l_Lake_GitRepo_fetch___closed__3() -> *mut LeanObject {
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    v___x_1288_ = l_Lake_GitRepo_fetch___closed__0;
    v___x_1289_ = lean_unsigned_to_nat(4);
    v___x_1290_ = lean_mk_empty_array_with_capacity(v___x_1289_);
    v___x_1291_ = lean_array_push(v___x_1290_, v___x_1288_);
    return v___x_1291_;
}
pub unsafe fn _init_l_Lake_GitRepo_fetch___closed__4() -> *mut LeanObject {
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    v___x_1292_ = l_Lake_GitRepo_fetch___closed__1;
    v___x_1293_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_fetch___closed__3),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_fetch___closed__3_once),
        _init_l_Lake_GitRepo_fetch___closed__3,
    );
    v___x_1294_ = lean_array_push(v___x_1293_, v___x_1292_);
    return v___x_1294_;
}
pub unsafe fn _init_l_Lake_GitRepo_fetch___closed__5() -> *mut LeanObject {
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    v___x_1295_ = l_Lake_GitRepo_fetch___closed__2;
    v___x_1296_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_fetch___closed__4),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_fetch___closed__4_once),
        _init_l_Lake_GitRepo_fetch___closed__4,
    );
    v___x_1297_ = lean_array_push(v___x_1296_, v___x_1295_);
    return v___x_1297_;
}
pub unsafe fn l_Lake_GitRepo_fetch(
    mut v_repo_1298_: *mut LeanObject,
    mut v_remote_1299_: *mut LeanObject,
    mut v_a_1300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: u8 = 0;
    let mut v___x_1309_: u8 = 0;
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    v___x_1302_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_fetch___closed__5),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_fetch___closed__5_once),
        _init_l_Lake_GitRepo_fetch___closed__5,
    );
    v___x_1303_ = lean_array_push(v___x_1302_, v_remote_1299_);
    v___x_1304_ = l_Lake_GitRepo_captureGit___closed__0;
    v___x_1305_ = l_Lake_Git_filterUrl_x3f___closed__2;
    v___x_1306_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1306_, 0, v_repo_1298_);
    v___x_1307_ = l_Lake_GitRepo_captureGit___closed__1;
    v___x_1308_ = 1;
    v___x_1309_ = 0;
    v___x_1310_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_1310_, 0, v___x_1304_);
    lean_ctor_set(v___x_1310_, 1, v___x_1305_);
    lean_ctor_set(v___x_1310_, 2, v___x_1303_);
    lean_ctor_set(v___x_1310_, 3, v___x_1306_);
    lean_ctor_set(v___x_1310_, 4, v___x_1307_);
    lean_ctor_set_uint8(
        v___x_1310_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_1308_,
    );
    lean_ctor_set_uint8(
        v___x_1310_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_1309_,
    );
    v___x_1311_ = l_Lake_proc(v___x_1310_, v___x_1308_, v_a_1300_);
    return v___x_1311_;
}
pub unsafe fn l_Lake_GitRepo_fetch___boxed(
    mut v_repo_1312_: *mut LeanObject,
    mut v_remote_1313_: *mut LeanObject,
    mut v_a_1314_: *mut LeanObject,
    mut v_a_1315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1316_: *mut LeanObject = core::ptr::null_mut();
    v_res_1316_ = l_Lake_GitRepo_fetch(v_repo_1312_, v_remote_1313_, v_a_1314_);
    return v_res_1316_;
}
pub unsafe fn _init_l_Lake_GitRepo_addWorktreeDetach___closed__3() -> *mut LeanObject {
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    v___x_1320_ = l_Lake_GitRepo_addWorktreeDetach___closed__0;
    v___x_1321_ = lean_unsigned_to_nat(5);
    v___x_1322_ = lean_mk_empty_array_with_capacity(v___x_1321_);
    v___x_1323_ = lean_array_push(v___x_1322_, v___x_1320_);
    return v___x_1323_;
}
pub unsafe fn _init_l_Lake_GitRepo_addWorktreeDetach___closed__4() -> *mut LeanObject {
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    v___x_1324_ = l_Lake_GitRepo_addWorktreeDetach___closed__1;
    v___x_1325_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_addWorktreeDetach___closed__3),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_addWorktreeDetach___closed__3_once),
        _init_l_Lake_GitRepo_addWorktreeDetach___closed__3,
    );
    v___x_1326_ = lean_array_push(v___x_1325_, v___x_1324_);
    return v___x_1326_;
}
pub unsafe fn _init_l_Lake_GitRepo_addWorktreeDetach___closed__5() -> *mut LeanObject {
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    v___x_1327_ = l_Lake_GitRepo_addWorktreeDetach___closed__2;
    v___x_1328_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_addWorktreeDetach___closed__4),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_addWorktreeDetach___closed__4_once),
        _init_l_Lake_GitRepo_addWorktreeDetach___closed__4,
    );
    v___x_1329_ = lean_array_push(v___x_1328_, v___x_1327_);
    return v___x_1329_;
}
pub unsafe fn l_Lake_GitRepo_addWorktreeDetach(
    mut v_path_1330_: *mut LeanObject,
    mut v_rev_1331_: *mut LeanObject,
    mut v_repo_1332_: *mut LeanObject,
    mut v_a_1333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: u8 = 0;
    let mut v___x_1343_: u8 = 0;
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    v___x_1335_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_addWorktreeDetach___closed__5),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_addWorktreeDetach___closed__5_once),
        _init_l_Lake_GitRepo_addWorktreeDetach___closed__5,
    );
    v___x_1336_ = lean_array_push(v___x_1335_, v_path_1330_);
    v___x_1337_ = lean_array_push(v___x_1336_, v_rev_1331_);
    v___x_1338_ = l_Lake_GitRepo_captureGit___closed__0;
    v___x_1339_ = l_Lake_Git_filterUrl_x3f___closed__2;
    v___x_1340_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1340_, 0, v_repo_1332_);
    v___x_1341_ = l_Lake_GitRepo_captureGit___closed__1;
    v___x_1342_ = 1;
    v___x_1343_ = 0;
    v___x_1344_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_1344_, 0, v___x_1338_);
    lean_ctor_set(v___x_1344_, 1, v___x_1339_);
    lean_ctor_set(v___x_1344_, 2, v___x_1337_);
    lean_ctor_set(v___x_1344_, 3, v___x_1340_);
    lean_ctor_set(v___x_1344_, 4, v___x_1341_);
    lean_ctor_set_uint8(
        v___x_1344_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_1342_,
    );
    lean_ctor_set_uint8(
        v___x_1344_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_1343_,
    );
    v___x_1345_ = l_Lake_proc(v___x_1344_, v___x_1342_, v_a_1333_);
    return v___x_1345_;
}
pub unsafe fn l_Lake_GitRepo_addWorktreeDetach___boxed(
    mut v_path_1346_: *mut LeanObject,
    mut v_rev_1347_: *mut LeanObject,
    mut v_repo_1348_: *mut LeanObject,
    mut v_a_1349_: *mut LeanObject,
    mut v_a_1350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1351_: *mut LeanObject = core::ptr::null_mut();
    v_res_1351_ =
        l_Lake_GitRepo_addWorktreeDetach(v_path_1346_, v_rev_1347_, v_repo_1348_, v_a_1349_);
    return v_res_1351_;
}
pub unsafe fn _init_l_Lake_GitRepo_checkoutBranch___closed__2() -> *mut LeanObject {
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    v___x_1354_ = l_Lake_GitRepo_checkoutBranch___closed__0;
    v___x_1355_ = lean_unsigned_to_nat(3);
    v___x_1356_ = lean_mk_empty_array_with_capacity(v___x_1355_);
    v___x_1357_ = lean_array_push(v___x_1356_, v___x_1354_);
    return v___x_1357_;
}
pub unsafe fn _init_l_Lake_GitRepo_checkoutBranch___closed__3() -> *mut LeanObject {
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    v___x_1358_ = l_Lake_GitRepo_checkoutBranch___closed__1;
    v___x_1359_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_checkoutBranch___closed__2),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_checkoutBranch___closed__2_once),
        _init_l_Lake_GitRepo_checkoutBranch___closed__2,
    );
    v___x_1360_ = lean_array_push(v___x_1359_, v___x_1358_);
    return v___x_1360_;
}
pub unsafe fn l_Lake_GitRepo_checkoutBranch(
    mut v_branch_1361_: *mut LeanObject,
    mut v_repo_1362_: *mut LeanObject,
    mut v_a_1363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: u8 = 0;
    let mut v___x_1372_: u8 = 0;
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    v___x_1365_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_checkoutBranch___closed__3),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_checkoutBranch___closed__3_once),
        _init_l_Lake_GitRepo_checkoutBranch___closed__3,
    );
    v___x_1366_ = lean_array_push(v___x_1365_, v_branch_1361_);
    v___x_1367_ = l_Lake_GitRepo_captureGit___closed__0;
    v___x_1368_ = l_Lake_Git_filterUrl_x3f___closed__2;
    v___x_1369_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1369_, 0, v_repo_1362_);
    v___x_1370_ = l_Lake_GitRepo_captureGit___closed__1;
    v___x_1371_ = 1;
    v___x_1372_ = 0;
    v___x_1373_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_1373_, 0, v___x_1367_);
    lean_ctor_set(v___x_1373_, 1, v___x_1368_);
    lean_ctor_set(v___x_1373_, 2, v___x_1366_);
    lean_ctor_set(v___x_1373_, 3, v___x_1369_);
    lean_ctor_set(v___x_1373_, 4, v___x_1370_);
    lean_ctor_set_uint8(
        v___x_1373_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_1371_,
    );
    lean_ctor_set_uint8(
        v___x_1373_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_1372_,
    );
    v___x_1374_ = l_Lake_proc(v___x_1373_, v___x_1371_, v_a_1363_);
    return v___x_1374_;
}
pub unsafe fn l_Lake_GitRepo_checkoutBranch___boxed(
    mut v_branch_1375_: *mut LeanObject,
    mut v_repo_1376_: *mut LeanObject,
    mut v_a_1377_: *mut LeanObject,
    mut v_a_1378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1379_: *mut LeanObject = core::ptr::null_mut();
    v_res_1379_ = l_Lake_GitRepo_checkoutBranch(v_branch_1375_, v_repo_1376_, v_a_1377_);
    return v_res_1379_;
}
pub unsafe fn _init_l_Lake_GitRepo_checkoutDetach___closed__1() -> *mut LeanObject {
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    v___x_1381_ = l_Lake_GitRepo_checkoutBranch___closed__0;
    v___x_1382_ = lean_unsigned_to_nat(4);
    v___x_1383_ = lean_mk_empty_array_with_capacity(v___x_1382_);
    v___x_1384_ = lean_array_push(v___x_1383_, v___x_1381_);
    return v___x_1384_;
}
pub unsafe fn _init_l_Lake_GitRepo_checkoutDetach___closed__2() -> *mut LeanObject {
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    v___x_1385_ = l_Lake_GitRepo_addWorktreeDetach___closed__2;
    v___x_1386_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_checkoutDetach___closed__1),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_checkoutDetach___closed__1_once),
        _init_l_Lake_GitRepo_checkoutDetach___closed__1,
    );
    v___x_1387_ = lean_array_push(v___x_1386_, v___x_1385_);
    return v___x_1387_;
}
pub unsafe fn l_Lake_GitRepo_checkoutDetach(
    mut v_hash_1388_: *mut LeanObject,
    mut v_repo_1389_: *mut LeanObject,
    mut v_a_1390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: u8 = 0;
    let mut v___x_1401_: u8 = 0;
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    v___x_1392_ = l_Lake_GitRepo_checkoutDetach___closed__0;
    v___x_1393_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_checkoutDetach___closed__2),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_checkoutDetach___closed__2_once),
        _init_l_Lake_GitRepo_checkoutDetach___closed__2,
    );
    v___x_1394_ = lean_array_push(v___x_1393_, v_hash_1388_);
    v___x_1395_ = lean_array_push(v___x_1394_, v___x_1392_);
    v___x_1396_ = l_Lake_GitRepo_captureGit___closed__0;
    v___x_1397_ = l_Lake_Git_filterUrl_x3f___closed__2;
    v___x_1398_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1398_, 0, v_repo_1389_);
    v___x_1399_ = l_Lake_GitRepo_captureGit___closed__1;
    v___x_1400_ = 1;
    v___x_1401_ = 0;
    v___x_1402_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_1402_, 0, v___x_1396_);
    lean_ctor_set(v___x_1402_, 1, v___x_1397_);
    lean_ctor_set(v___x_1402_, 2, v___x_1395_);
    lean_ctor_set(v___x_1402_, 3, v___x_1398_);
    lean_ctor_set(v___x_1402_, 4, v___x_1399_);
    lean_ctor_set_uint8(
        v___x_1402_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_1400_,
    );
    lean_ctor_set_uint8(
        v___x_1402_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_1401_,
    );
    v___x_1403_ = l_Lake_proc(v___x_1402_, v___x_1400_, v_a_1390_);
    return v___x_1403_;
}
pub unsafe fn l_Lake_GitRepo_checkoutDetach___boxed(
    mut v_hash_1404_: *mut LeanObject,
    mut v_repo_1405_: *mut LeanObject,
    mut v_a_1406_: *mut LeanObject,
    mut v_a_1407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1408_: *mut LeanObject = core::ptr::null_mut();
    v_res_1408_ = l_Lake_GitRepo_checkoutDetach(v_hash_1404_, v_repo_1405_, v_a_1406_);
    return v_res_1408_;
}
pub unsafe fn l_Lake_GitRepo_clean(
    mut v_repo_1417_: *mut LeanObject,
    mut v_a_1418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: u8 = 0;
    let mut v___x_1426_: u8 = 0;
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    v___x_1420_ = l_Lake_GitRepo_clean___closed__2;
    v___x_1421_ = l_Lake_GitRepo_captureGit___closed__0;
    v___x_1422_ = l_Lake_Git_filterUrl_x3f___closed__2;
    v___x_1423_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1423_, 0, v_repo_1417_);
    v___x_1424_ = l_Lake_GitRepo_captureGit___closed__1;
    v___x_1425_ = 1;
    v___x_1426_ = 0;
    v___x_1427_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_1427_, 0, v___x_1421_);
    lean_ctor_set(v___x_1427_, 1, v___x_1422_);
    lean_ctor_set(v___x_1427_, 2, v___x_1420_);
    lean_ctor_set(v___x_1427_, 3, v___x_1423_);
    lean_ctor_set(v___x_1427_, 4, v___x_1424_);
    lean_ctor_set_uint8(
        v___x_1427_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_1425_,
    );
    lean_ctor_set_uint8(
        v___x_1427_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_1426_,
    );
    v___x_1428_ = l_Lake_proc(v___x_1427_, v___x_1425_, v_a_1418_);
    return v___x_1428_;
}
pub unsafe fn l_Lake_GitRepo_clean___boxed(
    mut v_repo_1429_: *mut LeanObject,
    mut v_a_1430_: *mut LeanObject,
    mut v_a_1431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1432_: *mut LeanObject = core::ptr::null_mut();
    v_res_1432_ = l_Lake_GitRepo_clean(v_repo_1429_, v_a_1430_);
    return v_res_1432_;
}
pub unsafe fn _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2() -> *mut LeanObject {
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    v___x_1435_ = l_Lake_GitRepo_insideWorkTree___closed__0;
    v___x_1436_ = lean_unsigned_to_nat(4);
    v___x_1437_ = lean_mk_empty_array_with_capacity(v___x_1436_);
    v___x_1438_ = lean_array_push(v___x_1437_, v___x_1435_);
    return v___x_1438_;
}
pub unsafe fn _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3() -> *mut LeanObject {
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    v___x_1439_ = l_Lake_GitRepo_resolveRevision_x3f___closed__0;
    v___x_1440_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_resolveRevision_x3f___closed__2),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_resolveRevision_x3f___closed__2_once),
        _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2,
    );
    v___x_1441_ = lean_array_push(v___x_1440_, v___x_1439_);
    return v___x_1441_;
}
pub unsafe fn _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4() -> *mut LeanObject {
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    v___x_1442_ = l_Lake_GitRepo_resolveRevision_x3f___closed__1;
    v___x_1443_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_resolveRevision_x3f___closed__3),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_resolveRevision_x3f___closed__3_once),
        _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3,
    );
    v___x_1444_ = lean_array_push(v___x_1443_, v___x_1442_);
    return v___x_1444_;
}
pub unsafe fn l_Lake_GitRepo_resolveRevision_x3f(
    mut v_rev_1445_: *mut LeanObject,
    mut v_repo_1446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: u8 = 0;
    let mut v___x_1455_: u8 = 0;
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    v___x_1448_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_resolveRevision_x3f___closed__4),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_resolveRevision_x3f___closed__4_once),
        _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4,
    );
    v___x_1449_ = lean_array_push(v___x_1448_, v_rev_1445_);
    v___x_1450_ = l_Lake_GitRepo_captureGit___closed__0;
    v___x_1451_ = l_Lake_Git_filterUrl_x3f___closed__2;
    v___x_1452_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1452_, 0, v_repo_1446_);
    v___x_1453_ = l_Lake_GitRepo_captureGit___closed__1;
    v___x_1454_ = 1;
    v___x_1455_ = 0;
    v___x_1456_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_1456_, 0, v___x_1450_);
    lean_ctor_set(v___x_1456_, 1, v___x_1451_);
    lean_ctor_set(v___x_1456_, 2, v___x_1449_);
    lean_ctor_set(v___x_1456_, 3, v___x_1452_);
    lean_ctor_set(v___x_1456_, 4, v___x_1453_);
    lean_ctor_set_uint8(
        v___x_1456_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_1454_,
    );
    lean_ctor_set_uint8(
        v___x_1456_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_1455_,
    );
    v___x_1457_ = l_Lake_captureProc_x3f(v___x_1456_);
    return v___x_1457_;
}
pub unsafe fn l_Lake_GitRepo_resolveRevision_x3f___boxed(
    mut v_rev_1458_: *mut LeanObject,
    mut v_repo_1459_: *mut LeanObject,
    mut v_a_1460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1461_: *mut LeanObject = core::ptr::null_mut();
    v_res_1461_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_1458_, v_repo_1459_);
    return v_res_1461_;
}
pub unsafe fn l_Lake_GitRepo_findCommit_x3f(
    mut v_rev_1463_: *mut LeanObject,
    mut v_repo_1464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: u8 = 0;
    let mut v___x_1475_: u8 = 0;
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    v___x_1466_ = l_Lake_GitRepo_findCommit_x3f___closed__0;
    v___x_1467_ = lean_string_append(v_rev_1463_, v___x_1466_);
    v___x_1468_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_resolveRevision_x3f___closed__4),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_resolveRevision_x3f___closed__4_once),
        _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4,
    );
    v___x_1469_ = lean_array_push(v___x_1468_, v___x_1467_);
    v___x_1470_ = l_Lake_GitRepo_captureGit___closed__0;
    v___x_1471_ = l_Lake_Git_filterUrl_x3f___closed__2;
    v___x_1472_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1472_, 0, v_repo_1464_);
    v___x_1473_ = l_Lake_GitRepo_captureGit___closed__1;
    v___x_1474_ = 1;
    v___x_1475_ = 0;
    v___x_1476_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_1476_, 0, v___x_1470_);
    lean_ctor_set(v___x_1476_, 1, v___x_1471_);
    lean_ctor_set(v___x_1476_, 2, v___x_1469_);
    lean_ctor_set(v___x_1476_, 3, v___x_1472_);
    lean_ctor_set(v___x_1476_, 4, v___x_1473_);
    lean_ctor_set_uint8(
        v___x_1476_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_1474_,
    );
    lean_ctor_set_uint8(
        v___x_1476_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_1475_,
    );
    v___x_1477_ = l_Lake_captureProc_x3f(v___x_1476_);
    return v___x_1477_;
}
pub unsafe fn l_Lake_GitRepo_findCommit_x3f___boxed(
    mut v_rev_1478_: *mut LeanObject,
    mut v_repo_1479_: *mut LeanObject,
    mut v_a_1480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1481_: *mut LeanObject = core::ptr::null_mut();
    v_res_1481_ = l_Lake_GitRepo_findCommit_x3f(v_rev_1478_, v_repo_1479_);
    return v_res_1481_;
}
pub unsafe fn l_Lake_GitRepo_resolveRevision(
    mut v_rev_1484_: *mut LeanObject,
    mut v_repo_1485_: *mut LeanObject,
    mut v_a_1486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1488_: u8 = 0;
    v___x_1488_ = l_Lake_GitRev_isFullSha1(v_rev_1484_);
    if v___x_1488_ == 0 {
        let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_repo_1485_);
        lean_inc_ref(v_rev_1484_);
        v___x_1489_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_1484_, v_repo_1485_);
        if lean_obj_tag(v___x_1489_) == 1 {
            let mut v_val_1490_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_repo_1485_);
            lean_dec_ref(v_rev_1484_);
            v_val_1490_ = lean_ctor_get(v___x_1489_, 0);
            lean_inc(v_val_1490_);
            lean_dec_ref_known(v___x_1489_, 1);
            v___x_1491_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_1491_, 0, v_val_1490_);
            lean_ctor_set(v___x_1491_, 1, v_a_1486_);
            return v___x_1491_;
        } else {
            let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1497_: u8 = 0;
            let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_1489_);
            v___x_1492_ = l_Lake_GitRepo_resolveRevision___closed__0;
            v___x_1493_ = lean_string_append(v_repo_1485_, v___x_1492_);
            v___x_1494_ = lean_string_append(v___x_1493_, v_rev_1484_);
            lean_dec_ref(v_rev_1484_);
            v___x_1495_ = l_Lake_GitRepo_resolveRevision___closed__1;
            v___x_1496_ = lean_string_append(v___x_1494_, v___x_1495_);
            v___x_1497_ = 3;
            v___x_1498_ = lean_alloc_ctor(0, 1, (1) as u32);
            lean_ctor_set(v___x_1498_, 0, v___x_1496_);
            lean_ctor_set_uint8(
                v___x_1498_,
                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                v___x_1497_,
            );
            v___x_1499_ = lean_array_get_size(v_a_1486_);
            v___x_1500_ = lean_array_push(v_a_1486_, v___x_1498_);
            v___x_1501_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_1501_, 0, v___x_1499_);
            lean_ctor_set(v___x_1501_, 1, v___x_1500_);
            return v___x_1501_;
        }
    } else {
        let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_repo_1485_);
        v___x_1502_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1502_, 0, v_rev_1484_);
        lean_ctor_set(v___x_1502_, 1, v_a_1486_);
        return v___x_1502_;
    }
}
pub unsafe fn l_Lake_GitRepo_resolveRevision___boxed(
    mut v_rev_1503_: *mut LeanObject,
    mut v_repo_1504_: *mut LeanObject,
    mut v_a_1505_: *mut LeanObject,
    mut v_a_1506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1507_: *mut LeanObject = core::ptr::null_mut();
    v_res_1507_ = l_Lake_GitRepo_resolveRevision(v_rev_1503_, v_repo_1504_, v_a_1505_);
    return v_res_1507_;
}
pub unsafe fn l_Lake_GitRepo_getHeadRevision_x3f(
    mut v_repo_1508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    v___x_1510_ = l_Lake_GitRev_head___closed__0;
    v___x_1511_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1510_, v_repo_1508_);
    return v___x_1511_;
}
pub unsafe fn l_Lake_GitRepo_getHeadRevision_x3f___boxed(
    mut v_repo_1512_: *mut LeanObject,
    mut v_a_1513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1514_: *mut LeanObject = core::ptr::null_mut();
    v_res_1514_ = l_Lake_GitRepo_getHeadRevision_x3f(v_repo_1512_);
    return v_res_1514_;
}
pub unsafe fn l_Lake_GitRepo_getHeadRevision(
    mut v_repo_1516_: *mut LeanObject,
    mut v_a_1517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    v___x_1519_ = l_Lake_GitRev_head___closed__0;
    lean_inc_ref(v_repo_1516_);
    v___x_1520_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1519_, v_repo_1516_);
    if lean_obj_tag(v___x_1520_) == 1 {
        let mut v_val_1521_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_repo_1516_);
        v_val_1521_ = lean_ctor_get(v___x_1520_, 0);
        lean_inc(v_val_1521_);
        lean_dec_ref_known(v___x_1520_, 1);
        v___x_1522_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1522_, 0, v_val_1521_);
        lean_ctor_set(v___x_1522_, 1, v_a_1517_);
        return v___x_1522_;
    } else {
        let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1525_: u8 = 0;
        let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_1520_);
        v___x_1523_ = l_Lake_GitRepo_getHeadRevision___closed__0;
        v___x_1524_ = lean_string_append(v_repo_1516_, v___x_1523_);
        v___x_1525_ = 3;
        v___x_1526_ = lean_alloc_ctor(0, 1, (1) as u32);
        lean_ctor_set(v___x_1526_, 0, v___x_1524_);
        lean_ctor_set_uint8(
            v___x_1526_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            v___x_1525_,
        );
        v___x_1527_ = lean_array_get_size(v_a_1517_);
        v___x_1528_ = lean_array_push(v_a_1517_, v___x_1526_);
        v___x_1529_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1529_, 0, v___x_1527_);
        lean_ctor_set(v___x_1529_, 1, v___x_1528_);
        return v___x_1529_;
    }
}
pub unsafe fn l_Lake_GitRepo_getHeadRevision___boxed(
    mut v_repo_1530_: *mut LeanObject,
    mut v_a_1531_: *mut LeanObject,
    mut v_a_1532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1533_: *mut LeanObject = core::ptr::null_mut();
    v_res_1533_ = l_Lake_GitRepo_getHeadRevision(v_repo_1530_, v_a_1531_);
    return v_res_1533_;
}
pub unsafe fn _init_l_Lake_GitRepo_fetchRevision_x3f___closed__2() -> *mut LeanObject {
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    v___x_1536_ = l_Lake_GitRepo_fetch___closed__0;
    v___x_1537_ = lean_unsigned_to_nat(7);
    v___x_1538_ = lean_mk_empty_array_with_capacity(v___x_1537_);
    v___x_1539_ = lean_array_push(v___x_1538_, v___x_1536_);
    return v___x_1539_;
}
pub unsafe fn _init_l_Lake_GitRepo_fetchRevision_x3f___closed__3() -> *mut LeanObject {
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    v___x_1540_ = l_Lake_GitRepo_fetch___closed__1;
    v___x_1541_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_fetchRevision_x3f___closed__2),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_fetchRevision_x3f___closed__2_once),
        _init_l_Lake_GitRepo_fetchRevision_x3f___closed__2,
    );
    v___x_1542_ = lean_array_push(v___x_1541_, v___x_1540_);
    return v___x_1542_;
}
pub unsafe fn _init_l_Lake_GitRepo_fetchRevision_x3f___closed__4() -> *mut LeanObject {
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    v___x_1543_ = l_Lake_GitRepo_fetch___closed__2;
    v___x_1544_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_fetchRevision_x3f___closed__3),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_fetchRevision_x3f___closed__3_once),
        _init_l_Lake_GitRepo_fetchRevision_x3f___closed__3,
    );
    v___x_1545_ = lean_array_push(v___x_1544_, v___x_1543_);
    return v___x_1545_;
}
pub unsafe fn _init_l_Lake_GitRepo_fetchRevision_x3f___closed__5() -> *mut LeanObject {
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    v___x_1546_ = l_Lake_GitRepo_fetchRevision_x3f___closed__0;
    v___x_1547_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_fetchRevision_x3f___closed__4),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_fetchRevision_x3f___closed__4_once),
        _init_l_Lake_GitRepo_fetchRevision_x3f___closed__4,
    );
    v___x_1548_ = lean_array_push(v___x_1547_, v___x_1546_);
    return v___x_1548_;
}
pub unsafe fn _init_l_Lake_GitRepo_fetchRevision_x3f___closed__6() -> *mut LeanObject {
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    v___x_1549_ = l_Lake_GitRepo_fetchRevision_x3f___closed__1;
    v___x_1550_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_fetchRevision_x3f___closed__5),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_fetchRevision_x3f___closed__5_once),
        _init_l_Lake_GitRepo_fetchRevision_x3f___closed__5,
    );
    v___x_1551_ = lean_array_push(v___x_1550_, v___x_1549_);
    return v___x_1551_;
}
pub unsafe fn l_Lake_GitRepo_fetchRevision_x3f(
    mut v_repo_1553_: *mut LeanObject,
    mut v_remote_1554_: *mut LeanObject,
    mut v_rev_1555_: *mut LeanObject,
    mut v_a_1556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: u8 = 0;
    let mut v___x_1566_: u8 = 0;
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: u8 = 0;
    v___x_1558_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_fetchRevision_x3f___closed__6),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_fetchRevision_x3f___closed__6_once),
        _init_l_Lake_GitRepo_fetchRevision_x3f___closed__6,
    );
    v___x_1559_ = lean_array_push(v___x_1558_, v_remote_1554_);
    v___x_1560_ = lean_array_push(v___x_1559_, v_rev_1555_);
    v___x_1561_ = l_Lake_GitRepo_captureGit___closed__0;
    v___x_1562_ = l_Lake_Git_filterUrl_x3f___closed__2;
    lean_inc_ref(v_repo_1553_);
    v___x_1563_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1563_, 0, v_repo_1553_);
    v___x_1564_ = l_Lake_GitRepo_captureGit___closed__1;
    v___x_1565_ = 1;
    v___x_1566_ = 0;
    v___x_1567_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_1567_, 0, v___x_1561_);
    lean_ctor_set(v___x_1567_, 1, v___x_1562_);
    lean_ctor_set(v___x_1567_, 2, v___x_1560_);
    lean_ctor_set(v___x_1567_, 3, v___x_1563_);
    lean_ctor_set(v___x_1567_, 4, v___x_1564_);
    lean_ctor_set_uint8(
        v___x_1567_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_1565_,
    );
    lean_ctor_set_uint8(
        v___x_1567_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_1566_,
    );
    v___x_1568_ = l_Lake_testProc(v___x_1567_);
    if v___x_1568_ == 0 {
        let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_repo_1553_);
        v___x_1569_ = lean_box(0);
        v___x_1570_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1570_, 0, v___x_1569_);
        lean_ctor_set(v___x_1570_, 1, v_a_1556_);
        return v___x_1570_;
    } else {
        let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
        v___x_1571_ = l_Lake_GitRev_fetchHead___closed__0;
        lean_inc_ref(v_repo_1553_);
        v___x_1572_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1571_, v_repo_1553_);
        if lean_obj_tag(v___x_1572_) == 1 {
            let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_repo_1553_);
            v___x_1573_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_1573_, 0, v___x_1572_);
            lean_ctor_set(v___x_1573_, 1, v_a_1556_);
            return v___x_1573_;
        } else {
            let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1576_: u8 = 0;
            let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_1572_);
            v___x_1574_ = l_Lake_GitRepo_fetchRevision_x3f___closed__7;
            v___x_1575_ = lean_string_append(v_repo_1553_, v___x_1574_);
            v___x_1576_ = 3;
            v___x_1577_ = lean_alloc_ctor(0, 1, (1) as u32);
            lean_ctor_set(v___x_1577_, 0, v___x_1575_);
            lean_ctor_set_uint8(
                v___x_1577_,
                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                v___x_1576_,
            );
            v___x_1578_ = lean_array_get_size(v_a_1556_);
            v___x_1579_ = lean_array_push(v_a_1556_, v___x_1577_);
            v___x_1580_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_1580_, 0, v___x_1578_);
            lean_ctor_set(v___x_1580_, 1, v___x_1579_);
            return v___x_1580_;
        }
    }
}
pub unsafe fn l_Lake_GitRepo_fetchRevision_x3f___boxed(
    mut v_repo_1581_: *mut LeanObject,
    mut v_remote_1582_: *mut LeanObject,
    mut v_rev_1583_: *mut LeanObject,
    mut v_a_1584_: *mut LeanObject,
    mut v_a_1585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1586_: *mut LeanObject = core::ptr::null_mut();
    v_res_1586_ =
        l_Lake_GitRepo_fetchRevision_x3f(v_repo_1581_, v_remote_1582_, v_rev_1583_, v_a_1584_);
    return v_res_1586_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(
    mut v_s_1589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    v___x_1590_ =
        l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0;
    return v___x_1590_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___boxed(
    mut v_s_1591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1592_: *mut LeanObject = core::ptr::null_mut();
    v_res_1592_ =
        l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v_s_1591_);
    lean_dec_ref(v_s_1591_);
    return v_res_1592_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(
    mut v___x_1593_: *mut LeanObject,
    mut v___x_1594_: *mut LeanObject,
    mut v___x_1595_: *mut LeanObject,
    mut v_a_1596_: *mut LeanObject,
    mut v_b_1597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currPos_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1610_: u8 = 0;
    let mut v_startInclusive_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: u8 = 0;
    let mut v___x_1615_: u32 = 0;
    let mut v___x_1616_: u32 = 0;
    let mut v___x_1617_: u8 = 0;
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_slice_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1633_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1596_) == 0 {
                    v_currPos_1606_ = lean_ctor_get(v_a_1596_, 0);
                    v_searcher_1607_ = lean_ctor_get(v_a_1596_, 1);
                    v_isSharedCheck_1633_ = (!lean_is_exclusive(v_a_1596_)) as u8;
                    if v_isSharedCheck_1633_ == 0 {
                        v___x_1609_ = v_a_1596_;
                        v_isShared_1610_ = v_isSharedCheck_1633_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_searcher_1607_);
                        lean_inc(v_currPos_1606_);
                        lean_dec(v_a_1596_);
                        v___x_1609_ = lean_box(0);
                        v_isShared_1610_ = v_isSharedCheck_1633_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1595_);
                    lean_dec_ref(v___x_1593_);
                    return v_b_1597_;
                }
            }
            1 => {
                lean_inc_ref(v___x_1593_);
                v___x_1602_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1602_, 0, v___x_1593_);
                lean_ctor_set(v___x_1602_, 1, v_startInclusive_1600_);
                lean_ctor_set(v___x_1602_, 2, v_endExclusive_1601_);
                v___x_1603_ = l_String_Slice_toString(v___x_1602_);
                lean_dec_ref_known(v___x_1602_, 3);
                v___x_1604_ = lean_array_push(v_b_1597_, v___x_1603_);
                v_a_1596_ = v_it_1599_;
                v_b_1597_ = v___x_1604_;
                state = 0;
                continue;
            }
            2 => {
                v_startInclusive_1611_ = lean_ctor_get(v___x_1594_, 1);
                v_endExclusive_1612_ = lean_ctor_get(v___x_1594_, 2);
                v___x_1613_ = lean_nat_sub(v_endExclusive_1612_, v_startInclusive_1611_);
                v___x_1614_ = lean_nat_dec_eq(v_searcher_1607_, v___x_1613_);
                lean_dec(v___x_1613_);
                if v___x_1614_ == 0 {
                    v___x_1615_ = 10;
                    v___x_1616_ = lean_string_utf8_get_fast(v___x_1593_, v_searcher_1607_);
                    v___x_1617_ = lean_uint32_dec_eq(v___x_1616_, v___x_1615_);
                    if v___x_1617_ == 0 {
                        v___x_1618_ = lean_string_utf8_next_fast(v___x_1593_, v_searcher_1607_);
                        lean_dec(v_searcher_1607_);
                        if v_isShared_1610_ == 0 {
                            lean_ctor_set(v___x_1609_, 1, v___x_1618_);
                            v___x_1620_ = v___x_1609_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_currPos_1606_);
                            lean_ctor_set(v_reuseFailAlloc_1622_, 1, v___x_1618_);
                            v___x_1620_ = v_reuseFailAlloc_1622_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1623_ = lean_string_utf8_next_fast(v___x_1593_, v_searcher_1607_);
                        v___x_1624_ = lean_nat_sub(v___x_1623_, v_searcher_1607_);
                        v___x_1625_ = lean_nat_add(v_searcher_1607_, v___x_1624_);
                        lean_dec(v___x_1624_);
                        v_slice_1626_ = l_String_Slice_subslice_x21(
                            v___x_1594_,
                            v_currPos_1606_,
                            v_searcher_1607_,
                        );
                        lean_inc(v___x_1625_);
                        if v_isShared_1610_ == 0 {
                            lean_ctor_set(v___x_1609_, 1, v___x_1625_);
                            lean_ctor_set(v___x_1609_, 0, v___x_1625_);
                            v_nextIt_1628_ = v___x_1609_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1625_);
                            lean_ctor_set(v_reuseFailAlloc_1631_, 1, v___x_1625_);
                            v_nextIt_1628_ = v_reuseFailAlloc_1631_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_1609_);
                    lean_dec(v_searcher_1607_);
                    v___x_1632_ = lean_box(1);
                    lean_inc(v___x_1595_);
                    v_it_1599_ = v___x_1632_;
                    v_startInclusive_1600_ = v_currPos_1606_;
                    v_endExclusive_1601_ = v___x_1595_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_1596_ = v___x_1620_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_1629_ = lean_ctor_get(v_slice_1626_, 0);
                lean_inc(v_startInclusive_1629_);
                v_endExclusive_1630_ = lean_ctor_get(v_slice_1626_, 1);
                lean_inc(v_endExclusive_1630_);
                lean_dec_ref(v_slice_1626_);
                v_it_1599_ = v_nextIt_1628_;
                v_startInclusive_1600_ = v_startInclusive_1629_;
                v_endExclusive_1601_ = v_endExclusive_1630_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg___boxed(
    mut v___x_1634_: *mut LeanObject,
    mut v___x_1635_: *mut LeanObject,
    mut v___x_1636_: *mut LeanObject,
    mut v_a_1637_: *mut LeanObject,
    mut v_b_1638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1639_: *mut LeanObject = core::ptr::null_mut();
    v_res_1639_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_1634_, v___x_1635_, v___x_1636_, v_a_1637_, v_b_1638_);
    lean_dec_ref(v___x_1635_);
    return v_res_1639_;
}
pub unsafe fn _init_l_Lake_GitRepo_getHeadRevisions___closed__3() -> *mut LeanObject {
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    v___x_1648_ = l_Lake_GitRepo_getHeadRevisions___closed__2;
    v___x_1649_ = lean_unsigned_to_nat(2);
    v___x_1650_ = lean_mk_empty_array_with_capacity(v___x_1649_);
    v___x_1651_ = lean_array_push(v___x_1650_, v___x_1648_);
    return v___x_1651_;
}
pub unsafe fn l_Lake_GitRepo_getHeadRevisions(
    mut v_repo_1652_: *mut LeanObject,
    mut v_n_1653_: *mut LeanObject,
    mut v_a_1654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: u8 = 0;
    let mut v___x_1664_: u8 = 0;
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1671_: u8 = 0;
    let mut v_stdout_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1681_: u8 = 0;
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1692_: u8 = 0;
    let mut v_isSharedCheck_1693_: u8 = 0;
    let mut v_a_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1698_: u8 = 0;
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1702_: u8 = 0;
    let mut v_args_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: u8 = 0;
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_args_1703_ = l_Lake_GitRepo_getHeadRevisions___closed__1;
                v___x_1704_ = lean_unsigned_to_nat(0);
                v___x_1705_ = lean_nat_dec_eq(v_n_1653_, v___x_1704_);
                if v___x_1705_ == 0 {
                    v___x_1706_ = l_Nat_reprFast(v_n_1653_);
                    v___x_1707_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_GitRepo_getHeadRevisions___closed__3),
                        core::ptr::addr_of_mut!(l_Lake_GitRepo_getHeadRevisions___closed__3_once),
                        _init_l_Lake_GitRepo_getHeadRevisions___closed__3,
                    );
                    v___x_1708_ = lean_array_push(v___x_1707_, v___x_1706_);
                    v___x_1709_ = l_Array_append___redArg(v_args_1703_, v___x_1708_);
                    lean_dec_ref(v___x_1708_);
                    v___y_1657_ = v___x_1709_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_n_1653_);
                    v___y_1657_ = v_args_1703_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1658_ = l_Lake_GitRepo_captureGit___closed__0;
                v___x_1659_ = l_Lake_Git_filterUrl_x3f___closed__2;
                v___x_1660_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1660_, 0, v_repo_1652_);
                v___x_1661_ = lean_unsigned_to_nat(0);
                v___x_1662_ = l_Lake_GitRepo_captureGit___closed__1;
                v___x_1663_ = 1;
                v___x_1664_ = 0;
                v___x_1665_ = lean_alloc_ctor(0, 5, (2) as u32);
                lean_ctor_set(v___x_1665_, 0, v___x_1658_);
                lean_ctor_set(v___x_1665_, 1, v___x_1659_);
                lean_ctor_set(v___x_1665_, 2, v___y_1657_);
                lean_ctor_set(v___x_1665_, 3, v___x_1660_);
                lean_ctor_set(v___x_1665_, 4, v___x_1662_);
                lean_ctor_set_uint8(
                    v___x_1665_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___x_1663_,
                );
                lean_ctor_set_uint8(
                    v___x_1665_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___x_1664_,
                );
                v___x_1666_ = l_Lake_captureProc_x27(v___x_1665_, v_a_1654_);
                if lean_obj_tag(v___x_1666_) == 0 {
                    v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
                    v_a_1668_ = lean_ctor_get(v___x_1666_, 1);
                    v_isSharedCheck_1693_ = (!lean_is_exclusive(v___x_1666_)) as u8;
                    if v_isSharedCheck_1693_ == 0 {
                        v___x_1670_ = v___x_1666_;
                        v_isShared_1671_ = v_isSharedCheck_1693_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1668_);
                        lean_inc(v_a_1667_);
                        lean_dec(v___x_1666_);
                        v___x_1670_ = lean_box(0);
                        v_isShared_1671_ = v_isSharedCheck_1693_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1694_ = lean_ctor_get(v___x_1666_, 0);
                    v_a_1695_ = lean_ctor_get(v___x_1666_, 1);
                    v_isSharedCheck_1702_ = (!lean_is_exclusive(v___x_1666_)) as u8;
                    if v_isSharedCheck_1702_ == 0 {
                        v___x_1697_ = v___x_1666_;
                        v_isShared_1698_ = v_isSharedCheck_1702_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_1695_);
                        lean_inc(v_a_1694_);
                        lean_dec(v___x_1666_);
                        v___x_1697_ = lean_box(0);
                        v_isShared_1698_ = v_isSharedCheck_1702_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_stdout_1672_ = lean_ctor_get(v_a_1667_, 0);
                lean_inc_ref(v_stdout_1672_);
                lean_dec(v_a_1667_);
                v___x_1673_ = lean_string_utf8_byte_size(v_stdout_1672_);
                v___x_1674_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1674_, 0, v_stdout_1672_);
                lean_ctor_set(v___x_1674_, 1, v___x_1661_);
                lean_ctor_set(v___x_1674_, 2, v___x_1673_);
                v___x_1675_ = l_String_Slice_trimAscii(v___x_1674_);
                v_str_1676_ = lean_ctor_get(v___x_1675_, 0);
                v_startInclusive_1677_ = lean_ctor_get(v___x_1675_, 1);
                v_endExclusive_1678_ = lean_ctor_get(v___x_1675_, 2);
                v_isSharedCheck_1692_ = (!lean_is_exclusive(v___x_1675_)) as u8;
                if v_isSharedCheck_1692_ == 0 {
                    v___x_1680_ = v___x_1675_;
                    v_isShared_1681_ = v_isSharedCheck_1692_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_endExclusive_1678_);
                    lean_inc(v_startInclusive_1677_);
                    lean_inc(v_str_1676_);
                    lean_dec(v___x_1675_);
                    v___x_1680_ = lean_box(0);
                    v_isShared_1681_ = v_isSharedCheck_1692_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1682_ = lean_string_utf8_extract(
                    v_str_1676_,
                    v_startInclusive_1677_,
                    v_endExclusive_1678_,
                );
                lean_dec(v_endExclusive_1678_);
                lean_dec(v_startInclusive_1677_);
                lean_dec_ref(v_str_1676_);
                v___x_1683_ = lean_string_utf8_byte_size(v___x_1682_);
                lean_inc_ref(v___x_1682_);
                if v_isShared_1681_ == 0 {
                    lean_ctor_set(v___x_1680_, 2, v___x_1683_);
                    lean_ctor_set(v___x_1680_, 1, v___x_1661_);
                    lean_ctor_set(v___x_1680_, 0, v___x_1682_);
                    v___x_1685_ = v___x_1680_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1682_);
                    lean_ctor_set(v_reuseFailAlloc_1691_, 1, v___x_1661_);
                    lean_ctor_set(v_reuseFailAlloc_1691_, 2, v___x_1683_);
                    v___x_1685_ = v_reuseFailAlloc_1691_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1686_ =
                    l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(
                        v___x_1685_,
                    );
                v___x_1687_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_1682_, v___x_1685_, v___x_1683_, v___x_1686_, v___x_1662_);
                lean_dec_ref(v___x_1685_);
                if v_isShared_1671_ == 0 {
                    lean_ctor_set(v___x_1670_, 0, v___x_1687_);
                    v___x_1689_ = v___x_1670_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1687_);
                    lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_a_1668_);
                    v___x_1689_ = v_reuseFailAlloc_1690_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1689_;
            }
            6 => {
                if v_isShared_1698_ == 0 {
                    v___x_1700_ = v___x_1697_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1694_);
                    lean_ctor_set(v_reuseFailAlloc_1701_, 1, v_a_1695_);
                    v___x_1700_ = v_reuseFailAlloc_1701_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1700_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_GitRepo_getHeadRevisions___boxed(
    mut v_repo_1710_: *mut LeanObject,
    mut v_n_1711_: *mut LeanObject,
    mut v_a_1712_: *mut LeanObject,
    mut v_a_1713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1714_: *mut LeanObject = core::ptr::null_mut();
    v_res_1714_ = l_Lake_GitRepo_getHeadRevisions(v_repo_1710_, v_n_1711_, v_a_1712_);
    return v_res_1714_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(
    mut v___x_1715_: *mut LeanObject,
    mut v___x_1716_: *mut LeanObject,
    mut v___x_1717_: *mut LeanObject,
    mut v_inst_1718_: *mut LeanObject,
    mut v_R_1719_: *mut LeanObject,
    mut v_a_1720_: *mut LeanObject,
    mut v_b_1721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    v___x_1722_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_1715_, v___x_1716_, v___x_1717_, v_a_1720_, v_b_1721_);
    return v___x_1722_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___boxed(
    mut v___x_1723_: *mut LeanObject,
    mut v___x_1724_: *mut LeanObject,
    mut v___x_1725_: *mut LeanObject,
    mut v_inst_1726_: *mut LeanObject,
    mut v_R_1727_: *mut LeanObject,
    mut v_a_1728_: *mut LeanObject,
    mut v_b_1729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1730_: *mut LeanObject = core::ptr::null_mut();
    v_res_1730_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(v___x_1723_, v___x_1724_, v___x_1725_, v_inst_1726_, v_R_1727_, v_a_1728_, v_b_1729_);
    lean_dec_ref(v___x_1724_);
    return v_res_1730_;
}
pub unsafe fn l_Lake_GitRepo_resolveRemoteRevision(
    mut v_rev_1731_: *mut LeanObject,
    mut v_remote_1732_: *mut LeanObject,
    mut v_repo_1733_: *mut LeanObject,
    mut v_a_1734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_rev_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: u8 = 0;
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: u8 = 0;
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1740_ = l_Lake_GitRev_isFullSha1(v_rev_1731_);
                if v___x_1740_ == 0 {
                    v___x_1741_ = l_Lake_GitRev_withRemote___closed__0;
                    v___x_1742_ = lean_string_append(v_remote_1732_, v___x_1741_);
                    v___x_1743_ = lean_string_append(v___x_1742_, v_rev_1731_);
                    lean_inc_ref(v_repo_1733_);
                    v___x_1744_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1743_, v_repo_1733_);
                    if lean_obj_tag(v___x_1744_) == 1 {
                        lean_dec_ref(v_repo_1733_);
                        lean_dec_ref(v_rev_1731_);
                        v_val_1745_ = lean_ctor_get(v___x_1744_, 0);
                        lean_inc(v_val_1745_);
                        lean_dec_ref_known(v___x_1744_, 1);
                        v_rev_1737_ = v_val_1745_;
                        v___y_1738_ = v_a_1734_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1744_);
                        lean_inc_ref(v_repo_1733_);
                        lean_inc_ref(v_rev_1731_);
                        v___x_1746_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_1731_, v_repo_1733_);
                        if lean_obj_tag(v___x_1746_) == 1 {
                            lean_dec_ref(v_repo_1733_);
                            lean_dec_ref(v_rev_1731_);
                            v_val_1747_ = lean_ctor_get(v___x_1746_, 0);
                            lean_inc(v_val_1747_);
                            lean_dec_ref_known(v___x_1746_, 1);
                            v_rev_1737_ = v_val_1747_;
                            v___y_1738_ = v_a_1734_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_1746_);
                            v___x_1748_ = l_Lake_GitRepo_resolveRevision___closed__0;
                            v___x_1749_ = lean_string_append(v_repo_1733_, v___x_1748_);
                            v___x_1750_ = lean_string_append(v___x_1749_, v_rev_1731_);
                            lean_dec_ref(v_rev_1731_);
                            v___x_1751_ = l_Lake_GitRepo_resolveRevision___closed__1;
                            v___x_1752_ = lean_string_append(v___x_1750_, v___x_1751_);
                            v___x_1753_ = 3;
                            v___x_1754_ = lean_alloc_ctor(0, 1, (1) as u32);
                            lean_ctor_set(v___x_1754_, 0, v___x_1752_);
                            lean_ctor_set_uint8(
                                v___x_1754_,
                                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                v___x_1753_,
                            );
                            v___x_1755_ = lean_array_get_size(v_a_1734_);
                            v___x_1756_ = lean_array_push(v_a_1734_, v___x_1754_);
                            v___x_1757_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_1757_, 0, v___x_1755_);
                            lean_ctor_set(v___x_1757_, 1, v___x_1756_);
                            return v___x_1757_;
                        }
                    }
                } else {
                    lean_dec_ref(v_repo_1733_);
                    lean_dec_ref(v_remote_1732_);
                    v___x_1758_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1758_, 0, v_rev_1731_);
                    lean_ctor_set(v___x_1758_, 1, v_a_1734_);
                    return v___x_1758_;
                }
            }
            1 => {
                v___x_1739_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1739_, 0, v_rev_1737_);
                lean_ctor_set(v___x_1739_, 1, v___y_1738_);
                return v___x_1739_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_GitRepo_resolveRemoteRevision___boxed(
    mut v_rev_1759_: *mut LeanObject,
    mut v_remote_1760_: *mut LeanObject,
    mut v_repo_1761_: *mut LeanObject,
    mut v_a_1762_: *mut LeanObject,
    mut v_a_1763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1764_: *mut LeanObject = core::ptr::null_mut();
    v_res_1764_ =
        l_Lake_GitRepo_resolveRemoteRevision(v_rev_1759_, v_remote_1760_, v_repo_1761_, v_a_1762_);
    return v_res_1764_;
}
pub unsafe fn l_Lake_GitRepo_findRemoteRevision(
    mut v_repo_1765_: *mut LeanObject,
    mut v_rev_x3f_1766_: *mut LeanObject,
    mut v_remote_1767_: *mut LeanObject,
    mut v_a_1768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1781_: u8 = 0;
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1785_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_remote_1767_);
                lean_inc_ref(v_repo_1765_);
                v___x_1770_ = l_Lake_GitRepo_fetch(v_repo_1765_, v_remote_1767_, v_a_1768_);
                if lean_obj_tag(v___x_1770_) == 0 {
                    if lean_obj_tag(v_rev_x3f_1766_) == 0 {
                        v_a_1771_ = lean_ctor_get(v___x_1770_, 1);
                        lean_inc(v_a_1771_);
                        lean_dec_ref_known(v___x_1770_, 2);
                        v___x_1772_ = l_Lake_Git_upstreamBranch___closed__0;
                        v___x_1773_ = l_Lake_GitRepo_resolveRemoteRevision(
                            v___x_1772_,
                            v_remote_1767_,
                            v_repo_1765_,
                            v_a_1771_,
                        );
                        return v___x_1773_;
                    } else {
                        v_a_1774_ = lean_ctor_get(v___x_1770_, 1);
                        lean_inc(v_a_1774_);
                        lean_dec_ref_known(v___x_1770_, 2);
                        v_val_1775_ = lean_ctor_get(v_rev_x3f_1766_, 0);
                        lean_inc(v_val_1775_);
                        lean_dec_ref_known(v_rev_x3f_1766_, 1);
                        v___x_1776_ = l_Lake_GitRepo_resolveRemoteRevision(
                            v_val_1775_,
                            v_remote_1767_,
                            v_repo_1765_,
                            v_a_1774_,
                        );
                        return v___x_1776_;
                    }
                } else {
                    lean_dec_ref(v_remote_1767_);
                    lean_dec(v_rev_x3f_1766_);
                    lean_dec_ref(v_repo_1765_);
                    v_a_1777_ = lean_ctor_get(v___x_1770_, 0);
                    v_a_1778_ = lean_ctor_get(v___x_1770_, 1);
                    v_isSharedCheck_1785_ = (!lean_is_exclusive(v___x_1770_)) as u8;
                    if v_isSharedCheck_1785_ == 0 {
                        v___x_1780_ = v___x_1770_;
                        v_isShared_1781_ = v_isSharedCheck_1785_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1778_);
                        lean_inc(v_a_1777_);
                        lean_dec(v___x_1770_);
                        v___x_1780_ = lean_box(0);
                        v_isShared_1781_ = v_isSharedCheck_1785_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1781_ == 0 {
                    v___x_1783_ = v___x_1780_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1777_);
                    lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_a_1778_);
                    v___x_1783_ = v_reuseFailAlloc_1784_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1783_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_GitRepo_findRemoteRevision___boxed(
    mut v_repo_1786_: *mut LeanObject,
    mut v_rev_x3f_1787_: *mut LeanObject,
    mut v_remote_1788_: *mut LeanObject,
    mut v_a_1789_: *mut LeanObject,
    mut v_a_1790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1791_: *mut LeanObject = core::ptr::null_mut();
    v_res_1791_ =
        l_Lake_GitRepo_findRemoteRevision(v_repo_1786_, v_rev_x3f_1787_, v_remote_1788_, v_a_1789_);
    return v_res_1791_;
}
pub unsafe fn _init_l_Lake_GitRepo_branchExists___closed__2() -> *mut LeanObject {
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    v___x_1794_ = l_Lake_GitRepo_branchExists___closed__0;
    v___x_1795_ = lean_unsigned_to_nat(3);
    v___x_1796_ = lean_mk_empty_array_with_capacity(v___x_1795_);
    v___x_1797_ = lean_array_push(v___x_1796_, v___x_1794_);
    return v___x_1797_;
}
pub unsafe fn _init_l_Lake_GitRepo_branchExists___closed__3() -> *mut LeanObject {
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    v___x_1798_ = l_Lake_GitRepo_resolveRevision_x3f___closed__0;
    v___x_1799_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_branchExists___closed__2),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_branchExists___closed__2_once),
        _init_l_Lake_GitRepo_branchExists___closed__2,
    );
    v___x_1800_ = lean_array_push(v___x_1799_, v___x_1798_);
    return v___x_1800_;
}
pub unsafe fn l_Lake_GitRepo_branchExists(
    mut v_rev_1801_: *mut LeanObject,
    mut v_repo_1802_: *mut LeanObject,
) -> u8 {
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: u8 = 0;
    let mut v___x_1813_: u8 = 0;
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: u8 = 0;
    v___x_1804_ = l_Lake_GitRepo_branchExists___closed__1;
    v___x_1805_ = lean_string_append(v___x_1804_, v_rev_1801_);
    v___x_1806_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_branchExists___closed__3),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_branchExists___closed__3_once),
        _init_l_Lake_GitRepo_branchExists___closed__3,
    );
    v___x_1807_ = lean_array_push(v___x_1806_, v___x_1805_);
    v___x_1808_ = l_Lake_GitRepo_captureGit___closed__0;
    v___x_1809_ = l_Lake_Git_filterUrl_x3f___closed__2;
    v___x_1810_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1810_, 0, v_repo_1802_);
    v___x_1811_ = l_Lake_GitRepo_captureGit___closed__1;
    v___x_1812_ = 1;
    v___x_1813_ = 0;
    v___x_1814_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_1814_, 0, v___x_1808_);
    lean_ctor_set(v___x_1814_, 1, v___x_1809_);
    lean_ctor_set(v___x_1814_, 2, v___x_1807_);
    lean_ctor_set(v___x_1814_, 3, v___x_1810_);
    lean_ctor_set(v___x_1814_, 4, v___x_1811_);
    lean_ctor_set_uint8(
        v___x_1814_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_1812_,
    );
    lean_ctor_set_uint8(
        v___x_1814_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_1813_,
    );
    v___x_1815_ = l_Lake_testProc(v___x_1814_);
    return v___x_1815_;
}
pub unsafe fn l_Lake_GitRepo_branchExists___boxed(
    mut v_rev_1816_: *mut LeanObject,
    mut v_repo_1817_: *mut LeanObject,
    mut v_a_1818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1819_: u8 = 0;
    let mut v_r_1820_: *mut LeanObject = core::ptr::null_mut();
    v_res_1819_ = l_Lake_GitRepo_branchExists(v_rev_1816_, v_repo_1817_);
    lean_dec_ref(v_rev_1816_);
    v_r_1820_ = lean_box((v_res_1819_) as usize);
    return v_r_1820_;
}
pub unsafe fn _init_l_Lake_GitRepo_revisionExists___closed__0() -> *mut LeanObject {
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    v___x_1821_ = l_Lake_GitRepo_insideWorkTree___closed__0;
    v___x_1822_ = lean_unsigned_to_nat(3);
    v___x_1823_ = lean_mk_empty_array_with_capacity(v___x_1822_);
    v___x_1824_ = lean_array_push(v___x_1823_, v___x_1821_);
    return v___x_1824_;
}
pub unsafe fn _init_l_Lake_GitRepo_revisionExists___closed__1() -> *mut LeanObject {
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    v___x_1825_ = l_Lake_GitRepo_resolveRevision_x3f___closed__0;
    v___x_1826_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_revisionExists___closed__0),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_revisionExists___closed__0_once),
        _init_l_Lake_GitRepo_revisionExists___closed__0,
    );
    v___x_1827_ = lean_array_push(v___x_1826_, v___x_1825_);
    return v___x_1827_;
}
pub unsafe fn l_Lake_GitRepo_revisionExists(
    mut v_rev_1828_: *mut LeanObject,
    mut v_repo_1829_: *mut LeanObject,
) -> u8 {
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: u8 = 0;
    let mut v___x_1840_: u8 = 0;
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: u8 = 0;
    v___x_1831_ = l_Lake_GitRepo_findCommit_x3f___closed__0;
    v___x_1832_ = lean_string_append(v_rev_1828_, v___x_1831_);
    v___x_1833_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_revisionExists___closed__1),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_revisionExists___closed__1_once),
        _init_l_Lake_GitRepo_revisionExists___closed__1,
    );
    v___x_1834_ = lean_array_push(v___x_1833_, v___x_1832_);
    v___x_1835_ = l_Lake_GitRepo_captureGit___closed__0;
    v___x_1836_ = l_Lake_Git_filterUrl_x3f___closed__2;
    v___x_1837_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1837_, 0, v_repo_1829_);
    v___x_1838_ = l_Lake_GitRepo_captureGit___closed__1;
    v___x_1839_ = 1;
    v___x_1840_ = 0;
    v___x_1841_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_1841_, 0, v___x_1835_);
    lean_ctor_set(v___x_1841_, 1, v___x_1836_);
    lean_ctor_set(v___x_1841_, 2, v___x_1834_);
    lean_ctor_set(v___x_1841_, 3, v___x_1837_);
    lean_ctor_set(v___x_1841_, 4, v___x_1838_);
    lean_ctor_set_uint8(
        v___x_1841_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_1839_,
    );
    lean_ctor_set_uint8(
        v___x_1841_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_1840_,
    );
    v___x_1842_ = l_Lake_testProc(v___x_1841_);
    return v___x_1842_;
}
pub unsafe fn l_Lake_GitRepo_revisionExists___boxed(
    mut v_rev_1843_: *mut LeanObject,
    mut v_repo_1844_: *mut LeanObject,
    mut v_a_1845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1846_: u8 = 0;
    let mut v_r_1847_: *mut LeanObject = core::ptr::null_mut();
    v_res_1846_ = l_Lake_GitRepo_revisionExists(v_rev_1843_, v_repo_1844_);
    v_r_1847_ = lean_box((v_res_1846_) as usize);
    return v_r_1847_;
}
pub unsafe fn l_Lake_GitRepo_getTags(mut v_repo_1853_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: u8 = 0;
    let mut v___x_1862_: u8 = 0;
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    v___x_1855_ = l_Lake_GitRepo_getTags___closed__1;
    v___x_1856_ = l_Lake_GitRepo_captureGit___closed__0;
    v___x_1857_ = l_Lake_Git_filterUrl_x3f___closed__2;
    v___x_1858_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1858_, 0, v_repo_1853_);
    v___x_1859_ = lean_unsigned_to_nat(0);
    v___x_1860_ = l_Lake_GitRepo_captureGit___closed__1;
    v___x_1861_ = 1;
    v___x_1862_ = 0;
    v___x_1863_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_1863_, 0, v___x_1856_);
    lean_ctor_set(v___x_1863_, 1, v___x_1857_);
    lean_ctor_set(v___x_1863_, 2, v___x_1855_);
    lean_ctor_set(v___x_1863_, 3, v___x_1858_);
    lean_ctor_set(v___x_1863_, 4, v___x_1860_);
    lean_ctor_set_uint8(
        v___x_1863_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_1861_,
    );
    lean_ctor_set_uint8(
        v___x_1863_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_1862_,
    );
    v___x_1864_ = l_Lake_captureProc_x3f(v___x_1863_);
    if lean_obj_tag(v___x_1864_) == 1 {
        let mut v_val_1865_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
        v_val_1865_ = lean_ctor_get(v___x_1864_, 0);
        lean_inc_n(v_val_1865_, 2);
        lean_dec_ref_known(v___x_1864_, 1);
        v___x_1866_ = lean_string_utf8_byte_size(v_val_1865_);
        v___x_1867_ = lean_alloc_ctor(0, 3, (0) as u32);
        lean_ctor_set(v___x_1867_, 0, v_val_1865_);
        lean_ctor_set(v___x_1867_, 1, v___x_1859_);
        lean_ctor_set(v___x_1867_, 2, v___x_1866_);
        v___x_1868_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(
            v___x_1867_,
        );
        v___x_1869_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v_val_1865_, v___x_1867_, v___x_1866_, v___x_1868_, v___x_1860_);
        lean_dec_ref_known(v___x_1867_, 3);
        v___x_1870_ = lean_array_to_list(v___x_1869_);
        return v___x_1870_;
    } else {
        let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_1864_);
        v___x_1871_ = lean_box(0);
        return v___x_1871_;
    }
}
pub unsafe fn l_Lake_GitRepo_getTags___boxed(
    mut v_repo_1872_: *mut LeanObject,
    mut v_a_1873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1874_: *mut LeanObject = core::ptr::null_mut();
    v_res_1874_ = l_Lake_GitRepo_getTags(v_repo_1872_);
    return v_res_1874_;
}
pub unsafe fn _init_l_Lake_GitRepo_findTag_x3f___closed__2() -> *mut LeanObject {
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    v___x_1877_ = l_Lake_GitRepo_findTag_x3f___closed__0;
    v___x_1878_ = lean_unsigned_to_nat(4);
    v___x_1879_ = lean_mk_empty_array_with_capacity(v___x_1878_);
    v___x_1880_ = lean_array_push(v___x_1879_, v___x_1877_);
    return v___x_1880_;
}
pub unsafe fn _init_l_Lake_GitRepo_findTag_x3f___closed__3() -> *mut LeanObject {
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    v___x_1881_ = l_Lake_GitRepo_fetch___closed__1;
    v___x_1882_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_findTag_x3f___closed__2),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_findTag_x3f___closed__2_once),
        _init_l_Lake_GitRepo_findTag_x3f___closed__2,
    );
    v___x_1883_ = lean_array_push(v___x_1882_, v___x_1881_);
    return v___x_1883_;
}
pub unsafe fn _init_l_Lake_GitRepo_findTag_x3f___closed__4() -> *mut LeanObject {
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    v___x_1884_ = l_Lake_GitRepo_findTag_x3f___closed__1;
    v___x_1885_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_findTag_x3f___closed__3),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_findTag_x3f___closed__3_once),
        _init_l_Lake_GitRepo_findTag_x3f___closed__3,
    );
    v___x_1886_ = lean_array_push(v___x_1885_, v___x_1884_);
    return v___x_1886_;
}
pub unsafe fn l_Lake_GitRepo_findTag_x3f(
    mut v_rev_1887_: *mut LeanObject,
    mut v_repo_1888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: u8 = 0;
    let mut v___x_1897_: u8 = 0;
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    v___x_1890_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_findTag_x3f___closed__4),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_findTag_x3f___closed__4_once),
        _init_l_Lake_GitRepo_findTag_x3f___closed__4,
    );
    v___x_1891_ = lean_array_push(v___x_1890_, v_rev_1887_);
    v___x_1892_ = l_Lake_GitRepo_captureGit___closed__0;
    v___x_1893_ = l_Lake_Git_filterUrl_x3f___closed__2;
    v___x_1894_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1894_, 0, v_repo_1888_);
    v___x_1895_ = l_Lake_GitRepo_captureGit___closed__1;
    v___x_1896_ = 1;
    v___x_1897_ = 0;
    v___x_1898_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_1898_, 0, v___x_1892_);
    lean_ctor_set(v___x_1898_, 1, v___x_1893_);
    lean_ctor_set(v___x_1898_, 2, v___x_1891_);
    lean_ctor_set(v___x_1898_, 3, v___x_1894_);
    lean_ctor_set(v___x_1898_, 4, v___x_1895_);
    lean_ctor_set_uint8(
        v___x_1898_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_1896_,
    );
    lean_ctor_set_uint8(
        v___x_1898_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_1897_,
    );
    v___x_1899_ = l_Lake_captureProc_x3f(v___x_1898_);
    return v___x_1899_;
}
pub unsafe fn l_Lake_GitRepo_findTag_x3f___boxed(
    mut v_rev_1900_: *mut LeanObject,
    mut v_repo_1901_: *mut LeanObject,
    mut v_a_1902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1903_: *mut LeanObject = core::ptr::null_mut();
    v_res_1903_ = l_Lake_GitRepo_findTag_x3f(v_rev_1900_, v_repo_1901_);
    return v_res_1903_;
}
pub unsafe fn _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2() -> *mut LeanObject {
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    v___x_1906_ = l_Lake_GitRepo_getRemoteUrl_x3f___closed__0;
    v___x_1907_ = lean_unsigned_to_nat(3);
    v___x_1908_ = lean_mk_empty_array_with_capacity(v___x_1907_);
    v___x_1909_ = lean_array_push(v___x_1908_, v___x_1906_);
    return v___x_1909_;
}
pub unsafe fn _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3() -> *mut LeanObject {
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    v___x_1910_ = l_Lake_GitRepo_getRemoteUrl_x3f___closed__1;
    v___x_1911_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_getRemoteUrl_x3f___closed__2),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_getRemoteUrl_x3f___closed__2_once),
        _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2,
    );
    v___x_1912_ = lean_array_push(v___x_1911_, v___x_1910_);
    return v___x_1912_;
}
pub unsafe fn l_Lake_GitRepo_getRemoteUrl_x3f(
    mut v_remote_1913_: *mut LeanObject,
    mut v_repo_1914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: u8 = 0;
    let mut v___x_1923_: u8 = 0;
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    v___x_1916_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_getRemoteUrl_x3f___closed__3),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_getRemoteUrl_x3f___closed__3_once),
        _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3,
    );
    v___x_1917_ = lean_array_push(v___x_1916_, v_remote_1913_);
    v___x_1918_ = l_Lake_GitRepo_captureGit___closed__0;
    v___x_1919_ = l_Lake_Git_filterUrl_x3f___closed__2;
    v___x_1920_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1920_, 0, v_repo_1914_);
    v___x_1921_ = l_Lake_GitRepo_captureGit___closed__1;
    v___x_1922_ = 1;
    v___x_1923_ = 0;
    v___x_1924_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_1924_, 0, v___x_1918_);
    lean_ctor_set(v___x_1924_, 1, v___x_1919_);
    lean_ctor_set(v___x_1924_, 2, v___x_1917_);
    lean_ctor_set(v___x_1924_, 3, v___x_1920_);
    lean_ctor_set(v___x_1924_, 4, v___x_1921_);
    lean_ctor_set_uint8(
        v___x_1924_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_1922_,
    );
    lean_ctor_set_uint8(
        v___x_1924_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_1923_,
    );
    v___x_1925_ = l_Lake_captureProc_x3f(v___x_1924_);
    return v___x_1925_;
}
pub unsafe fn l_Lake_GitRepo_getRemoteUrl_x3f___boxed(
    mut v_remote_1926_: *mut LeanObject,
    mut v_repo_1927_: *mut LeanObject,
    mut v_a_1928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1929_: *mut LeanObject = core::ptr::null_mut();
    v_res_1929_ = l_Lake_GitRepo_getRemoteUrl_x3f(v_remote_1926_, v_repo_1927_);
    return v_res_1929_;
}
pub unsafe fn _init_l_Lake_GitRepo_addRemote___closed__0() -> *mut LeanObject {
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    v___x_1930_ = l_Lake_GitRepo_getRemoteUrl_x3f___closed__0;
    v___x_1931_ = lean_unsigned_to_nat(4);
    v___x_1932_ = lean_mk_empty_array_with_capacity(v___x_1931_);
    v___x_1933_ = lean_array_push(v___x_1932_, v___x_1930_);
    return v___x_1933_;
}
pub unsafe fn _init_l_Lake_GitRepo_addRemote___closed__1() -> *mut LeanObject {
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    v___x_1934_ = l_Lake_GitRepo_addWorktreeDetach___closed__1;
    v___x_1935_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_addRemote___closed__0),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_addRemote___closed__0_once),
        _init_l_Lake_GitRepo_addRemote___closed__0,
    );
    v___x_1936_ = lean_array_push(v___x_1935_, v___x_1934_);
    return v___x_1936_;
}
pub unsafe fn l_Lake_GitRepo_addRemote(
    mut v_remote_1937_: *mut LeanObject,
    mut v_url_1938_: *mut LeanObject,
    mut v_repo_1939_: *mut LeanObject,
    mut v_a_1940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: u8 = 0;
    let mut v___x_1950_: u8 = 0;
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    v___x_1942_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_addRemote___closed__1),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_addRemote___closed__1_once),
        _init_l_Lake_GitRepo_addRemote___closed__1,
    );
    v___x_1943_ = lean_array_push(v___x_1942_, v_remote_1937_);
    v___x_1944_ = lean_array_push(v___x_1943_, v_url_1938_);
    v___x_1945_ = l_Lake_GitRepo_captureGit___closed__0;
    v___x_1946_ = l_Lake_Git_filterUrl_x3f___closed__2;
    v___x_1947_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1947_, 0, v_repo_1939_);
    v___x_1948_ = l_Lake_GitRepo_captureGit___closed__1;
    v___x_1949_ = 1;
    v___x_1950_ = 0;
    v___x_1951_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_1951_, 0, v___x_1945_);
    lean_ctor_set(v___x_1951_, 1, v___x_1946_);
    lean_ctor_set(v___x_1951_, 2, v___x_1944_);
    lean_ctor_set(v___x_1951_, 3, v___x_1947_);
    lean_ctor_set(v___x_1951_, 4, v___x_1948_);
    lean_ctor_set_uint8(
        v___x_1951_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_1949_,
    );
    lean_ctor_set_uint8(
        v___x_1951_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_1950_,
    );
    v___x_1952_ = l_Lake_proc(v___x_1951_, v___x_1949_, v_a_1940_);
    return v___x_1952_;
}
pub unsafe fn l_Lake_GitRepo_addRemote___boxed(
    mut v_remote_1953_: *mut LeanObject,
    mut v_url_1954_: *mut LeanObject,
    mut v_repo_1955_: *mut LeanObject,
    mut v_a_1956_: *mut LeanObject,
    mut v_a_1957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1958_: *mut LeanObject = core::ptr::null_mut();
    v_res_1958_ = l_Lake_GitRepo_addRemote(v_remote_1953_, v_url_1954_, v_repo_1955_, v_a_1956_);
    return v_res_1958_;
}
pub unsafe fn _init_l_Lake_GitRepo_setRemoteUrl___closed__1() -> *mut LeanObject {
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    v___x_1960_ = l_Lake_GitRepo_setRemoteUrl___closed__0;
    v___x_1961_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_addRemote___closed__0),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_addRemote___closed__0_once),
        _init_l_Lake_GitRepo_addRemote___closed__0,
    );
    v___x_1962_ = lean_array_push(v___x_1961_, v___x_1960_);
    return v___x_1962_;
}
pub unsafe fn l_Lake_GitRepo_setRemoteUrl(
    mut v_remote_1963_: *mut LeanObject,
    mut v_url_1964_: *mut LeanObject,
    mut v_repo_1965_: *mut LeanObject,
    mut v_a_1966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: u8 = 0;
    let mut v___x_1976_: u8 = 0;
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    v___x_1968_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_GitRepo_setRemoteUrl___closed__1),
        core::ptr::addr_of_mut!(l_Lake_GitRepo_setRemoteUrl___closed__1_once),
        _init_l_Lake_GitRepo_setRemoteUrl___closed__1,
    );
    v___x_1969_ = lean_array_push(v___x_1968_, v_remote_1963_);
    v___x_1970_ = lean_array_push(v___x_1969_, v_url_1964_);
    v___x_1971_ = l_Lake_GitRepo_captureGit___closed__0;
    v___x_1972_ = l_Lake_Git_filterUrl_x3f___closed__2;
    v___x_1973_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1973_, 0, v_repo_1965_);
    v___x_1974_ = l_Lake_GitRepo_captureGit___closed__1;
    v___x_1975_ = 1;
    v___x_1976_ = 0;
    v___x_1977_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_1977_, 0, v___x_1971_);
    lean_ctor_set(v___x_1977_, 1, v___x_1972_);
    lean_ctor_set(v___x_1977_, 2, v___x_1970_);
    lean_ctor_set(v___x_1977_, 3, v___x_1973_);
    lean_ctor_set(v___x_1977_, 4, v___x_1974_);
    lean_ctor_set_uint8(
        v___x_1977_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_1975_,
    );
    lean_ctor_set_uint8(
        v___x_1977_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_1976_,
    );
    v___x_1978_ = l_Lake_proc(v___x_1977_, v___x_1975_, v_a_1966_);
    return v___x_1978_;
}
pub unsafe fn l_Lake_GitRepo_setRemoteUrl___boxed(
    mut v_remote_1979_: *mut LeanObject,
    mut v_url_1980_: *mut LeanObject,
    mut v_repo_1981_: *mut LeanObject,
    mut v_a_1982_: *mut LeanObject,
    mut v_a_1983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1984_: *mut LeanObject = core::ptr::null_mut();
    v_res_1984_ = l_Lake_GitRepo_setRemoteUrl(v_remote_1979_, v_url_1980_, v_repo_1981_, v_a_1982_);
    return v_res_1984_;
}
pub unsafe fn l_Lake_GitRepo_getFilteredRemoteUrl_x3f(
    mut v_remote_1985_: *mut LeanObject,
    mut v_repo_1986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    v___x_1988_ = l_Lake_GitRepo_getRemoteUrl_x3f(v_remote_1985_, v_repo_1986_);
    if lean_obj_tag(v___x_1988_) == 0 {
        return v___x_1988_;
    } else {
        let mut v_val_1989_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
        v_val_1989_ = lean_ctor_get(v___x_1988_, 0);
        lean_inc(v_val_1989_);
        lean_dec_ref_known(v___x_1988_, 1);
        v___x_1990_ = l_Lake_Git_filterUrl_x3f(v_val_1989_);
        return v___x_1990_;
    }
}
pub unsafe fn l_Lake_GitRepo_getFilteredRemoteUrl_x3f___boxed(
    mut v_remote_1991_: *mut LeanObject,
    mut v_repo_1992_: *mut LeanObject,
    mut v_a_1993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1994_: *mut LeanObject = core::ptr::null_mut();
    v_res_1994_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v_remote_1991_, v_repo_1992_);
    return v_res_1994_;
}
pub unsafe fn l_Lake_GitRepo_hasNoDiff(mut v_repo_2005_: *mut LeanObject) -> u8 {
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: u8 = 0;
    let mut v___x_2013_: u8 = 0;
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: u8 = 0;
    v___x_2007_ = l_Lake_GitRepo_hasNoDiff___closed__2;
    v___x_2008_ = l_Lake_GitRepo_captureGit___closed__0;
    v___x_2009_ = l_Lake_Git_filterUrl_x3f___closed__2;
    v___x_2010_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2010_, 0, v_repo_2005_);
    v___x_2011_ = l_Lake_GitRepo_captureGit___closed__1;
    v___x_2012_ = 1;
    v___x_2013_ = 0;
    v___x_2014_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_2014_, 0, v___x_2008_);
    lean_ctor_set(v___x_2014_, 1, v___x_2009_);
    lean_ctor_set(v___x_2014_, 2, v___x_2007_);
    lean_ctor_set(v___x_2014_, 3, v___x_2010_);
    lean_ctor_set(v___x_2014_, 4, v___x_2011_);
    lean_ctor_set_uint8(
        v___x_2014_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_2012_,
    );
    lean_ctor_set_uint8(
        v___x_2014_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_2013_,
    );
    v___x_2015_ = l_Lake_testProc(v___x_2014_);
    return v___x_2015_;
}
pub unsafe fn l_Lake_GitRepo_hasNoDiff___boxed(
    mut v_repo_2016_: *mut LeanObject,
    mut v_a_2017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2018_: u8 = 0;
    let mut v_r_2019_: *mut LeanObject = core::ptr::null_mut();
    v_res_2018_ = l_Lake_GitRepo_hasNoDiff(v_repo_2016_);
    v_r_2019_ = lean_box((v_res_2018_) as usize);
    return v_r_2019_;
}
pub unsafe fn l_Lake_GitRepo_hasDiff(mut v_repo_2020_: *mut LeanObject) -> u8 {
    let mut v___x_2022_: u8 = 0;
    v___x_2022_ = l_Lake_GitRepo_hasNoDiff(v_repo_2020_);
    if v___x_2022_ == 0 {
        let mut v___x_2023_: u8 = 0;
        v___x_2023_ = 1;
        return v___x_2023_;
    } else {
        let mut v___x_2024_: u8 = 0;
        v___x_2024_ = 0;
        return v___x_2024_;
    }
}
pub unsafe fn l_Lake_GitRepo_hasDiff___boxed(
    mut v_repo_2025_: *mut LeanObject,
    mut v_a_2026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2027_: u8 = 0;
    let mut v_r_2028_: *mut LeanObject = core::ptr::null_mut();
    v_res_2027_ = l_Lake_GitRepo_hasDiff(v_repo_2025_);
    v_r_2028_ = lean_box((v_res_2027_) as usize);
    return v_r_2028_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Git(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Proc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Git(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Git(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Proc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Git(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Git(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Util_Git(builtin);
}
