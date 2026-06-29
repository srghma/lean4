// Lean compiler output
// Module: Leanc
// Imports: Init Init Lean.Compiler.FFI
use crate::r#gen::Init::Data::Array::Basic::{
    l_Array_append___redArg, l_Array_eraseIdx___redArg,
    l_List_foldl___at___00Array_appendList_spec__0___redArg,
};
use crate::r#gen::Init::Data::List::Basic::l_List_isEmpty___redArg;
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_Pos_get_x3f;
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Prelude::l_Char_utf8Size;
use crate::r#gen::Init::System::FilePath::{
    l_System_FilePath_fileStem, l_System_FilePath_parent, l_System_FilePath_withExtension,
};
use crate::r#gen::Init::System::IO::{
    l_IO_appDir, l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0,
    l_System_FilePath_pathExists,
};
use crate::r#gen::Init::System::Platform::l_System_Platform_isWindows;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::initialize_Init;
use crate::r#gen::Lean::Compiler::FFI::{
    initialize_Lean_Compiler_FFI, l_Lean_Compiler_FFI_getCFlags,
    l_Lean_Compiler_FFI_getInternalCFlags, l_Lean_Compiler_FFI_getInternalLinkerFlags,
    l_Lean_Compiler_FFI_getLinkerFlags,
    l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_utf8_get_fast;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Modify::lean_string_utf8_set;
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_mk, lean_array_push,
    lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_string_dec_eq,
    lean_string_utf8_byte_size, lean_uint32_dec_eq, lean_uint32_dec_le, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::{
    lean_get_stdout, lean_io_getenv, lean_io_process_child_wait, lean_io_process_spawn,
};
pub static l_panic___at___00main_spec__9___closed__0_value: crate::leanh::LeanStringObject<1> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 1,
        m_capacity: 1,
        m_length: 0,
        m_data: [0],
    };
static mut l_panic___at___00main_spec__9___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00main_spec__9___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__5___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [46, 114, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__5___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [47, 108, 105, 98, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [46, 114, 108, 105, 98, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__2_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [45, 45, 101, 120, 116, 101, 114, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__3_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [61, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [45, 45, 112, 114, 105, 110, 116, 45, 99, 102, 108, 97, 103, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [45, 45, 112, 114, 105, 110, 116, 45, 108, 100, 102, 108, 97, 103, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__2_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__3_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__3_value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__4___boxed__const__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [51, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [45, 79, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [45, 103, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [45, 79, 51, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__4_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [45, 79, 50, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__5_value: crate::leanh::LeanArrayObject<1> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 246 }, m_size: 1, m_capacity: 1, m_data: [core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [45, 111, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_main___closed__0_value: crate::leanh::LeanCtorObject<1> =
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
static mut l_main___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__1_value: crate::leanh::LeanStringObject<3> =
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
static mut l_main___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__2_value: crate::leanh::LeanStringObject<34> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            45, 87, 110, 111, 45, 117, 110, 117, 115, 101, 100, 45, 99, 111, 109, 109, 97, 110,
            100, 45, 108, 105, 110, 101, 45, 97, 114, 103, 117, 109, 101, 110, 116, 0,
        ],
    };
static mut l_main___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_main___closed__2_value) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_main___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__4_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [76, 69, 65, 78, 95, 67, 67, 0],
    };
static mut l_main___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__5_value: crate::leanh::LeanStringObject<20> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            45, 87, 108, 44, 45, 45, 119, 104, 111, 108, 101, 45, 97, 114, 99, 104, 105, 118, 101,
            0,
        ],
    };
static mut l_main___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__6_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
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
            45, 108, 108, 101, 97, 110, 109, 97, 110, 105, 102, 101, 115, 116, 0,
        ],
    };
static mut l_main___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__7_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
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
            45, 87, 108, 44, 45, 45, 110, 111, 45, 119, 104, 111, 108, 101, 45, 97, 114, 99, 104,
            105, 118, 101, 0,
        ],
    };
static mut l_main___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__8_value: crate::leanh::LeanArrayObject<3> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 3,
        m_capacity: 3,
        m_data: [
            core::ptr::addr_of!(l_main___closed__5_value) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_main___closed__6_value) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_main___closed__7_value) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_main___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__9_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [114, 117, 115, 116, 99, 0],
    };
static mut l_main___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__10_value: crate::leanh::LeanStringObject<13> =
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
        m_data: [76, 69, 65, 78, 95, 83, 89, 83, 82, 79, 79, 84, 0],
    };
static mut l_main___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__11_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [45, 108, 101, 97, 110, 115, 104, 97, 114, 101, 100, 0],
    };
static mut l_main___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__12_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [45, 115, 104, 97, 114, 101, 100, 0],
    };
static mut l_main___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__13_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [64, 76, 69, 65, 78, 67, 95, 67, 67, 64, 0],
    };
static mut l_main___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__13_value) as *mut crate::leanh::LeanObject;
static mut l_main___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_main___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_main___closed__15_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            77, 65, 67, 79, 83, 88, 95, 68, 69, 80, 76, 79, 89, 77, 69, 78, 84, 95, 84, 65, 82, 71,
            69, 84, 0,
        ],
    };
static mut l_main___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__16_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [57, 57, 46, 48, 0],
    };
static mut l_main___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__17_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [core::ptr::addr_of!(l_main___closed__16_value) as *mut crate::leanh::LeanObject],
    };
static mut l_main___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__18_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_main___closed__15_value) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_main___closed__17_value) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_main___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__19_value: crate::leanh::LeanArrayObject<1> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 1,
        m_capacity: 1,
        m_data: [core::ptr::addr_of!(l_main___closed__18_value) as *mut crate::leanh::LeanObject],
    };
static mut l_main___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__20_value: crate::leanh::LeanStringObject<91> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 91,
        m_capacity: 91,
        m_length: 90,
        m_data: [
            76, 101, 97, 110, 32, 99, 111, 109, 112, 105, 108, 101, 114, 32, 119, 114, 97, 112,
            112, 101, 114, 10, 10, 65, 32, 115, 105, 109, 112, 108, 101, 32, 119, 114, 97, 112,
            112, 101, 114, 32, 97, 114, 111, 117, 110, 100, 32, 97, 32, 99, 111, 109, 112, 105,
            108, 101, 114, 32, 40, 114, 117, 115, 116, 99, 32, 111, 114, 32, 108, 105, 110, 107,
            101, 114, 41, 46, 32, 68, 101, 102, 97, 117, 108, 116, 115, 32, 116, 111, 32, 96, 0,
        ],
    };
static mut l_main___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__21_value: crate::leanh::LeanStringObject<354> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 354,
        m_capacity: 354,
        m_length: 353,
        m_data: [
            96, 44, 10, 119, 104, 105, 99, 104, 32, 99, 97, 110, 32, 98, 101, 32, 111, 118, 101,
            114, 114, 105, 100, 100, 101, 110, 32, 119, 105, 116, 104, 32, 116, 104, 101, 32, 101,
            110, 118, 105, 114, 111, 110, 109, 101, 110, 116, 32, 118, 97, 114, 105, 97, 98, 108,
            101, 32, 96, 76, 69, 65, 78, 95, 67, 67, 96, 46, 32, 65, 108, 108, 32, 112, 97, 114,
            97, 109, 101, 116, 101, 114, 115, 32, 97, 114, 101, 32, 112, 97, 115, 115, 101, 100,
            10, 97, 115, 45, 105, 115, 32, 116, 111, 32, 116, 104, 101, 32, 119, 114, 97, 112, 112,
            101, 100, 32, 99, 111, 109, 112, 105, 108, 101, 114, 46, 10, 10, 73, 110, 116, 101,
            114, 101, 115, 116, 105, 110, 103, 32, 111, 112, 116, 105, 111, 110, 115, 58, 10, 42,
            32, 96, 45, 45, 112, 114, 105, 110, 116, 45, 99, 102, 108, 97, 103, 115, 96, 58, 32,
            112, 114, 105, 110, 116, 32, 99, 111, 109, 112, 105, 108, 101, 114, 32, 102, 108, 97,
            103, 115, 32, 110, 101, 99, 101, 115, 115, 97, 114, 121, 32, 102, 111, 114, 32, 98,
            117, 105, 108, 100, 105, 110, 103, 32, 97, 103, 97, 105, 110, 115, 116, 32, 116, 104,
            101, 32, 76, 101, 97, 110, 32, 114, 117, 110, 116, 105, 109, 101, 32, 97, 110, 100, 32,
            101, 120, 105, 116, 10, 42, 32, 96, 45, 45, 112, 114, 105, 110, 116, 45, 108, 100, 102,
            108, 97, 103, 115, 96, 58, 32, 112, 114, 105, 110, 116, 32, 99, 111, 109, 112, 105,
            108, 101, 114, 32, 102, 108, 97, 103, 115, 32, 110, 101, 99, 101, 115, 115, 97, 114,
            121, 32, 102, 111, 114, 32, 115, 116, 97, 116, 105, 99, 97, 108, 108, 121, 32, 108,
            105, 110, 107, 105, 110, 103, 32, 97, 103, 97, 105, 110, 115, 116, 32, 116, 104, 101,
            32, 76, 101, 97, 110, 32, 108, 105, 98, 114, 97, 114, 121, 32, 97, 110, 100, 32, 101,
            120, 105, 116, 0,
        ],
    };
static mut l_main___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__22_value: crate::leanh::LeanStringObject<14> =
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
        m_data: [45, 45, 99, 114, 97, 116, 101, 45, 116, 121, 112, 101, 61, 0],
    };
static mut l_main___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__23_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [45, 45, 101, 109, 105, 116, 61, 108, 105, 110, 107, 0],
    };
static mut l_main___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__24_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
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
            45, 45, 101, 100, 105, 116, 105, 111, 110, 61, 50, 48, 50, 49, 0,
        ],
    };
static mut l_main___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__25_value: crate::leanh::LeanStringObject<14> =
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
        m_data: [45, 45, 99, 114, 97, 116, 101, 45, 110, 97, 109, 101, 61, 0],
    };
static mut l_main___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__26_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [45, 67, 0],
    };
static mut l_main___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__27_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [111, 112, 116, 45, 108, 101, 118, 101, 108, 61, 0],
    };
static mut l_main___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__28_value: crate::leanh::LeanStringObject<20> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            100, 101, 98, 117, 103, 45, 97, 115, 115, 101, 114, 116, 105, 111, 110, 115, 61, 110,
            111, 0,
        ],
    };
static mut l_main___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__29_value: crate::leanh::LeanStringObject<14> =
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
            108, 101, 97, 110, 95, 114, 117, 110, 116, 105, 109, 101, 61, 0,
        ],
    };
static mut l_main___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__30_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [45, 76, 0],
    };
static mut l_main___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__30_value) as *mut crate::leanh::LeanObject;
static mut l_main___closed__31_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_main___closed__31: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_main___closed__32_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [114, 117, 115, 116, 99, 32, 0],
    };
static mut l_main___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__32_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__33_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [108, 101, 97, 110, 95, 105, 110, 105, 116, 0],
    };
static mut l_main___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__33_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__34_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [108, 101, 97, 110, 95, 115, 116, 100, 0],
    };
static mut l_main___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__34_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__35_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [108, 101, 97, 110, 95, 108, 101, 97, 110, 0],
    };
static mut l_main___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__35_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__36_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [108, 101, 97, 110, 95, 108, 97, 107, 101, 0],
    };
static mut l_main___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__36_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__37_value: crate::leanh::LeanArrayObject<4> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 4,
        m_capacity: 4,
        m_data: [
            core::ptr::addr_of!(l_main___closed__33_value) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_main___closed__34_value) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_main___closed__35_value) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_main___closed__36_value) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_main___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__37_value) as *mut crate::leanh::LeanObject;
static mut l_main___closed__38_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_main___closed__38: usize = 0;
pub static l_main___closed__39_value: crate::leanh::LeanStringObject<33> =
    crate::leanh::LeanStringObject {
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
            47, 108, 101, 97, 110, 95, 115, 116, 100, 108, 105, 98, 47, 116, 97, 114, 103, 101,
            116, 47, 114, 101, 108, 101, 97, 115, 101, 47, 100, 101, 112, 115, 0,
        ],
    };
static mut l_main___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__39_value) as *mut crate::leanh::LeanObject;
static mut l_main___closed__40_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_main___closed__40: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_main___closed__41_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [95, 0],
    };
static mut l_main___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__41_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__42_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [109, 111, 100, 117, 108, 101, 0],
    };
static mut l_main___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__42_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__43_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [47, 108, 105, 98, 47, 108, 101, 97, 110, 0],
    };
static mut l_main___closed__43: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__43_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__44_value: crate::leanh::LeanStringObject<33> =
    crate::leanh::LeanStringObject {
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
            47, 108, 105, 98, 108, 101, 97, 110, 95, 114, 117, 110, 116, 105, 109, 101, 95, 102,
            114, 111, 109, 95, 99, 97, 114, 103, 111, 46, 114, 108, 105, 98, 0,
        ],
    };
static mut l_main___closed__44: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__44_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__45_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            47, 108, 105, 98, 108, 101, 97, 110, 95, 114, 117, 110, 116, 105, 109, 101, 46, 114,
            108, 105, 98, 0,
        ],
    };
static mut l_main___closed__45: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__45_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__46_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [114, 108, 105, 98, 0],
    };
static mut l_main___closed__46: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__46_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__47_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [108, 105, 98, 0],
    };
static mut l_main___closed__47: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__47_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__48_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [48, 0],
    };
static mut l_main___closed__48: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__48_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__49_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_main___closed__49: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__49_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__50_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [45, 99, 0],
    };
static mut l_main___closed__50: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__50_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__51_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [98, 105, 110, 0],
    };
static mut l_main___closed__51: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__51_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__52_value: crate::leanh::LeanStringObject<68> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 68,
        m_capacity: 68,
        m_length: 67,
        m_data: [
            108, 101, 97, 110, 99, 58, 32, 115, 104, 97, 114, 101, 100, 32, 108, 105, 98, 114, 97,
            114, 105, 101, 115, 32, 97, 114, 101, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111,
            114, 116, 101, 100, 32, 105, 110, 32, 116, 104, 101, 32, 82, 117, 115, 116, 47, 67, 97,
            114, 103, 111, 32, 98, 97, 99, 107, 101, 110, 100, 0,
        ],
    };
static mut l_main___closed__52: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__52_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__53_value: crate::leanh::LeanStringObject<27> =
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
            108, 101, 97, 110, 99, 58, 32, 110, 111, 32, 105, 110, 112, 117, 116, 32, 114, 117,
            115, 116, 32, 102, 105, 108, 101, 115, 0,
        ],
    };
static mut l_main___closed__53: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__53_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__54_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97,
            115, 105, 99, 65, 117, 120, 0,
        ],
    };
static mut l_main___closed__54: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__54_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__55_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0],
    };
static mut l_main___closed__55: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__55_value) as *mut crate::leanh::LeanObject;
pub static l_main___closed__56_value: crate::leanh::LeanStringObject<14> =
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
            118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0,
        ],
    };
static mut l_main___closed__56: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_main___closed__56_value) as *mut crate::leanh::LeanObject;
static mut l_main___closed__57_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_main___closed__57: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_main___boxed__const__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_panic___at___00main_spec__9(
    mut v_msg_1122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1123_ = l_panic___at___00main_spec__9___closed__0;
    v___x_1124_ = lean_panic_fn_borrowed(v___x_1123_, v_msg_1122_);
    return v___x_1124_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__5___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1126_ =
        l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__5___closed__0;
    v___x_1127_ = lean_string_utf8_byte_size(v___x_1126_);
    return v___x_1127_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__5(
    mut v_as_1128_: *mut crate::leanh::LeanObject,
    mut v_i_1129_: usize,
    mut v_stop_1130_: usize,
) -> u8 {
    let mut v___x_1131_: u8 = 0;
    let mut v___x_1132_: u8 = 0;
    let mut v___y_1134_: u8 = 0;
    let mut v___x_1135_: usize = 0;
    let mut v___x_1136_: usize = 0;
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: u8 = 0;
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: u8 = 0;
    let mut v___x_1146_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1131_ = lean_usize_dec_eq(v_i_1129_, v_stop_1130_);
                if v___x_1131_ == 0 {
                    v___x_1132_ = 1;
                    v___x_1138_ = lean_array_uget_borrowed(v_as_1128_, v_i_1129_);
                    v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__5___closed__0;
                    v___x_1140_ = lean_string_utf8_byte_size(v___x_1138_);
                    v___x_1141_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__5___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__5___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__5___closed__1);
                    v___x_1142_ = lean_nat_dec_le(v___x_1141_, v___x_1140_);
                    if v___x_1142_ == 0 {
                        v___y_1134_ = v___x_1131_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1143_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1144_ = lean_nat_sub(v___x_1140_, v___x_1141_);
                        v___x_1145_ = lean_string_memcmp(
                            v___x_1138_,
                            v___x_1139_,
                            v___x_1144_,
                            v___x_1143_,
                            v___x_1141_,
                        );
                        crate::leanh::lean_dec(v___x_1144_);
                        v___y_1134_ = v___x_1145_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1146_ = 0;
                    return v___x_1146_;
                }
            }
            1 => {
                if v___y_1134_ == 0 {
                    v___x_1135_ = 1usize;
                    v___x_1136_ = lean_usize_add(v_i_1129_, v___x_1135_);
                    v_i_1129_ = v___x_1136_;
                    state = 0;
                    continue;
                } else {
                    return v___x_1132_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__5___boxed(
    mut v_as_1147_: *mut crate::leanh::LeanObject,
    mut v_i_1148_: *mut crate::leanh::LeanObject,
    mut v_stop_1149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1150_: usize = 0;
    let mut v_stop_boxed_1151_: usize = 0;
    let mut v_res_1152_: u8 = 0;
    let mut v_r_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1150_ = crate::leanh::lean_unbox_usize(v_i_1148_);
    crate::leanh::lean_dec(v_i_1148_);
    v_stop_boxed_1151_ = crate::leanh::lean_unbox_usize(v_stop_1149_);
    crate::leanh::lean_dec(v_stop_1149_);
    v_res_1152_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__5(
        v_as_1147_,
        v_i_boxed_1150_,
        v_stop_boxed_1151_,
    );
    crate::leanh::lean_dec_ref(v_as_1147_);
    v_r_1153_ = crate::leanh::lean_box((v_res_1152_) as usize);
    return v_r_1153_;
}
pub unsafe fn l_String_mapAux___at___00main_spec__8(
    mut v_s_1154_: *mut crate::leanh::LeanObject,
    mut v_p_1155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1157_: u32 = 0;
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: u8 = 0;
    let mut v___x_1164_: u32 = 0;
    let mut v___y_1166_: u8 = 0;
    let mut v___x_1167_: u32 = 0;
    let mut v___x_1168_: u8 = 0;
    let mut v___y_1170_: u8 = 0;
    let mut v___x_1171_: u32 = 0;
    let mut v___x_1172_: u8 = 0;
    let mut v___x_1173_: u32 = 0;
    let mut v___x_1174_: u8 = 0;
    let mut v___x_1176_: u32 = 0;
    let mut v___x_1177_: u8 = 0;
    let mut v___x_1178_: u32 = 0;
    let mut v___x_1179_: u8 = 0;
    let mut v___x_1180_: u32 = 0;
    let mut v___x_1181_: u8 = 0;
    let mut v___x_1182_: u32 = 0;
    let mut v___x_1183_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1162_ = lean_string_utf8_byte_size(v_s_1154_);
                v___x_1163_ = lean_nat_dec_eq(v_p_1155_, v___x_1162_);
                if v___x_1163_ == 0 {
                    v___x_1164_ = lean_string_utf8_get_fast(v_s_1154_, v_p_1155_);
                    v___x_1180_ = 65;
                    v___x_1181_ = lean_uint32_dec_le(v___x_1180_, v___x_1164_);
                    if v___x_1181_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        v___x_1182_ = 90;
                        v___x_1183_ = lean_uint32_dec_le(v___x_1164_, v___x_1182_);
                        if v___x_1183_ == 0 {
                            state = 4;
                            continue;
                        } else {
                            v___y_1157_ = v___x_1164_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_p_1155_);
                    return v_s_1154_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_p_1155_);
                v___x_1158_ = lean_string_utf8_set(v_s_1154_, v_p_1155_, v___y_1157_);
                v___x_1159_ = l_Char_utf8Size(v___y_1157_);
                v___x_1160_ = lean_nat_add(v_p_1155_, v___x_1159_);
                crate::leanh::lean_dec(v___x_1159_);
                crate::leanh::lean_dec(v_p_1155_);
                v_s_1154_ = v___x_1158_;
                v_p_1155_ = v___x_1160_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_1166_ == 0 {
                    v___x_1167_ = 95;
                    v___x_1168_ = lean_uint32_dec_eq(v___x_1164_, v___x_1167_);
                    if v___x_1168_ == 0 {
                        v___y_1157_ = v___x_1167_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1157_ = v___x_1164_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___y_1157_ = v___x_1164_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_1170_ == 0 {
                    v___x_1171_ = 48;
                    v___x_1172_ = lean_uint32_dec_le(v___x_1171_, v___x_1164_);
                    if v___x_1172_ == 0 {
                        v___y_1166_ = v___x_1172_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1173_ = 57;
                        v___x_1174_ = lean_uint32_dec_le(v___x_1164_, v___x_1173_);
                        v___y_1166_ = v___x_1174_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___y_1157_ = v___x_1164_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                v___x_1176_ = 97;
                v___x_1177_ = lean_uint32_dec_le(v___x_1176_, v___x_1164_);
                if v___x_1177_ == 0 {
                    v___y_1170_ = v___x_1177_;
                    state = 3;
                    continue;
                } else {
                    v___x_1178_ = 122;
                    v___x_1179_ = lean_uint32_dec_le(v___x_1164_, v___x_1178_);
                    v___y_1170_ = v___x_1179_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00main_spec__1_spec__2(
    mut v_a_1184_: *mut crate::leanh::LeanObject,
    mut v_as_1185_: *mut crate::leanh::LeanObject,
    mut v_i_1186_: usize,
    mut v_stop_1187_: usize,
) -> u8 {
    let mut v___x_1188_: u8 = 0;
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: u8 = 0;
    let mut v___x_1191_: usize = 0;
    let mut v___x_1192_: usize = 0;
    let mut v___x_1194_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1188_ = lean_usize_dec_eq(v_i_1186_, v_stop_1187_);
                if v___x_1188_ == 0 {
                    v___x_1189_ = lean_array_uget_borrowed(v_as_1185_, v_i_1186_);
                    v___x_1190_ = lean_string_dec_eq(v_a_1184_, v___x_1189_);
                    if v___x_1190_ == 0 {
                        v___x_1191_ = 1usize;
                        v___x_1192_ = lean_usize_add(v_i_1186_, v___x_1191_);
                        v_i_1186_ = v___x_1192_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1190_;
                    }
                } else {
                    v___x_1194_ = 0;
                    return v___x_1194_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00main_spec__1_spec__2___boxed(
    mut v_a_1195_: *mut crate::leanh::LeanObject,
    mut v_as_1196_: *mut crate::leanh::LeanObject,
    mut v_i_1197_: *mut crate::leanh::LeanObject,
    mut v_stop_1198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1199_: usize = 0;
    let mut v_stop_boxed_1200_: usize = 0;
    let mut v_res_1201_: u8 = 0;
    let mut v_r_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1199_ = crate::leanh::lean_unbox_usize(v_i_1197_);
    crate::leanh::lean_dec(v_i_1197_);
    v_stop_boxed_1200_ = crate::leanh::lean_unbox_usize(v_stop_1198_);
    crate::leanh::lean_dec(v_stop_1198_);
    v_res_1201_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00main_spec__1_spec__2(v_a_1195_, v_as_1196_, v_i_boxed_1199_, v_stop_boxed_1200_);
    crate::leanh::lean_dec_ref(v_as_1196_);
    crate::leanh::lean_dec_ref(v_a_1195_);
    v_r_1202_ = crate::leanh::lean_box((v_res_1201_) as usize);
    return v_r_1202_;
}
pub unsafe fn l_Array_contains___at___00main_spec__1(
    mut v_as_1203_: *mut crate::leanh::LeanObject,
    mut v_a_1204_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: u8 = 0;
    v___x_1205_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1206_ = lean_array_get_size(v_as_1203_);
    v___x_1207_ = lean_nat_dec_lt(v___x_1205_, v___x_1206_);
    if v___x_1207_ == 0 {
        return v___x_1207_;
    } else {
        if v___x_1207_ == 0 {
            return v___x_1207_;
        } else {
            let mut v___x_1208_: usize = 0;
            let mut v___x_1209_: usize = 0;
            let mut v___x_1210_: u8 = 0;
            v___x_1208_ = 0usize;
            v___x_1209_ = lean_usize_of_nat(v___x_1206_);
            v___x_1210_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00main_spec__1_spec__2(v_a_1204_, v_as_1203_, v___x_1208_, v___x_1209_);
            return v___x_1210_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00main_spec__1___boxed(
    mut v_as_1211_: *mut crate::leanh::LeanObject,
    mut v_a_1212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1213_: u8 = 0;
    let mut v_r_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1213_ = l_Array_contains___at___00main_spec__1(v_as_1211_, v_a_1212_);
    crate::leanh::lean_dec_ref(v_a_1212_);
    crate::leanh::lean_dec_ref(v_as_1211_);
    v_r_1214_ = crate::leanh::lean_box((v_res_1213_) as usize);
    return v_r_1214_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00main_spec__0_spec__0_spec__2(
    mut v_xs_1215_: *mut crate::leanh::LeanObject,
    mut v_v_1216_: *mut crate::leanh::LeanObject,
    mut v_i_1217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: u8 = 0;
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: u8 = 0;
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1218_ = lean_array_get_size(v_xs_1215_);
                v___x_1219_ = lean_nat_dec_lt(v_i_1217_, v___x_1218_);
                if v___x_1219_ == 0 {
                    crate::leanh::lean_dec(v_i_1217_);
                    v___x_1220_ = crate::leanh::lean_box(0);
                    return v___x_1220_;
                } else {
                    v___x_1221_ = lean_array_fget_borrowed(v_xs_1215_, v_i_1217_);
                    v___x_1222_ = lean_string_dec_eq(v___x_1221_, v_v_1216_);
                    if v___x_1222_ == 0 {
                        v___x_1223_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1224_ = lean_nat_add(v_i_1217_, v___x_1223_);
                        crate::leanh::lean_dec(v_i_1217_);
                        v_i_1217_ = v___x_1224_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1226_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1226_, 0, v_i_1217_);
                        return v___x_1226_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00main_spec__0_spec__0_spec__2___boxed(
    mut v_xs_1227_: *mut crate::leanh::LeanObject,
    mut v_v_1228_: *mut crate::leanh::LeanObject,
    mut v_i_1229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1230_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00main_spec__0_spec__0_spec__2(v_xs_1227_, v_v_1228_, v_i_1229_);
    crate::leanh::lean_dec_ref(v_v_1228_);
    crate::leanh::lean_dec_ref(v_xs_1227_);
    return v_res_1230_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_erase___at___00main_spec__0_spec__0(
    mut v_xs_1231_: *mut crate::leanh::LeanObject,
    mut v_v_1232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1233_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1234_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00main_spec__0_spec__0_spec__2(v_xs_1231_, v_v_1232_, v___x_1233_);
    return v___x_1234_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_erase___at___00main_spec__0_spec__0___boxed(
    mut v_xs_1235_: *mut crate::leanh::LeanObject,
    mut v_v_1236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1237_ = l_Array_finIdxOf_x3f___at___00Array_erase___at___00main_spec__0_spec__0(
        v_xs_1235_, v_v_1236_,
    );
    crate::leanh::lean_dec_ref(v_v_1236_);
    crate::leanh::lean_dec_ref(v_xs_1235_);
    return v_res_1237_;
}
pub unsafe fn l_Array_erase___at___00main_spec__0(
    mut v_as_1238_: *mut crate::leanh::LeanObject,
    mut v_a_1239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1240_ = l_Array_finIdxOf_x3f___at___00Array_erase___at___00main_spec__0_spec__0(
        v_as_1238_, v_a_1239_,
    );
    if crate::leanh::lean_obj_tag(v___x_1240_) == 0 {
        return v_as_1238_;
    } else {
        let mut v_val_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1241_ = crate::leanh::lean_ctor_get(v___x_1240_, 0);
        crate::leanh::lean_inc(v_val_1241_);
        crate::leanh::lean_dec_ref_known(v___x_1240_, 1);
        v___x_1242_ = l_Array_eraseIdx___redArg(v_as_1238_, v_val_1241_);
        return v___x_1242_;
    }
}
pub unsafe fn l_Array_erase___at___00main_spec__0___boxed(
    mut v_as_1243_: *mut crate::leanh::LeanObject,
    mut v_a_1244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1245_ = l_Array_erase___at___00main_spec__0(v_as_1243_, v_a_1244_);
    crate::leanh::lean_dec_ref(v_a_1244_);
    return v_res_1245_;
}
pub unsafe fn l_IO_print___at___00IO_println___at___00main_spec__3_spec__5(
    mut v_s_1246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1248_ = lean_get_stdout();
    v_putStr_1249_ = crate::leanh::lean_ctor_get(v___x_1248_, 4);
    crate::leanh::lean_inc_ref(v_putStr_1249_);
    crate::leanh::lean_dec_ref(v___x_1248_);
    v___x_1250_ = crate::leanh::lean_apply_2(v_putStr_1249_, v_s_1246_, crate::leanh::lean_box(0));
    return v___x_1250_;
}
pub unsafe fn l_IO_print___at___00IO_println___at___00main_spec__3_spec__5___boxed(
    mut v_s_1251_: *mut crate::leanh::LeanObject,
    mut v_a_1252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1253_ = l_IO_print___at___00IO_println___at___00main_spec__3_spec__5(v_s_1251_);
    return v_res_1253_;
}
pub unsafe fn l_IO_println___at___00main_spec__3(
    mut v_s_1254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1256_: u32 = 0;
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1256_ = 10;
    v___x_1257_ = lean_string_push(v_s_1254_, v___x_1256_);
    v___x_1258_ = l_IO_print___at___00IO_println___at___00main_spec__3_spec__5(v___x_1257_);
    return v___x_1258_;
}
pub unsafe fn l_IO_println___at___00main_spec__3___boxed(
    mut v_s_1259_: *mut crate::leanh::LeanObject,
    mut v_a_1260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1261_ = l_IO_println___at___00main_spec__3(v_s_1259_);
    return v_res_1261_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__2;
    v___x_1267_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1268_ = lean_mk_empty_array_with_capacity(v___x_1267_);
    v___x_1269_ = lean_array_push(v___x_1268_, v___x_1266_);
    return v___x_1269_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7(
    mut v___x_1270_: *mut crate::leanh::LeanObject,
    mut v_as_1271_: *mut crate::leanh::LeanObject,
    mut v_sz_1272_: usize,
    mut v_i_1273_: usize,
    mut v_b_1274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1276_: u8 = 0;
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: u8 = 0;
    let mut v_a_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: usize = 0;
    let mut v___x_1288_: usize = 0;
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1276_ = lean_usize_dec_lt(v_i_1273_, v_sz_1272_);
                if v___x_1276_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1270_);
                    v___x_1277_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1277_, 0, v_b_1274_);
                    return v___x_1277_;
                } else {
                    v_a_1278_ = lean_array_uget_borrowed(v_as_1271_, v_i_1273_);
                    v___x_1279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__0;
                    crate::leanh::lean_inc_ref(v___x_1270_);
                    v___x_1280_ = lean_string_append(v___x_1270_, v___x_1279_);
                    v___x_1281_ = lean_string_append(v___x_1280_, v_a_1278_);
                    v___x_1282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__1;
                    v___x_1283_ = lean_string_append(v___x_1281_, v___x_1282_);
                    v___x_1284_ = l_System_FilePath_pathExists(v___x_1283_);
                    if v___x_1284_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1283_);
                        v_a_1286_ = v_b_1274_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__3;
                        crate::leanh::lean_inc(v_a_1278_);
                        v___x_1291_ = lean_string_append(v_a_1278_, v___x_1290_);
                        v___x_1292_ = lean_string_append(v___x_1291_, v___x_1283_);
                        crate::leanh::lean_dec_ref(v___x_1283_);
                        v___x_1293_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__4);
                        v___x_1294_ = lean_array_push(v___x_1293_, v___x_1292_);
                        v___x_1295_ = l_Array_append___redArg(v_b_1274_, v___x_1294_);
                        crate::leanh::lean_dec_ref(v___x_1294_);
                        v_a_1286_ = v___x_1295_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1287_ = 1usize;
                v___x_1288_ = lean_usize_add(v_i_1273_, v___x_1287_);
                v_i_1273_ = v___x_1288_;
                v_b_1274_ = v_a_1286_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___boxed(
    mut v___x_1296_: *mut crate::leanh::LeanObject,
    mut v_as_1297_: *mut crate::leanh::LeanObject,
    mut v_sz_1298_: *mut crate::leanh::LeanObject,
    mut v_i_1299_: *mut crate::leanh::LeanObject,
    mut v_b_1300_: *mut crate::leanh::LeanObject,
    mut v___y_1301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1302_: usize = 0;
    let mut v_i_boxed_1303_: usize = 0;
    let mut v_res_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1302_ = crate::leanh::lean_unbox_usize(v_sz_1298_);
    crate::leanh::lean_dec(v_sz_1298_);
    v_i_boxed_1303_ = crate::leanh::lean_unbox_usize(v_i_1299_);
    crate::leanh::lean_dec(v_i_1299_);
    v_res_1304_ =
        l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7(
            v___x_1296_,
            v_as_1297_,
            v_sz_boxed_1302_,
            v_i_boxed_1303_,
            v_b_1300_,
        );
    crate::leanh::lean_dec_ref(v_as_1297_);
    return v_res_1304_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__4___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1311_: u32 = 0;
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1311_ = 0;
    v___x_1312_ = crate::leanh::lean_box_uint32(v___x_1311_);
    return v___x_1312_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__4___boxed__const__1;
    v___x_1314_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1314_, 0, v___x_1313_);
    return v___x_1314_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1315_ = crate::leanh::lean_box(0);
    v___x_1316_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__4);
    v___x_1317_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1317_, 0, v___x_1316_);
    crate::leanh::lean_ctor_set(v___x_1317_, 1, v___x_1315_);
    return v___x_1317_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4(
    mut v___x_1318_: *mut crate::leanh::LeanObject,
    mut v_ldflags_1319_: *mut crate::leanh::LeanObject,
    mut v_as_1320_: *mut crate::leanh::LeanObject,
    mut v_sz_1321_: usize,
    mut v_i_1322_: usize,
    mut v_b_1323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1325_: u8 = 0;
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: u8 = 0;
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: u8 = 0;
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: usize = 0;
    let mut v___x_1334_: usize = 0;
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1343_: u8 = 0;
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1348_: u8 = 0;
    let mut v_unused_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1353_: u8 = 0;
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1357_: u8 = 0;
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1364_: u8 = 0;
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1369_: u8 = 0;
    let mut v_unused_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1374_: u8 = 0;
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1325_ = lean_usize_dec_lt(v_i_1322_, v_sz_1321_);
                if v___x_1325_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1318_);
                    v___x_1326_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1326_, 0, v_b_1323_);
                    return v___x_1326_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_1323_);
                    v_a_1327_ = lean_array_uget_borrowed(v_as_1320_, v_i_1322_);
                    v___x_1328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__0;
                    v___x_1329_ = lean_string_dec_eq(v_a_1327_, v___x_1328_);
                    if v___x_1329_ == 0 {
                        v___x_1330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__1;
                        v___x_1331_ = lean_string_dec_eq(v_a_1327_, v___x_1330_);
                        if v___x_1331_ == 0 {
                            v___x_1332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__2;
                            v___x_1333_ = 1usize;
                            v___x_1334_ = lean_usize_add(v_i_1322_, v___x_1333_);
                            v_i_1322_ = v___x_1334_;
                            v_b_1323_ = v___x_1332_;
                            state = 0;
                            continue;
                        } else {
                            v___x_1336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__3;
                            v___x_1337_ = l_Array_append___redArg(v___x_1318_, v_ldflags_1319_);
                            v___x_1338_ = lean_array_to_list(v___x_1337_);
                            v___x_1339_ = l_String_intercalate(v___x_1336_, v___x_1338_);
                            v___x_1340_ = l_IO_println___at___00main_spec__3(v___x_1339_);
                            if crate::leanh::lean_obj_tag(v___x_1340_) == 0 {
                                v_isSharedCheck_1348_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1340_)) as u8;
                                if v_isSharedCheck_1348_ == 0 {
                                    v_unused_1349_ = crate::leanh::lean_ctor_get(v___x_1340_, 0);
                                    crate::leanh::lean_dec(v_unused_1349_);
                                    v___x_1342_ = v___x_1340_;
                                    v_isShared_1343_ = v_isSharedCheck_1348_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_1340_);
                                    v___x_1342_ = crate::leanh::lean_box(0);
                                    v_isShared_1343_ = v_isSharedCheck_1348_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_1350_ = crate::leanh::lean_ctor_get(v___x_1340_, 0);
                                v_isSharedCheck_1357_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1340_)) as u8;
                                if v_isSharedCheck_1357_ == 0 {
                                    v___x_1352_ = v___x_1340_;
                                    v_isShared_1353_ = v_isSharedCheck_1357_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1350_);
                                    crate::leanh::lean_dec(v___x_1340_);
                                    v___x_1352_ = crate::leanh::lean_box(0);
                                    v_isShared_1353_ = v_isSharedCheck_1357_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_1358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__3;
                        v___x_1359_ = lean_array_to_list(v___x_1318_);
                        v___x_1360_ = l_String_intercalate(v___x_1358_, v___x_1359_);
                        v___x_1361_ = l_IO_println___at___00main_spec__3(v___x_1360_);
                        if crate::leanh::lean_obj_tag(v___x_1361_) == 0 {
                            v_isSharedCheck_1369_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1361_)) as u8;
                            if v_isSharedCheck_1369_ == 0 {
                                v_unused_1370_ = crate::leanh::lean_ctor_get(v___x_1361_, 0);
                                crate::leanh::lean_dec(v_unused_1370_);
                                v___x_1363_ = v___x_1361_;
                                v_isShared_1364_ = v_isSharedCheck_1369_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1361_);
                                v___x_1363_ = crate::leanh::lean_box(0);
                                v_isShared_1364_ = v_isSharedCheck_1369_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v_a_1371_ = crate::leanh::lean_ctor_get(v___x_1361_, 0);
                            v_isSharedCheck_1378_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1361_)) as u8;
                            if v_isSharedCheck_1378_ == 0 {
                                v___x_1373_ = v___x_1361_;
                                v_isShared_1374_ = v_isSharedCheck_1378_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1371_);
                                crate::leanh::lean_dec(v___x_1361_);
                                v___x_1373_ = crate::leanh::lean_box(0);
                                v_isShared_1374_ = v_isSharedCheck_1378_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1344_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__5);
                if v_isShared_1343_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1342_, 0, v___x_1344_);
                    v___x_1346_ = v___x_1342_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1347_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1344_);
                    v___x_1346_ = v_reuseFailAlloc_1347_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1346_;
            }
            3 => {
                if v_isShared_1353_ == 0 {
                    v___x_1355_ = v___x_1352_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1356_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
                    v___x_1355_ = v_reuseFailAlloc_1356_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1355_;
            }
            5 => {
                v___x_1365_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__5);
                if v_isShared_1364_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1363_, 0, v___x_1365_);
                    v___x_1367_ = v___x_1363_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1368_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
                    v___x_1367_ = v_reuseFailAlloc_1368_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1367_;
            }
            7 => {
                if v_isShared_1374_ == 0 {
                    v___x_1376_ = v___x_1373_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1377_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
                    v___x_1376_ = v_reuseFailAlloc_1377_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1376_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___boxed(
    mut v___x_1379_: *mut crate::leanh::LeanObject,
    mut v_ldflags_1380_: *mut crate::leanh::LeanObject,
    mut v_as_1381_: *mut crate::leanh::LeanObject,
    mut v_sz_1382_: *mut crate::leanh::LeanObject,
    mut v_i_1383_: *mut crate::leanh::LeanObject,
    mut v_b_1384_: *mut crate::leanh::LeanObject,
    mut v___y_1385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1386_: usize = 0;
    let mut v_i_boxed_1387_: usize = 0;
    let mut v_res_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1386_ = crate::leanh::lean_unbox_usize(v_sz_1382_);
    crate::leanh::lean_dec(v_sz_1382_);
    v_i_boxed_1387_ = crate::leanh::lean_unbox_usize(v_i_1383_);
    crate::leanh::lean_dec(v_i_1383_);
    v_res_1388_ =
        l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4(
            v___x_1379_,
            v_ldflags_1380_,
            v_as_1381_,
            v_sz_boxed_1386_,
            v_i_boxed_1387_,
            v_b_1384_,
        );
    crate::leanh::lean_dec_ref(v_as_1381_);
    crate::leanh::lean_dec_ref(v_ldflags_1380_);
    return v_res_1388_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(
    mut v_as_1389_: *mut crate::leanh::LeanObject,
    mut v_i_1390_: usize,
    mut v_stop_1391_: usize,
    mut v_b_1392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: usize = 0;
    let mut v___x_1396_: usize = 0;
    let mut v___x_1398_: u8 = 0;
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: u8 = 0;
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1398_ = lean_usize_dec_eq(v_i_1390_, v_stop_1391_);
                if v___x_1398_ == 0 {
                    v___x_1399_ = lean_array_uget_borrowed(v_as_1389_, v_i_1390_);
                    v___x_1400_ = lean_string_utf8_byte_size(v___x_1399_);
                    v___x_1401_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1402_ = lean_nat_dec_eq(v___x_1400_, v___x_1401_);
                    if v___x_1402_ == 0 {
                        crate::leanh::lean_inc(v___x_1399_);
                        v___x_1403_ = lean_array_push(v_b_1392_, v___x_1399_);
                        v___y_1394_ = v___x_1403_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1394_ = v_b_1392_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_1392_;
                }
            }
            1 => {
                v___x_1395_ = 1usize;
                v___x_1396_ = lean_usize_add(v_i_1390_, v___x_1395_);
                v_i_1390_ = v___x_1396_;
                v_b_1392_ = v___y_1394_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(
    mut v_as_1404_: *mut crate::leanh::LeanObject,
    mut v_i_1405_: *mut crate::leanh::LeanObject,
    mut v_stop_1406_: *mut crate::leanh::LeanObject,
    mut v_b_1407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1408_: usize = 0;
    let mut v_stop_boxed_1409_: usize = 0;
    let mut v_res_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1408_ = crate::leanh::lean_unbox_usize(v_i_1405_);
    crate::leanh::lean_dec(v_i_1405_);
    v_stop_boxed_1409_ = crate::leanh::lean_unbox_usize(v_stop_1406_);
    crate::leanh::lean_dec(v_stop_1406_);
    v_res_1410_ =
        l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(
            v_as_1404_,
            v_i_boxed_1408_,
            v_stop_boxed_1409_,
            v_b_1407_,
        );
    crate::leanh::lean_dec_ref(v_as_1404_);
    return v_res_1410_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0(
    mut v_fst_1420_: *mut crate::leanh::LeanObject,
    mut v_fst_1421_: *mut crate::leanh::LeanObject,
    mut v_fst_1422_: *mut crate::leanh::LeanObject,
    mut v_fst_1423_: *mut crate::leanh::LeanObject,
    mut v___x_1424_: u8,
    mut v_arg_1425_: *mut crate::leanh::LeanObject,
    mut v_rest_1426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sourcefile_x3f_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optLevel_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1441_: u8 = 0;
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: u8 = 0;
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: u8 = 0;
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: u8 = 0;
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: u8 = 0;
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: u8 = 0;
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: u8 = 0;
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1452_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__5___closed__0;
                v___x_1453_ = lean_string_utf8_byte_size(v_arg_1425_);
                v___x_1454_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__5___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__5___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__5___closed__1);
                v___x_1455_ = lean_nat_dec_le(v___x_1454_, v___x_1453_);
                if v___x_1455_ == 0 {
                    state = 4;
                    continue;
                } else {
                    v___x_1456_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1457_ = lean_nat_sub(v___x_1453_, v___x_1454_);
                    v___x_1458_ = lean_string_memcmp(
                        v_arg_1425_,
                        v___x_1452_,
                        v___x_1457_,
                        v___x_1456_,
                        v___x_1454_,
                    );
                    crate::leanh::lean_dec(v___x_1457_);
                    if v___x_1458_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_fst_1421_);
                        v___x_1459_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1459_, 0, v_arg_1425_);
                        v_sourcefile_x3f_1429_ = v___x_1459_;
                        v_optLevel_1430_ = v_fst_1423_;
                        v_debug_1431_ = v_fst_1422_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1432_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1432_, 0, v_debug_1431_);
                crate::leanh::lean_ctor_set(v___x_1432_, 1, v_rest_1426_);
                v___x_1433_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1433_, 0, v_optLevel_1430_);
                crate::leanh::lean_ctor_set(v___x_1433_, 1, v___x_1432_);
                v___x_1434_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1434_, 0, v_sourcefile_x3f_1429_);
                crate::leanh::lean_ctor_set(v___x_1434_, 1, v___x_1433_);
                v___x_1435_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1435_, 0, v_fst_1420_);
                crate::leanh::lean_ctor_set(v___x_1435_, 1, v___x_1434_);
                v___x_1436_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1436_, 0, v___x_1435_);
                v___x_1437_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1437_, 0, v___x_1436_);
                return v___x_1437_;
            }
            2 => {
                v___x_1439_ = l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__0;
                v_sourcefile_x3f_1429_ = v_fst_1421_;
                v_optLevel_1430_ = v___x_1439_;
                v_debug_1431_ = v_fst_1422_;
                state = 1;
                continue;
            }
            3 => {
                if v___y_1441_ == 0 {
                    v___x_1442_ = l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__1;
                    v___x_1443_ = lean_string_dec_eq(v_arg_1425_, v___x_1442_);
                    crate::leanh::lean_dec_ref(v_arg_1425_);
                    if v___x_1443_ == 0 {
                        v_sourcefile_x3f_1429_ = v_fst_1421_;
                        v_optLevel_1430_ = v_fst_1423_;
                        v_debug_1431_ = v_fst_1422_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_fst_1423_);
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_arg_1425_);
                    crate::leanh::lean_dec(v_fst_1423_);
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_1445_ = l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__2;
                v___x_1446_ = lean_string_dec_eq(v_arg_1425_, v___x_1445_);
                if v___x_1446_ == 0 {
                    v___x_1447_ = l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__3;
                    v___x_1448_ = lean_string_dec_eq(v_arg_1425_, v___x_1447_);
                    if v___x_1448_ == 0 {
                        v___x_1449_ = l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__4;
                        v___x_1450_ = lean_string_dec_eq(v_arg_1425_, v___x_1449_);
                        v___y_1441_ = v___x_1450_;
                        state = 3;
                        continue;
                    } else {
                        v___y_1441_ = v___x_1424_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_arg_1425_);
                    crate::leanh::lean_dec(v_fst_1422_);
                    v___x_1451_ = l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___closed__5;
                    v_sourcefile_x3f_1429_ = v_fst_1421_;
                    v_optLevel_1430_ = v_fst_1423_;
                    v_debug_1431_ = v___x_1451_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0___boxed(
    mut v_fst_1460_: *mut crate::leanh::LeanObject,
    mut v_fst_1461_: *mut crate::leanh::LeanObject,
    mut v_fst_1462_: *mut crate::leanh::LeanObject,
    mut v_fst_1463_: *mut crate::leanh::LeanObject,
    mut v___x_1464_: *mut crate::leanh::LeanObject,
    mut v_arg_1465_: *mut crate::leanh::LeanObject,
    mut v_rest_1466_: *mut crate::leanh::LeanObject,
    mut v___y_1467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_12453__boxed_1468_: u8 = 0;
    let mut v_res_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_12453__boxed_1468_ = (crate::leanh::lean_unbox(v___x_1464_) as u8);
    v_res_1469_ = l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0(
        v_fst_1460_,
        v_fst_1461_,
        v_fst_1462_,
        v_fst_1463_,
        v___x_12453__boxed_1468_,
        v_arg_1465_,
        v_rest_1466_,
    );
    return v_res_1469_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg(
    mut v___x_1471_: u8,
    mut v_a_1472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1479_: u8 = 0;
    let mut v_a_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1486_: u8 = 0;
    let mut v_a_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1490_: u8 = 0;
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1494_: u8 = 0;
    let mut v_snd_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1501_: u8 = 0;
    let mut v_fst_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1505_: u8 = 0;
    let mut v_fst_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1509_: u8 = 0;
    let mut v_fst_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1514_: u8 = 0;
    let mut v___x_1515_: u8 = 0;
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: u8 = 0;
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1564_: u8 = 0;
    let mut v_isSharedCheck_1565_: u8 = 0;
    let mut v_unused_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1567_: u8 = 0;
    let mut v_unused_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1569_: u8 = 0;
    let mut v_unused_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_1495_ = crate::leanh::lean_ctor_get(v_a_1472_, 1);
                crate::leanh::lean_inc(v_snd_1495_);
                v_snd_1496_ = crate::leanh::lean_ctor_get(v_snd_1495_, 1);
                crate::leanh::lean_inc(v_snd_1496_);
                v_snd_1497_ = crate::leanh::lean_ctor_get(v_snd_1496_, 1);
                crate::leanh::lean_inc(v_snd_1497_);
                v_fst_1498_ = crate::leanh::lean_ctor_get(v_a_1472_, 0);
                v_isSharedCheck_1569_ = (!crate::leanh::lean_is_exclusive(v_a_1472_)) as u8;
                if v_isSharedCheck_1569_ == 0 {
                    v_unused_1570_ = crate::leanh::lean_ctor_get(v_a_1472_, 1);
                    crate::leanh::lean_dec(v_unused_1570_);
                    v___x_1500_ = v_a_1472_;
                    v_isShared_1501_ = v_isSharedCheck_1569_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_1498_);
                    crate::leanh::lean_dec(v_a_1472_);
                    v___x_1500_ = crate::leanh::lean_box(0);
                    v_isShared_1501_ = v_isSharedCheck_1569_;
                    state = 6;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_1475_) == 0 {
                    v_a_1476_ = crate::leanh::lean_ctor_get(v___y_1475_, 0);
                    v_isSharedCheck_1486_ = (!crate::leanh::lean_is_exclusive(v___y_1475_)) as u8;
                    if v_isSharedCheck_1486_ == 0 {
                        v___x_1478_ = v___y_1475_;
                        v_isShared_1479_ = v_isSharedCheck_1486_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1476_);
                        crate::leanh::lean_dec(v___y_1475_);
                        v___x_1478_ = crate::leanh::lean_box(0);
                        v_isShared_1479_ = v_isSharedCheck_1486_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1487_ = crate::leanh::lean_ctor_get(v___y_1475_, 0);
                    v_isSharedCheck_1494_ = (!crate::leanh::lean_is_exclusive(v___y_1475_)) as u8;
                    if v_isSharedCheck_1494_ == 0 {
                        v___x_1489_ = v___y_1475_;
                        v_isShared_1490_ = v_isSharedCheck_1494_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1487_);
                        crate::leanh::lean_dec(v___y_1475_);
                        v___x_1489_ = crate::leanh::lean_box(0);
                        v_isShared_1490_ = v_isSharedCheck_1494_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_1476_) == 0 {
                    v_a_1480_ = crate::leanh::lean_ctor_get(v_a_1476_, 0);
                    crate::leanh::lean_inc(v_a_1480_);
                    crate::leanh::lean_dec_ref_known(v_a_1476_, 1);
                    if v_isShared_1479_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1478_, 0, v_a_1480_);
                        v___x_1482_ = v___x_1478_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1483_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1480_);
                        v___x_1482_ = v_reuseFailAlloc_1483_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1478_);
                    v_a_1484_ = crate::leanh::lean_ctor_get(v_a_1476_, 0);
                    crate::leanh::lean_inc(v_a_1484_);
                    crate::leanh::lean_dec_ref_known(v_a_1476_, 1);
                    v_a_1472_ = v_a_1484_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_1482_;
            }
            4 => {
                if v_isShared_1490_ == 0 {
                    v___x_1492_ = v___x_1489_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1493_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
                    v___x_1492_ = v_reuseFailAlloc_1493_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1492_;
            }
            6 => {
                v_fst_1502_ = crate::leanh::lean_ctor_get(v_snd_1495_, 0);
                v_isSharedCheck_1567_ = (!crate::leanh::lean_is_exclusive(v_snd_1495_)) as u8;
                if v_isSharedCheck_1567_ == 0 {
                    v_unused_1568_ = crate::leanh::lean_ctor_get(v_snd_1495_, 1);
                    crate::leanh::lean_dec(v_unused_1568_);
                    v___x_1504_ = v_snd_1495_;
                    v_isShared_1505_ = v_isSharedCheck_1567_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_1502_);
                    crate::leanh::lean_dec(v_snd_1495_);
                    v___x_1504_ = crate::leanh::lean_box(0);
                    v_isShared_1505_ = v_isSharedCheck_1567_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_fst_1506_ = crate::leanh::lean_ctor_get(v_snd_1496_, 0);
                v_isSharedCheck_1565_ = (!crate::leanh::lean_is_exclusive(v_snd_1496_)) as u8;
                if v_isSharedCheck_1565_ == 0 {
                    v_unused_1566_ = crate::leanh::lean_ctor_get(v_snd_1496_, 1);
                    crate::leanh::lean_dec(v_unused_1566_);
                    v___x_1508_ = v_snd_1496_;
                    v_isShared_1509_ = v_isSharedCheck_1565_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_1506_);
                    crate::leanh::lean_dec(v_snd_1496_);
                    v___x_1508_ = crate::leanh::lean_box(0);
                    v_isShared_1509_ = v_isSharedCheck_1565_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_fst_1510_ = crate::leanh::lean_ctor_get(v_snd_1497_, 0);
                v_snd_1511_ = crate::leanh::lean_ctor_get(v_snd_1497_, 1);
                v_isSharedCheck_1564_ = (!crate::leanh::lean_is_exclusive(v_snd_1497_)) as u8;
                if v_isSharedCheck_1564_ == 0 {
                    v___x_1513_ = v_snd_1497_;
                    v_isShared_1514_ = v_isSharedCheck_1564_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1511_);
                    crate::leanh::lean_inc(v_fst_1510_);
                    crate::leanh::lean_dec(v_snd_1497_);
                    v___x_1513_ = crate::leanh::lean_box(0);
                    v_isShared_1514_ = v_isSharedCheck_1564_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1515_ = l_List_isEmpty___redArg(v_snd_1511_);
                if v___x_1515_ == 0 {
                    if crate::leanh::lean_obj_tag(v_snd_1511_) == 0 {
                        if v_isShared_1514_ == 0 {
                            v___x_1517_ = v___x_1513_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_1528_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_fst_1510_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_snd_1511_);
                            v___x_1517_ = v_reuseFailAlloc_1528_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v_head_1529_ = crate::leanh::lean_ctor_get(v_snd_1511_, 0);
                        crate::leanh::lean_inc(v_head_1529_);
                        v_tail_1530_ = crate::leanh::lean_ctor_get(v_snd_1511_, 1);
                        crate::leanh::lean_inc(v_tail_1530_);
                        crate::leanh::lean_dec_ref_known(v_snd_1511_, 2);
                        v___x_1531_ = l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___closed__0;
                        v___x_1532_ = lean_string_dec_eq(v_head_1529_, v___x_1531_);
                        if v___x_1532_ == 0 {
                            crate::leanh::lean_del_object(v___x_1513_);
                            crate::leanh::lean_del_object(v___x_1508_);
                            crate::leanh::lean_del_object(v___x_1504_);
                            crate::leanh::lean_del_object(v___x_1500_);
                            v___x_1533_ = l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0(v_fst_1498_, v_fst_1502_, v_fst_1510_, v_fst_1506_, v___x_1471_, v_head_1529_, v_tail_1530_);
                            v___y_1475_ = v___x_1533_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_head_1529_);
                            if crate::leanh::lean_obj_tag(v_tail_1530_) == 1 {
                                crate::leanh::lean_dec(v_fst_1498_);
                                v_head_1534_ = crate::leanh::lean_ctor_get(v_tail_1530_, 0);
                                crate::leanh::lean_inc(v_head_1534_);
                                v_tail_1535_ = crate::leanh::lean_ctor_get(v_tail_1530_, 1);
                                crate::leanh::lean_inc(v_tail_1535_);
                                crate::leanh::lean_dec_ref_known(v_tail_1530_, 2);
                                v___x_1536_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1536_, 0, v_head_1534_);
                                if v_isShared_1514_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1513_, 1, v_tail_1535_);
                                    v___x_1538_ = v___x_1513_;
                                    state = 14;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1549_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1549_,
                                        0,
                                        v_fst_1510_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1549_,
                                        1,
                                        v_tail_1535_,
                                    );
                                    v___x_1538_ = v_reuseFailAlloc_1549_;
                                    state = 14;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_1513_);
                                crate::leanh::lean_del_object(v___x_1508_);
                                crate::leanh::lean_del_object(v___x_1504_);
                                crate::leanh::lean_del_object(v___x_1500_);
                                v___x_1550_ = l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___lam__0(v_fst_1498_, v_fst_1502_, v_fst_1510_, v_fst_1506_, v___x_1471_, v___x_1531_, v_tail_1530_);
                                v___y_1475_ = v___x_1550_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                } else {
                    if v_isShared_1514_ == 0 {
                        v___x_1552_ = v___x_1513_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_1563_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_fst_1510_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1563_, 1, v_snd_1511_);
                        v___x_1552_ = v_reuseFailAlloc_1563_;
                        state = 18;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_1509_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1508_, 1, v___x_1517_);
                    v___x_1519_ = v___x_1508_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1527_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_fst_1506_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 1, v___x_1517_);
                    v___x_1519_ = v_reuseFailAlloc_1527_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1505_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1504_, 1, v___x_1519_);
                    v___x_1521_ = v___x_1504_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1526_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_fst_1502_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1526_, 1, v___x_1519_);
                    v___x_1521_ = v_reuseFailAlloc_1526_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_1501_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1500_, 1, v___x_1521_);
                    v___x_1523_ = v___x_1500_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1525_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_fst_1498_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1525_, 1, v___x_1521_);
                    v___x_1523_ = v_reuseFailAlloc_1525_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_1524_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1524_, 0, v___x_1523_);
                return v___x_1524_;
            }
            14 => {
                if v_isShared_1509_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1508_, 1, v___x_1538_);
                    v___x_1540_ = v___x_1508_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1548_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_fst_1506_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1548_, 1, v___x_1538_);
                    v___x_1540_ = v_reuseFailAlloc_1548_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1505_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1504_, 1, v___x_1540_);
                    v___x_1542_ = v___x_1504_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1547_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_fst_1502_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1547_, 1, v___x_1540_);
                    v___x_1542_ = v_reuseFailAlloc_1547_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_1501_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1500_, 1, v___x_1542_);
                    crate::leanh::lean_ctor_set(v___x_1500_, 0, v___x_1536_);
                    v___x_1544_ = v___x_1500_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1546_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1536_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1546_, 1, v___x_1542_);
                    v___x_1544_ = v_reuseFailAlloc_1546_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v_a_1472_ = v___x_1544_;
                state = 0;
                continue;
            }
            18 => {
                if v_isShared_1509_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1508_, 1, v___x_1552_);
                    v___x_1554_ = v___x_1508_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1562_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_fst_1506_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1562_, 1, v___x_1552_);
                    v___x_1554_ = v_reuseFailAlloc_1562_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1505_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1504_, 1, v___x_1554_);
                    v___x_1556_ = v___x_1504_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1561_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_fst_1502_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1561_, 1, v___x_1554_);
                    v___x_1556_ = v_reuseFailAlloc_1561_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_1501_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1500_, 1, v___x_1556_);
                    v___x_1558_ = v___x_1500_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1560_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_fst_1498_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1560_, 1, v___x_1556_);
                    v___x_1558_ = v_reuseFailAlloc_1560_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_1559_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1559_, 0, v___x_1558_);
                return v___x_1559_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___boxed(
    mut v___x_1571_: *mut crate::leanh::LeanObject,
    mut v_a_1572_: *mut crate::leanh::LeanObject,
    mut v___y_1573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_12528__boxed_1574_: u8 = 0;
    let mut v_res_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_12528__boxed_1574_ = (crate::leanh::lean_unbox(v___x_1571_) as u8);
    v_res_1575_ = l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg(
        v___x_12528__boxed_1574_,
        v_a_1572_,
    );
    return v_res_1575_;
}
pub unsafe fn _init_l_main___closed__14() -> *mut crate::leanh::LeanObject {
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1600_ = l_main___closed__13;
    v___x_1601_ = lean_string_utf8_byte_size(v___x_1600_);
    return v___x_1601_;
}
pub unsafe fn _init_l_main___closed__31() -> *mut crate::leanh::LeanObject {
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1624_ =
        l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg___closed__0;
    v___x_1625_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_1626_ = lean_mk_empty_array_with_capacity(v___x_1625_);
    v___x_1627_ = lean_array_push(v___x_1626_, v___x_1624_);
    return v___x_1627_;
}
pub unsafe fn _init_l_main___closed__38() -> usize {
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1644_: usize = 0;
    v___x_1643_ = l_main___closed__37;
    v_sz_1644_ = lean_array_size(v___x_1643_);
    return v_sz_1644_;
}
pub unsafe fn _init_l_main___closed__40() -> *mut crate::leanh::LeanObject {
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1646_ = l_main___closed__30;
    v___x_1647_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1648_ = lean_mk_empty_array_with_capacity(v___x_1647_);
    v___x_1649_ = lean_array_push(v___x_1648_, v___x_1646_);
    return v___x_1649_;
}
pub unsafe fn _init_l_main___closed__57() -> *mut crate::leanh::LeanObject {
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1667_ = l_main___closed__56;
    v___x_1668_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_1669_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_1670_ = l_main___closed__55;
    v___x_1671_ = l_main___closed__54;
    v___x_1672_ = l_mkPanicMessageWithDecl(
        v___x_1671_,
        v___x_1670_,
        v___x_1669_,
        v___x_1668_,
        v___x_1667_,
    );
    return v___x_1672_;
}
pub unsafe fn _init_l_main___boxed__const__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1673_: u32 = 0;
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1673_ = 1;
    v___x_1674_ = crate::leanh::lean_box_uint32(v___x_1673_);
    return v___x_1674_;
}
pub unsafe fn _lean_main(
    mut v_args_1675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1678_: u8 = 0;
    let mut v___y_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1680_: u8 = 0;
    let mut v___y_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1692_: u8 = 0;
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1696_: u8 = 0;
    let mut v___y_1698_: u8 = 0;
    let mut v___y_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1700_: u8 = 0;
    let mut v___y_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: u8 = 0;
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1714_: u8 = 0;
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1718_: u8 = 0;
    let mut v___y_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1721_: u8 = 0;
    let mut v___y_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1725_: u8 = 0;
    let mut v___y_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cc_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cflagsInternal_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ldflagsInternal_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: u8 = 0;
    let mut v___x_1739_: u8 = 0;
    let mut v___x_1740_: usize = 0;
    let mut v___x_1741_: usize = 0;
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: usize = 0;
    let mut v___x_1744_: usize = 0;
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1747_: u8 = 0;
    let mut v___y_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1751_: u8 = 0;
    let mut v___y_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ldflags_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1758_: usize = 0;
    let mut v___x_1759_: usize = 0;
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1764_: u8 = 0;
    let mut v_fst_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1774_: u8 = 0;
    let mut v_a_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1778_: u8 = 0;
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1782_: u8 = 0;
    let mut v___y_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1785_: u8 = 0;
    let mut v___y_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1788_: u8 = 0;
    let mut v___y_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1794_: u8 = 0;
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1799_: u8 = 0;
    let mut v___y_1800_: u8 = 0;
    let mut v___y_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: u32 = 0;
    let mut v___x_1812_: u32 = 0;
    let mut v___x_1813_: u8 = 0;
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1816_: u8 = 0;
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1821_: u8 = 0;
    let mut v_unused_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1826_: u8 = 0;
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1830_: u8 = 0;
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1836_: u8 = 0;
    let mut v___y_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1839_: u8 = 0;
    let mut v___y_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1842_: u8 = 0;
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: u8 = 0;
    let mut v___x_1850_: u8 = 0;
    let mut v___y_1852_: u8 = 0;
    let mut v___y_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1855_: u8 = 0;
    let mut v___y_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: u8 = 0;
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: u8 = 0;
    let mut v___y_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: u8 = 0;
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: u8 = 0;
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1883_: u8 = 0;
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1888_: u8 = 0;
    let mut v_unused_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1893_: u8 = 0;
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1897_: u8 = 0;
    let mut v___y_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1902_: u8 = 0;
    let mut v___y_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1909_: u8 = 0;
    let mut v___y_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: u8 = 0;
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1960_: u8 = 0;
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1964_: u8 = 0;
    let mut v___y_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1968_: u8 = 0;
    let mut v___y_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1976_: u8 = 0;
    let mut v___y_1977_: usize = 0;
    let mut v___y_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1983_: usize = 0;
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: u8 = 0;
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1994_: u8 = 0;
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1998_: u8 = 0;
    let mut v___y_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2002_: u8 = 0;
    let mut v___y_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2010_: u8 = 0;
    let mut v___y_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2012_: usize = 0;
    let mut v___y_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2014_: u8 = 0;
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2020_: u8 = 0;
    let mut v___y_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2028_: u8 = 0;
    let mut v___y_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2030_: usize = 0;
    let mut v___y_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2032_: u32 = 0;
    let mut v___x_2033_: u32 = 0;
    let mut v___x_2034_: u8 = 0;
    let mut v___x_2035_: u32 = 0;
    let mut v___x_2036_: u8 = 0;
    let mut v___y_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2040_: u8 = 0;
    let mut v___y_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2048_: u8 = 0;
    let mut v___y_2049_: usize = 0;
    let mut v___y_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: u8 = 0;
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: u32 = 0;
    let mut v_val_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: u32 = 0;
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2064_: u8 = 0;
    let mut v___y_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2066_: u8 = 0;
    let mut v___y_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2069_: usize = 0;
    let mut v___y_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rlib_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2081_: u8 = 0;
    let mut v___y_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2083_: u8 = 0;
    let mut v___y_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2085_: usize = 0;
    let mut v___y_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: u8 = 0;
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2102_: u8 = 0;
    let mut v___y_2103_: u8 = 0;
    let mut v___y_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2105_: usize = 0;
    let mut v___y_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2118_: u8 = 0;
    let mut v___y_2119_: u8 = 0;
    let mut v___y_2120_: usize = 0;
    let mut v___y_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: u8 = 0;
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: u8 = 0;
    let mut v___x_2139_: usize = 0;
    let mut v___x_2140_: usize = 0;
    let mut v___x_2141_: u8 = 0;
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: u8 = 0;
    let mut v_snd_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: u8 = 0;
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2170_: u8 = 0;
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2175_: u8 = 0;
    let mut v_unused_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2180_: u8 = 0;
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2184_: u8 = 0;
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2189_: u8 = 0;
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2194_: u8 = 0;
    let mut v_unused_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2199_: u8 = 0;
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2203_: u8 = 0;
    let mut v_a_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2207_: u8 = 0;
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2211_: u8 = 0;
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2221_: u8 = 0;
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2225_: u8 = 0;
    let mut v_val_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1831_ = l_main___closed__10;
                v___x_1832_ = lean_io_getenv(v___x_1831_);
                v_args_1833_ = lean_array_mk(v_args_1675_);
                if crate::leanh::lean_obj_tag(v___x_1832_) == 0 {
                    v___x_2212_ = l_IO_appDir();
                    if crate::leanh::lean_obj_tag(v___x_2212_) == 0 {
                        v_a_2213_ = crate::leanh::lean_ctor_get(v___x_2212_, 0);
                        crate::leanh::lean_inc(v_a_2213_);
                        crate::leanh::lean_dec_ref_known(v___x_2212_, 1);
                        v___x_2214_ = l_System_FilePath_parent(v_a_2213_);
                        if crate::leanh::lean_obj_tag(v___x_2214_) == 0 {
                            v___x_2215_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_main___closed__57),
                                core::ptr::addr_of_mut!(l_main___closed__57_once),
                                _init_l_main___closed__57,
                            );
                            v___x_2216_ = l_panic___at___00main_spec__9(v___x_2215_);
                            v_root_2135_ = v___x_2216_;
                            state = 39;
                            continue;
                        } else {
                            v_val_2217_ = crate::leanh::lean_ctor_get(v___x_2214_, 0);
                            crate::leanh::lean_inc(v_val_2217_);
                            crate::leanh::lean_dec_ref_known(v___x_2214_, 1);
                            v_root_2135_ = v_val_2217_;
                            state = 39;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_args_1833_);
                        v_a_2218_ = crate::leanh::lean_ctor_get(v___x_2212_, 0);
                        v_isSharedCheck_2225_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2212_)) as u8;
                        if v_isSharedCheck_2225_ == 0 {
                            v___x_2220_ = v___x_2212_;
                            v_isShared_2221_ = v_isSharedCheck_2225_;
                            state = 50;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2218_);
                            crate::leanh::lean_dec(v___x_2212_);
                            v___x_2220_ = crate::leanh::lean_box(0);
                            v_isShared_2221_ = v_isSharedCheck_2225_;
                            state = 50;
                            continue;
                        }
                    }
                } else {
                    v_val_2226_ = crate::leanh::lean_ctor_get(v___x_1832_, 0);
                    crate::leanh::lean_inc(v_val_2226_);
                    crate::leanh::lean_dec_ref_known(v___x_1832_, 1);
                    v_root_2135_ = v_val_2226_;
                    state = 39;
                    continue;
                }
            }
            1 => {
                v___x_1683_ = l_main___closed__0;
                v___x_1684_ = crate::leanh::lean_box(0);
                v___x_1685_ = crate::leanh::lean_alloc_ctor(0, 5, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_1685_, 0, v___x_1683_);
                crate::leanh::lean_ctor_set(v___x_1685_, 1, v___y_1679_);
                crate::leanh::lean_ctor_set(v___x_1685_, 2, v___y_1682_);
                crate::leanh::lean_ctor_set(v___x_1685_, 3, v___x_1684_);
                crate::leanh::lean_ctor_set(v___x_1685_, 4, v___y_1681_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1685_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_1678_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1685_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_1680_,
                );
                v___x_1686_ = lean_io_process_spawn(v___x_1685_);
                if crate::leanh::lean_obj_tag(v___x_1686_) == 0 {
                    v_a_1687_ = crate::leanh::lean_ctor_get(v___x_1686_, 0);
                    crate::leanh::lean_inc(v_a_1687_);
                    crate::leanh::lean_dec_ref_known(v___x_1686_, 1);
                    v___x_1688_ = lean_io_process_child_wait(v___x_1683_, v_a_1687_);
                    crate::leanh::lean_dec(v_a_1687_);
                    return v___x_1688_;
                } else {
                    v_a_1689_ = crate::leanh::lean_ctor_get(v___x_1686_, 0);
                    v_isSharedCheck_1696_ = (!crate::leanh::lean_is_exclusive(v___x_1686_)) as u8;
                    if v_isSharedCheck_1696_ == 0 {
                        v___x_1691_ = v___x_1686_;
                        v_isShared_1692_ = v_isSharedCheck_1696_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1689_);
                        crate::leanh::lean_dec(v___x_1686_);
                        v___x_1691_ = crate::leanh::lean_box(0);
                        v_isShared_1692_ = v_isSharedCheck_1696_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1692_ == 0 {
                    v___x_1694_ = v___x_1691_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1695_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
                    v___x_1694_ = v_reuseFailAlloc_1695_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1694_;
            }
            4 => {
                v___x_1703_ = l_main___closed__1;
                v___x_1704_ = l_Array_contains___at___00main_spec__1(v___y_1702_, v___x_1703_);
                if v___x_1704_ == 0 {
                    v___y_1678_ = v___y_1698_;
                    v___y_1679_ = v___y_1699_;
                    v___y_1680_ = v___y_1700_;
                    v___y_1681_ = v___y_1701_;
                    v___y_1682_ = v___y_1702_;
                    state = 1;
                    continue;
                } else {
                    v___x_1705_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__3;
                    crate::leanh::lean_inc_ref(v___y_1699_);
                    v___x_1706_ = lean_string_append(v___y_1699_, v___x_1705_);
                    crate::leanh::lean_inc_ref(v___y_1702_);
                    v___x_1707_ = lean_array_to_list(v___y_1702_);
                    v___x_1708_ = l_String_intercalate(v___x_1705_, v___x_1707_);
                    v___x_1709_ = lean_string_append(v___x_1706_, v___x_1708_);
                    crate::leanh::lean_dec_ref(v___x_1708_);
                    v___x_1710_ =
                        l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(
                            v___x_1709_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1710_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1710_, 1);
                        v___y_1678_ = v___y_1698_;
                        v___y_1679_ = v___y_1699_;
                        v___y_1680_ = v___y_1700_;
                        v___y_1681_ = v___y_1701_;
                        v___y_1682_ = v___y_1702_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_1702_);
                        crate::leanh::lean_dec_ref(v___y_1701_);
                        crate::leanh::lean_dec_ref(v___y_1699_);
                        v_a_1711_ = crate::leanh::lean_ctor_get(v___x_1710_, 0);
                        v_isSharedCheck_1718_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1710_)) as u8;
                        if v_isSharedCheck_1718_ == 0 {
                            v___x_1713_ = v___x_1710_;
                            v_isShared_1714_ = v_isSharedCheck_1718_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1711_);
                            crate::leanh::lean_dec(v___x_1710_);
                            v___x_1713_ = crate::leanh::lean_box(0);
                            v_isShared_1714_ = v_isSharedCheck_1718_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            5 => {
                if v_isShared_1714_ == 0 {
                    v___x_1716_ = v___x_1713_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1717_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
                    v___x_1716_ = v_reuseFailAlloc_1717_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1716_;
            }
            7 => {
                v___x_1730_ = l_Array_append___redArg(v___y_1724_, v_cflagsInternal_1728_);
                crate::leanh::lean_dec_ref(v_cflagsInternal_1728_);
                v___x_1731_ = l_Array_append___redArg(v___x_1730_, v___y_1722_);
                crate::leanh::lean_dec_ref(v___y_1722_);
                v___x_1732_ = l_Array_append___redArg(v___x_1731_, v_ldflagsInternal_1729_);
                crate::leanh::lean_dec_ref(v_ldflagsInternal_1729_);
                v___x_1733_ = l_Array_append___redArg(v___x_1732_, v___y_1723_);
                crate::leanh::lean_dec_ref(v___y_1723_);
                v___x_1734_ = l_main___closed__3;
                v___x_1735_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                    v___x_1733_,
                    v___x_1734_,
                );
                v___x_1736_ = lean_array_get_size(v___x_1735_);
                v___x_1737_ = lean_mk_empty_array_with_capacity(v___y_1720_);
                v___x_1738_ = lean_nat_dec_lt(v___y_1720_, v___x_1736_);
                crate::leanh::lean_dec(v___y_1720_);
                if v___x_1738_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1735_);
                    v___y_1698_ = v___y_1721_;
                    v___y_1699_ = v_cc_1727_;
                    v___y_1700_ = v___y_1725_;
                    v___y_1701_ = v___y_1726_;
                    v___y_1702_ = v___x_1737_;
                    state = 4;
                    continue;
                } else {
                    v___x_1739_ = lean_nat_dec_le(v___x_1736_, v___x_1736_);
                    if v___x_1739_ == 0 {
                        if v___x_1738_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1735_);
                            v___y_1698_ = v___y_1721_;
                            v___y_1699_ = v_cc_1727_;
                            v___y_1700_ = v___y_1725_;
                            v___y_1701_ = v___y_1726_;
                            v___y_1702_ = v___x_1737_;
                            state = 4;
                            continue;
                        } else {
                            v___x_1740_ = 0usize;
                            v___x_1741_ = lean_usize_of_nat(v___x_1736_);
                            v___x_1742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_1735_, v___x_1740_, v___x_1741_, v___x_1737_);
                            crate::leanh::lean_dec_ref(v___x_1735_);
                            v___y_1698_ = v___y_1721_;
                            v___y_1699_ = v_cc_1727_;
                            v___y_1700_ = v___y_1725_;
                            v___y_1701_ = v___y_1726_;
                            v___y_1702_ = v___x_1742_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_1743_ = 0usize;
                        v___x_1744_ = lean_usize_of_nat(v___x_1736_);
                        v___x_1745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_1735_, v___x_1743_, v___x_1744_, v___x_1737_);
                        crate::leanh::lean_dec_ref(v___x_1735_);
                        v___y_1698_ = v___y_1721_;
                        v___y_1699_ = v_cc_1727_;
                        v___y_1700_ = v___y_1725_;
                        v___y_1701_ = v___y_1726_;
                        v___y_1702_ = v___x_1745_;
                        state = 4;
                        continue;
                    }
                }
            }
            8 => {
                v___x_1757_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__2;
                v_sz_1758_ = lean_array_size(v___y_1749_);
                v___x_1759_ = 0usize;
                crate::leanh::lean_inc_ref(v___y_1750_);
                v___x_1760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4(v___y_1750_, v_ldflags_1756_, v___y_1749_, v_sz_1758_, v___x_1759_, v___x_1757_);
                if crate::leanh::lean_obj_tag(v___x_1760_) == 0 {
                    v_a_1761_ = crate::leanh::lean_ctor_get(v___x_1760_, 0);
                    v_isSharedCheck_1774_ = (!crate::leanh::lean_is_exclusive(v___x_1760_)) as u8;
                    if v_isSharedCheck_1774_ == 0 {
                        v___x_1763_ = v___x_1760_;
                        v_isShared_1764_ = v_isSharedCheck_1774_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1761_);
                        crate::leanh::lean_dec(v___x_1760_);
                        v___x_1763_ = crate::leanh::lean_box(0);
                        v_isShared_1764_ = v_isSharedCheck_1774_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_ldflags_1756_);
                    crate::leanh::lean_dec_ref(v___y_1755_);
                    crate::leanh::lean_dec_ref(v___y_1754_);
                    crate::leanh::lean_dec_ref(v___y_1753_);
                    crate::leanh::lean_dec_ref(v___y_1752_);
                    crate::leanh::lean_dec_ref(v___y_1750_);
                    crate::leanh::lean_dec_ref(v___y_1749_);
                    crate::leanh::lean_dec(v___y_1748_);
                    v_a_1775_ = crate::leanh::lean_ctor_get(v___x_1760_, 0);
                    v_isSharedCheck_1782_ = (!crate::leanh::lean_is_exclusive(v___x_1760_)) as u8;
                    if v_isSharedCheck_1782_ == 0 {
                        v___x_1777_ = v___x_1760_;
                        v_isShared_1778_ = v_isSharedCheck_1782_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1775_);
                        crate::leanh::lean_dec(v___x_1760_);
                        v___x_1777_ = crate::leanh::lean_box(0);
                        v_isShared_1778_ = v_isSharedCheck_1782_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                v_fst_1765_ = crate::leanh::lean_ctor_get(v_a_1761_, 0);
                crate::leanh::lean_inc(v_fst_1765_);
                crate::leanh::lean_dec(v_a_1761_);
                if crate::leanh::lean_obj_tag(v_fst_1765_) == 0 {
                    crate::leanh::lean_del_object(v___x_1763_);
                    v___x_1766_ = l_main___closed__4;
                    v___x_1767_ = lean_io_getenv(v___x_1766_);
                    if crate::leanh::lean_obj_tag(v___x_1767_) == 1 {
                        crate::leanh::lean_dec_ref(v___y_1755_);
                        crate::leanh::lean_dec_ref(v___y_1753_);
                        crate::leanh::lean_dec_ref(v___y_1752_);
                        v_val_1768_ = crate::leanh::lean_ctor_get(v___x_1767_, 0);
                        crate::leanh::lean_inc(v_val_1768_);
                        crate::leanh::lean_dec_ref_known(v___x_1767_, 1);
                        v___x_1769_ = lean_mk_empty_array_with_capacity(v___y_1748_);
                        crate::leanh::lean_inc_ref(v___x_1769_);
                        v___y_1720_ = v___y_1748_;
                        v___y_1721_ = v___y_1747_;
                        v___y_1722_ = v___y_1749_;
                        v___y_1723_ = v_ldflags_1756_;
                        v___y_1724_ = v___y_1750_;
                        v___y_1725_ = v___y_1751_;
                        v___y_1726_ = v___y_1754_;
                        v_cc_1727_ = v_val_1768_;
                        v_cflagsInternal_1728_ = v___x_1769_;
                        v_ldflagsInternal_1729_ = v___x_1769_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1767_);
                        v___y_1720_ = v___y_1748_;
                        v___y_1721_ = v___y_1747_;
                        v___y_1722_ = v___y_1749_;
                        v___y_1723_ = v_ldflags_1756_;
                        v___y_1724_ = v___y_1750_;
                        v___y_1725_ = v___y_1751_;
                        v___y_1726_ = v___y_1754_;
                        v_cc_1727_ = v___y_1753_;
                        v_cflagsInternal_1728_ = v___y_1755_;
                        v_ldflagsInternal_1729_ = v___y_1752_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_ldflags_1756_);
                    crate::leanh::lean_dec_ref(v___y_1755_);
                    crate::leanh::lean_dec_ref(v___y_1754_);
                    crate::leanh::lean_dec_ref(v___y_1753_);
                    crate::leanh::lean_dec_ref(v___y_1752_);
                    crate::leanh::lean_dec_ref(v___y_1750_);
                    crate::leanh::lean_dec_ref(v___y_1749_);
                    crate::leanh::lean_dec(v___y_1748_);
                    v_val_1770_ = crate::leanh::lean_ctor_get(v_fst_1765_, 0);
                    crate::leanh::lean_inc(v_val_1770_);
                    crate::leanh::lean_dec_ref_known(v_fst_1765_, 1);
                    if v_isShared_1764_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1763_, 0, v_val_1770_);
                        v___x_1772_ = v___x_1763_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1773_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_val_1770_);
                        v___x_1772_ = v_reuseFailAlloc_1773_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                return v___x_1772_;
            }
            11 => {
                if v_isShared_1778_ == 0 {
                    v___x_1780_ = v___x_1777_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1781_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1775_);
                    v___x_1780_ = v_reuseFailAlloc_1781_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1780_;
            }
            13 => {
                if v___y_1794_ == 0 {
                    v___y_1747_ = v___y_1785_;
                    v___y_1748_ = v___y_1784_;
                    v___y_1749_ = v___y_1786_;
                    v___y_1750_ = v___y_1787_;
                    v___y_1751_ = v___y_1788_;
                    v___y_1752_ = v___y_1792_;
                    v___y_1753_ = v___y_1791_;
                    v___y_1754_ = v___y_1790_;
                    v___y_1755_ = v___y_1793_;
                    v_ldflags_1756_ = v___y_1789_;
                    state = 8;
                    continue;
                } else {
                    v___x_1795_ = l_main___closed__8;
                    v___x_1796_ = l_Array_append___redArg(v___y_1789_, v___x_1795_);
                    v___y_1747_ = v___y_1785_;
                    v___y_1748_ = v___y_1784_;
                    v___y_1749_ = v___y_1786_;
                    v___y_1750_ = v___y_1787_;
                    v___y_1751_ = v___y_1788_;
                    v___y_1752_ = v___y_1792_;
                    v___y_1753_ = v___y_1791_;
                    v___y_1754_ = v___y_1790_;
                    v___y_1755_ = v___y_1793_;
                    v_ldflags_1756_ = v___x_1796_;
                    state = 8;
                    continue;
                }
            }
            14 => {
                v___x_1802_ = l_main___closed__0;
                v___x_1803_ = l_main___closed__9;
                v___x_1804_ = crate::leanh::lean_box(0);
                v___x_1805_ = lean_mk_empty_array_with_capacity(v___y_1798_);
                crate::leanh::lean_dec(v___y_1798_);
                v___x_1806_ = crate::leanh::lean_alloc_ctor(0, 5, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_1806_, 0, v___x_1802_);
                crate::leanh::lean_ctor_set(v___x_1806_, 1, v___x_1803_);
                crate::leanh::lean_ctor_set(v___x_1806_, 2, v___y_1801_);
                crate::leanh::lean_ctor_set(v___x_1806_, 3, v___x_1804_);
                crate::leanh::lean_ctor_set(v___x_1806_, 4, v___x_1805_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1806_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_1799_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1806_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_1800_,
                );
                v___x_1807_ = lean_io_process_spawn(v___x_1806_);
                if crate::leanh::lean_obj_tag(v___x_1807_) == 0 {
                    v_a_1808_ = crate::leanh::lean_ctor_get(v___x_1807_, 0);
                    crate::leanh::lean_inc(v_a_1808_);
                    crate::leanh::lean_dec_ref_known(v___x_1807_, 1);
                    v___x_1809_ = lean_io_process_child_wait(v___x_1802_, v_a_1808_);
                    crate::leanh::lean_dec(v_a_1808_);
                    if crate::leanh::lean_obj_tag(v___x_1809_) == 0 {
                        v_a_1810_ = crate::leanh::lean_ctor_get(v___x_1809_, 0);
                        crate::leanh::lean_inc(v_a_1810_);
                        v___x_1811_ = 0;
                        v___x_1812_ = crate::leanh::lean_unbox_uint32(v_a_1810_);
                        crate::leanh::lean_dec(v_a_1810_);
                        v___x_1813_ = lean_uint32_dec_eq(v___x_1812_, v___x_1811_);
                        if v___x_1813_ == 0 {
                            return v___x_1809_;
                        } else {
                            v_isSharedCheck_1821_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1809_)) as u8;
                            if v_isSharedCheck_1821_ == 0 {
                                v_unused_1822_ = crate::leanh::lean_ctor_get(v___x_1809_, 0);
                                crate::leanh::lean_dec(v_unused_1822_);
                                v___x_1815_ = v___x_1809_;
                                v_isShared_1816_ = v_isSharedCheck_1821_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1809_);
                                v___x_1815_ = crate::leanh::lean_box(0);
                                v_isShared_1816_ = v_isSharedCheck_1821_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        return v___x_1809_;
                    }
                } else {
                    v_a_1823_ = crate::leanh::lean_ctor_get(v___x_1807_, 0);
                    v_isSharedCheck_1830_ = (!crate::leanh::lean_is_exclusive(v___x_1807_)) as u8;
                    if v_isSharedCheck_1830_ == 0 {
                        v___x_1825_ = v___x_1807_;
                        v_isShared_1826_ = v_isSharedCheck_1830_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1823_);
                        crate::leanh::lean_dec(v___x_1807_);
                        v___x_1825_ = crate::leanh::lean_box(0);
                        v_isShared_1826_ = v_isSharedCheck_1830_;
                        state = 17;
                        continue;
                    }
                }
            }
            15 => {
                v___x_1817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__4___boxed__const__1;
                if v_isShared_1816_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1815_, 0, v___x_1817_);
                    v___x_1819_ = v___x_1815_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1820_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
                    v___x_1819_ = v_reuseFailAlloc_1820_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1819_;
            }
            17 => {
                if v_isShared_1826_ == 0 {
                    v___x_1828_ = v___x_1825_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1829_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
                    v___x_1828_ = v_reuseFailAlloc_1829_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1828_;
            }
            19 => {
                v___x_1843_ = l_main___closed__11;
                v___x_1844_ = l_Array_erase___at___00main_spec__0(v_args_1833_, v___x_1843_);
                crate::leanh::lean_inc_ref(v___y_1837_);
                v___x_1845_ = l_Lean_Compiler_FFI_getCFlags(v___y_1837_);
                v___x_1846_ = l_Lean_Compiler_FFI_getInternalCFlags(v___y_1837_);
                v___x_1847_ = l_Lean_Compiler_FFI_getInternalLinkerFlags(v___y_1837_);
                v___x_1848_ = l_Lean_Compiler_FFI_getLinkerFlags(v___y_1837_, v___y_1842_);
                v___x_1849_ = l_System_Platform_isWindows;
                if v___x_1849_ == 0 {
                    v___y_1784_ = v___y_1835_;
                    v___y_1785_ = v___y_1836_;
                    v___y_1786_ = v___x_1844_;
                    v___y_1787_ = v___x_1845_;
                    v___y_1788_ = v___y_1839_;
                    v___y_1789_ = v___x_1848_;
                    v___y_1790_ = v___y_1840_;
                    v___y_1791_ = v___y_1841_;
                    v___y_1792_ = v___x_1847_;
                    v___y_1793_ = v___x_1846_;
                    v___y_1794_ = v___x_1849_;
                    state = 13;
                    continue;
                } else {
                    v___x_1850_ = l_Array_contains___at___00main_spec__1(v___x_1844_, v___y_1838_);
                    if v___x_1850_ == 0 {
                        v___y_1784_ = v___y_1835_;
                        v___y_1785_ = v___y_1836_;
                        v___y_1786_ = v___x_1844_;
                        v___y_1787_ = v___x_1845_;
                        v___y_1788_ = v___y_1839_;
                        v___y_1789_ = v___x_1848_;
                        v___y_1790_ = v___y_1840_;
                        v___y_1791_ = v___y_1841_;
                        v___y_1792_ = v___x_1847_;
                        v___y_1793_ = v___x_1846_;
                        v___y_1794_ = v___x_1849_;
                        state = 13;
                        continue;
                    } else {
                        v___y_1784_ = v___y_1835_;
                        v___y_1785_ = v___y_1836_;
                        v___y_1786_ = v___x_1844_;
                        v___y_1787_ = v___x_1845_;
                        v___y_1788_ = v___y_1839_;
                        v___y_1789_ = v___x_1848_;
                        v___y_1790_ = v___y_1840_;
                        v___y_1791_ = v___y_1841_;
                        v___y_1792_ = v___x_1847_;
                        v___y_1793_ = v___x_1846_;
                        v___y_1794_ = v___y_1839_;
                        state = 13;
                        continue;
                    }
                }
            }
            20 => {
                v___x_1858_ = l_main___closed__12;
                v___x_1859_ = l_Array_contains___at___00main_spec__1(v_args_1833_, v___x_1858_);
                if v___x_1859_ == 0 {
                    v___x_1860_ = l_main___closed__11;
                    v___x_1861_ = l_Array_contains___at___00main_spec__1(v_args_1833_, v___x_1860_);
                    if v___x_1861_ == 0 {
                        v___y_1835_ = v___y_1853_;
                        v___y_1836_ = v___y_1852_;
                        v___y_1837_ = v___y_1854_;
                        v___y_1838_ = v___x_1858_;
                        v___y_1839_ = v___y_1855_;
                        v___y_1840_ = v___y_1857_;
                        v___y_1841_ = v___y_1856_;
                        v___y_1842_ = v___y_1852_;
                        state = 19;
                        continue;
                    } else {
                        v___y_1835_ = v___y_1853_;
                        v___y_1836_ = v___y_1852_;
                        v___y_1837_ = v___y_1854_;
                        v___y_1838_ = v___x_1858_;
                        v___y_1839_ = v___y_1855_;
                        v___y_1840_ = v___y_1857_;
                        v___y_1841_ = v___y_1856_;
                        v___y_1842_ = v___y_1855_;
                        state = 19;
                        continue;
                    }
                } else {
                    v___y_1835_ = v___y_1853_;
                    v___y_1836_ = v___y_1852_;
                    v___y_1837_ = v___y_1854_;
                    v___y_1838_ = v___x_1858_;
                    v___y_1839_ = v___y_1855_;
                    v___y_1840_ = v___y_1857_;
                    v___y_1841_ = v___y_1856_;
                    v___y_1842_ = v___y_1855_;
                    state = 19;
                    continue;
                }
            }
            21 => {
                v___x_1865_ = l_main___closed__13;
                v___x_1866_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_main___closed__14),
                    core::ptr::addr_of_mut!(l_main___closed__14_once),
                    _init_l_main___closed__14,
                );
                crate::leanh::lean_inc(v___y_1863_);
                v___x_1867_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1867_, 0, v___x_1865_);
                crate::leanh::lean_ctor_set(v___x_1867_, 1, v___y_1863_);
                crate::leanh::lean_ctor_set(v___x_1867_, 2, v___x_1866_);
                v___x_1868_ = l_String_Slice_replace___at___00Lean_Compiler_FFI_getInternalCFlags_spec__0___redArg(v___x_1867_, v___y_1864_);
                v___x_1869_ = lean_array_get_size(v_args_1833_);
                v___x_1870_ = lean_nat_dec_eq(v___x_1869_, v___y_1863_);
                if v___x_1870_ == 0 {
                    v___x_1871_ = l_main___closed__15;
                    v___x_1872_ = lean_io_getenv(v___x_1871_);
                    v___x_1873_ = 1;
                    if crate::leanh::lean_obj_tag(v___x_1872_) == 0 {
                        v___x_1874_ = l_main___closed__19;
                        v___y_1852_ = v___x_1873_;
                        v___y_1853_ = v___y_1863_;
                        v___y_1854_ = v___y_1864_;
                        v___y_1855_ = v___x_1870_;
                        v___y_1856_ = v___x_1868_;
                        v___y_1857_ = v___x_1874_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_1872_, 1);
                        v___x_1875_ = lean_mk_empty_array_with_capacity(v___y_1863_);
                        v___y_1852_ = v___x_1873_;
                        v___y_1853_ = v___y_1863_;
                        v___y_1854_ = v___y_1864_;
                        v___y_1855_ = v___x_1870_;
                        v___y_1856_ = v___x_1868_;
                        v___y_1857_ = v___x_1875_;
                        state = 20;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_1864_);
                    crate::leanh::lean_dec(v___y_1863_);
                    crate::leanh::lean_dec_ref(v_args_1833_);
                    v___x_1876_ = l_main___closed__20;
                    v___x_1877_ = lean_string_append(v___x_1876_, v___x_1868_);
                    crate::leanh::lean_dec_ref(v___x_1868_);
                    v___x_1878_ = l_main___closed__21;
                    v___x_1879_ = lean_string_append(v___x_1877_, v___x_1878_);
                    v___x_1880_ = l_IO_println___at___00main_spec__3(v___x_1879_);
                    if crate::leanh::lean_obj_tag(v___x_1880_) == 0 {
                        v_isSharedCheck_1888_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1880_)) as u8;
                        if v_isSharedCheck_1888_ == 0 {
                            v_unused_1889_ = crate::leanh::lean_ctor_get(v___x_1880_, 0);
                            crate::leanh::lean_dec(v_unused_1889_);
                            v___x_1882_ = v___x_1880_;
                            v_isShared_1883_ = v_isSharedCheck_1888_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1880_);
                            v___x_1882_ = crate::leanh::lean_box(0);
                            v_isShared_1883_ = v_isSharedCheck_1888_;
                            state = 22;
                            continue;
                        }
                    } else {
                        v_a_1890_ = crate::leanh::lean_ctor_get(v___x_1880_, 0);
                        v_isSharedCheck_1897_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1880_)) as u8;
                        if v_isSharedCheck_1897_ == 0 {
                            v___x_1892_ = v___x_1880_;
                            v_isShared_1893_ = v_isSharedCheck_1897_;
                            state = 24;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1890_);
                            crate::leanh::lean_dec(v___x_1880_);
                            v___x_1892_ = crate::leanh::lean_box(0);
                            v_isShared_1893_ = v_isSharedCheck_1897_;
                            state = 24;
                            continue;
                        }
                    }
                }
            }
            22 => {
                v___x_1884_ = l_main___boxed__const__1;
                if v_isShared_1883_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1882_, 0, v___x_1884_);
                    v___x_1886_ = v___x_1882_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1887_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1884_);
                    v___x_1886_ = v_reuseFailAlloc_1887_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_1886_;
            }
            24 => {
                if v_isShared_1893_ == 0 {
                    v___x_1895_ = v___x_1892_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1896_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
                    v___x_1895_ = v_reuseFailAlloc_1896_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_1895_;
            }
            26 => {
                v___x_1913_ = l_main___closed__22;
                v___x_1914_ = lean_string_append(v___x_1913_, v___y_1904_);
                v___x_1915_ = l_main___closed__23;
                v___x_1916_ = l_main___closed__24;
                v___x_1917_ = l_main___closed__25;
                v___x_1918_ = lean_string_append(v___x_1917_, v___y_1901_);
                crate::leanh::lean_dec_ref(v___y_1901_);
                v___x_1919_ = l_main___closed__26;
                v___x_1920_ = l_main___closed__27;
                v___x_1921_ = lean_string_append(v___x_1920_, v___y_1906_);
                crate::leanh::lean_dec(v___y_1906_);
                v___x_1922_ = l_main___closed__28;
                v___x_1923_ = crate::leanh::lean_unsigned_to_nat(8);
                v___x_1924_ = lean_mk_empty_array_with_capacity(v___x_1923_);
                v___x_1925_ = lean_array_push(v___x_1924_, v___x_1914_);
                v___x_1926_ = lean_array_push(v___x_1925_, v___x_1915_);
                v___x_1927_ = lean_array_push(v___x_1926_, v___x_1916_);
                v___x_1928_ = lean_array_push(v___x_1927_, v___x_1918_);
                v___x_1929_ = lean_array_push(v___x_1928_, v___x_1919_);
                v___x_1930_ = lean_array_push(v___x_1929_, v___x_1921_);
                v___x_1931_ = lean_array_push(v___x_1930_, v___x_1919_);
                v___x_1932_ = lean_array_push(v___x_1931_, v___x_1922_);
                v___x_1933_ = l_Array_append___redArg(v___x_1932_, v___y_1911_);
                crate::leanh::lean_dec(v___y_1911_);
                v___x_1934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__2;
                v___x_1935_ = l_main___closed__29;
                v___x_1936_ = lean_string_append(v___x_1935_, v___y_1905_);
                crate::leanh::lean_dec_ref(v___y_1905_);
                v___x_1937_ = l_main___closed__30;
                v___x_1938_ = lean_array_push(v___y_1900_, v___x_1934_);
                v___x_1939_ = lean_array_push(v___x_1938_, v___x_1936_);
                v___x_1940_ = lean_array_push(v___x_1939_, v___x_1937_);
                v___x_1941_ = lean_array_push(v___x_1940_, v___y_1903_);
                v___x_1942_ = l_Array_append___redArg(v___x_1933_, v___x_1941_);
                crate::leanh::lean_dec_ref(v___x_1941_);
                v___x_1943_ = l_Array_append___redArg(v___x_1942_, v___y_1910_);
                crate::leanh::lean_dec_ref(v___y_1910_);
                v___x_1944_ = l_Array_append___redArg(v___x_1943_, v___y_1912_);
                crate::leanh::lean_dec_ref(v___y_1912_);
                v___x_1945_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_main___closed__31),
                    core::ptr::addr_of_mut!(l_main___closed__31_once),
                    _init_l_main___closed__31,
                );
                v___x_1946_ = lean_array_push(v___x_1945_, v___y_1907_);
                v___x_1947_ = lean_array_push(v___x_1946_, v___y_1908_);
                v___x_1948_ = l_Array_append___redArg(v___x_1944_, v___x_1947_);
                crate::leanh::lean_dec_ref(v___x_1947_);
                v___x_1949_ = l_main___closed__1;
                v___x_1950_ = l_Array_contains___at___00main_spec__1(v_args_1833_, v___x_1949_);
                crate::leanh::lean_dec_ref(v_args_1833_);
                if v___x_1950_ == 0 {
                    v___y_1798_ = v___y_1899_;
                    v___y_1799_ = v___y_1909_;
                    v___y_1800_ = v___y_1902_;
                    v___y_1801_ = v___x_1948_;
                    state = 14;
                    continue;
                } else {
                    v___x_1951_ = l_main___closed__32;
                    v___x_1952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__3;
                    crate::leanh::lean_inc_ref(v___x_1948_);
                    v___x_1953_ = lean_array_to_list(v___x_1948_);
                    v___x_1954_ = l_String_intercalate(v___x_1952_, v___x_1953_);
                    v___x_1955_ = lean_string_append(v___x_1951_, v___x_1954_);
                    crate::leanh::lean_dec_ref(v___x_1954_);
                    v___x_1956_ =
                        l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(
                            v___x_1955_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1956_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1956_, 1);
                        v___y_1798_ = v___y_1899_;
                        v___y_1799_ = v___y_1909_;
                        v___y_1800_ = v___y_1902_;
                        v___y_1801_ = v___x_1948_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1948_);
                        crate::leanh::lean_dec(v___y_1899_);
                        v_a_1957_ = crate::leanh::lean_ctor_get(v___x_1956_, 0);
                        v_isSharedCheck_1964_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1956_)) as u8;
                        if v_isSharedCheck_1964_ == 0 {
                            v___x_1959_ = v___x_1956_;
                            v_isShared_1960_ = v_isSharedCheck_1964_;
                            state = 27;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1957_);
                            crate::leanh::lean_dec(v___x_1956_);
                            v___x_1959_ = crate::leanh::lean_box(0);
                            v_isShared_1960_ = v_isSharedCheck_1964_;
                            state = 27;
                            continue;
                        }
                    }
                }
            }
            27 => {
                if v_isShared_1960_ == 0 {
                    v___x_1962_ = v___x_1959_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1963_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
                    v___x_1962_ = v_reuseFailAlloc_1963_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_1962_;
            }
            29 => {
                v___x_1980_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_1981_ = lean_mk_empty_array_with_capacity(v___x_1980_);
                v___x_1982_ = l_main___closed__37;
                v_sz_1983_ = crate::leanh::lean_usize_once(
                    core::ptr::addr_of_mut!(l_main___closed__38),
                    core::ptr::addr_of_mut!(l_main___closed__38_once),
                    _init_l_main___closed__38,
                );
                crate::leanh::lean_inc_ref(v___y_1975_);
                crate::leanh::lean_inc_ref(v___y_1969_);
                v___x_1984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7(v___y_1969_, v___x_1982_, v_sz_1983_, v___y_1977_, v___y_1975_);
                if crate::leanh::lean_obj_tag(v___x_1984_) == 0 {
                    v_a_1985_ = crate::leanh::lean_ctor_get(v___x_1984_, 0);
                    crate::leanh::lean_inc(v_a_1985_);
                    crate::leanh::lean_dec_ref_known(v___x_1984_, 1);
                    v___x_1986_ = l_main___closed__39;
                    v___x_1987_ = lean_string_append(v___y_1967_, v___x_1986_);
                    v___x_1988_ = l_System_FilePath_pathExists(v___x_1987_);
                    if v___x_1988_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1987_);
                        crate::leanh::lean_inc_ref(v___y_1975_);
                        v___y_1899_ = v___y_1966_;
                        v___y_1900_ = v___x_1981_;
                        v___y_1901_ = v___y_1979_;
                        v___y_1902_ = v___y_1968_;
                        v___y_1903_ = v___y_1969_;
                        v___y_1904_ = v___y_1970_;
                        v___y_1905_ = v___y_1971_;
                        v___y_1906_ = v___y_1972_;
                        v___y_1907_ = v___y_1973_;
                        v___y_1908_ = v___y_1974_;
                        v___y_1909_ = v___y_1976_;
                        v___y_1910_ = v_a_1985_;
                        v___y_1911_ = v___y_1978_;
                        v___y_1912_ = v___y_1975_;
                        state = 26;
                        continue;
                    } else {
                        v___x_1989_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_main___closed__40),
                            core::ptr::addr_of_mut!(l_main___closed__40_once),
                            _init_l_main___closed__40,
                        );
                        v___x_1990_ = lean_array_push(v___x_1989_, v___x_1987_);
                        v___y_1899_ = v___y_1966_;
                        v___y_1900_ = v___x_1981_;
                        v___y_1901_ = v___y_1979_;
                        v___y_1902_ = v___y_1968_;
                        v___y_1903_ = v___y_1969_;
                        v___y_1904_ = v___y_1970_;
                        v___y_1905_ = v___y_1971_;
                        v___y_1906_ = v___y_1972_;
                        v___y_1907_ = v___y_1973_;
                        v___y_1908_ = v___y_1974_;
                        v___y_1909_ = v___y_1976_;
                        v___y_1910_ = v_a_1985_;
                        v___y_1911_ = v___y_1978_;
                        v___y_1912_ = v___x_1990_;
                        state = 26;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1981_);
                    crate::leanh::lean_dec_ref(v___y_1979_);
                    crate::leanh::lean_dec(v___y_1978_);
                    crate::leanh::lean_dec_ref(v___y_1974_);
                    crate::leanh::lean_dec_ref(v___y_1973_);
                    crate::leanh::lean_dec(v___y_1972_);
                    crate::leanh::lean_dec_ref(v___y_1971_);
                    crate::leanh::lean_dec_ref(v___y_1969_);
                    crate::leanh::lean_dec_ref(v___y_1967_);
                    crate::leanh::lean_dec(v___y_1966_);
                    crate::leanh::lean_dec_ref(v_args_1833_);
                    v_a_1991_ = crate::leanh::lean_ctor_get(v___x_1984_, 0);
                    v_isSharedCheck_1998_ = (!crate::leanh::lean_is_exclusive(v___x_1984_)) as u8;
                    if v_isSharedCheck_1998_ == 0 {
                        v___x_1993_ = v___x_1984_;
                        v_isShared_1994_ = v_isSharedCheck_1998_;
                        state = 30;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1991_);
                        crate::leanh::lean_dec(v___x_1984_);
                        v___x_1993_ = crate::leanh::lean_box(0);
                        v_isShared_1994_ = v_isSharedCheck_1998_;
                        state = 30;
                        continue;
                    }
                }
            }
            30 => {
                if v_isShared_1994_ == 0 {
                    v___x_1996_ = v___x_1993_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_1997_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
                    v___x_1996_ = v_reuseFailAlloc_1997_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_1996_;
            }
            32 => {
                if v___y_2014_ == 0 {
                    v___y_1966_ = v___y_2000_;
                    v___y_1967_ = v___y_2001_;
                    v___y_1968_ = v___y_2002_;
                    v___y_1969_ = v___y_2003_;
                    v___y_1970_ = v___y_2004_;
                    v___y_1971_ = v___y_2005_;
                    v___y_1972_ = v___y_2006_;
                    v___y_1973_ = v___y_2007_;
                    v___y_1974_ = v___y_2008_;
                    v___y_1975_ = v___y_2009_;
                    v___y_1976_ = v___y_2010_;
                    v___y_1977_ = v___y_2012_;
                    v___y_1978_ = v___y_2013_;
                    v___y_1979_ = v___y_2011_;
                    state = 29;
                    continue;
                } else {
                    v___x_2015_ = l_main___closed__41;
                    v___x_2016_ = lean_string_append(v___x_2015_, v___y_2011_);
                    crate::leanh::lean_dec_ref(v___y_2011_);
                    v___y_1966_ = v___y_2000_;
                    v___y_1967_ = v___y_2001_;
                    v___y_1968_ = v___y_2002_;
                    v___y_1969_ = v___y_2003_;
                    v___y_1970_ = v___y_2004_;
                    v___y_1971_ = v___y_2005_;
                    v___y_1972_ = v___y_2006_;
                    v___y_1973_ = v___y_2007_;
                    v___y_1974_ = v___y_2008_;
                    v___y_1975_ = v___y_2009_;
                    v___y_1976_ = v___y_2010_;
                    v___y_1977_ = v___y_2012_;
                    v___y_1978_ = v___y_2013_;
                    v___y_1979_ = v___x_2016_;
                    state = 29;
                    continue;
                }
            }
            33 => {
                v___x_2033_ = 48;
                v___x_2034_ = lean_uint32_dec_le(v___x_2033_, v___y_2032_);
                if v___x_2034_ == 0 {
                    v___y_2000_ = v___y_2018_;
                    v___y_2001_ = v___y_2019_;
                    v___y_2002_ = v___y_2020_;
                    v___y_2003_ = v___y_2021_;
                    v___y_2004_ = v___y_2022_;
                    v___y_2005_ = v___y_2023_;
                    v___y_2006_ = v___y_2024_;
                    v___y_2007_ = v___y_2025_;
                    v___y_2008_ = v___y_2026_;
                    v___y_2009_ = v___y_2027_;
                    v___y_2010_ = v___y_2028_;
                    v___y_2011_ = v___y_2029_;
                    v___y_2012_ = v___y_2030_;
                    v___y_2013_ = v___y_2031_;
                    v___y_2014_ = v___x_2034_;
                    state = 32;
                    continue;
                } else {
                    v___x_2035_ = 57;
                    v___x_2036_ = lean_uint32_dec_le(v___y_2032_, v___x_2035_);
                    v___y_2000_ = v___y_2018_;
                    v___y_2001_ = v___y_2019_;
                    v___y_2002_ = v___y_2020_;
                    v___y_2003_ = v___y_2021_;
                    v___y_2004_ = v___y_2022_;
                    v___y_2005_ = v___y_2023_;
                    v___y_2006_ = v___y_2024_;
                    v___y_2007_ = v___y_2025_;
                    v___y_2008_ = v___y_2026_;
                    v___y_2009_ = v___y_2027_;
                    v___y_2010_ = v___y_2028_;
                    v___y_2011_ = v___y_2029_;
                    v___y_2012_ = v___y_2030_;
                    v___y_2013_ = v___y_2031_;
                    v___y_2014_ = v___x_2036_;
                    state = 32;
                    continue;
                }
            }
            34 => {
                crate::leanh::lean_inc(v___y_2038_);
                v___x_2052_ = l_String_mapAux___at___00main_spec__8(v___y_2051_, v___y_2038_);
                v___x_2053_ = lean_string_utf8_byte_size(v___x_2052_);
                v___x_2054_ = lean_nat_dec_eq(v___x_2053_, v___y_2038_);
                if v___x_2054_ == 0 {
                    crate::leanh::lean_inc(v___y_2038_);
                    crate::leanh::lean_inc_ref(v___x_2052_);
                    v___x_2055_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2055_, 0, v___x_2052_);
                    crate::leanh::lean_ctor_set(v___x_2055_, 1, v___y_2038_);
                    crate::leanh::lean_ctor_set(v___x_2055_, 2, v___x_2053_);
                    v___x_2056_ = l_String_Slice_Pos_get_x3f(v___x_2055_, v___y_2038_);
                    crate::leanh::lean_dec_ref_known(v___x_2055_, 3);
                    if crate::leanh::lean_obj_tag(v___x_2056_) == 0 {
                        v___x_2057_ = 65;
                        v___y_2018_ = v___y_2038_;
                        v___y_2019_ = v___y_2039_;
                        v___y_2020_ = v___y_2040_;
                        v___y_2021_ = v___y_2041_;
                        v___y_2022_ = v___y_2042_;
                        v___y_2023_ = v___y_2043_;
                        v___y_2024_ = v___y_2044_;
                        v___y_2025_ = v___y_2045_;
                        v___y_2026_ = v___y_2046_;
                        v___y_2027_ = v___y_2047_;
                        v___y_2028_ = v___y_2048_;
                        v___y_2029_ = v___x_2052_;
                        v___y_2030_ = v___y_2049_;
                        v___y_2031_ = v___y_2050_;
                        v___y_2032_ = v___x_2057_;
                        state = 33;
                        continue;
                    } else {
                        v_val_2058_ = crate::leanh::lean_ctor_get(v___x_2056_, 0);
                        crate::leanh::lean_inc(v_val_2058_);
                        crate::leanh::lean_dec_ref_known(v___x_2056_, 1);
                        v___x_2059_ = crate::leanh::lean_unbox_uint32(v_val_2058_);
                        crate::leanh::lean_dec(v_val_2058_);
                        v___y_2018_ = v___y_2038_;
                        v___y_2019_ = v___y_2039_;
                        v___y_2020_ = v___y_2040_;
                        v___y_2021_ = v___y_2041_;
                        v___y_2022_ = v___y_2042_;
                        v___y_2023_ = v___y_2043_;
                        v___y_2024_ = v___y_2044_;
                        v___y_2025_ = v___y_2045_;
                        v___y_2026_ = v___y_2046_;
                        v___y_2027_ = v___y_2047_;
                        v___y_2028_ = v___y_2048_;
                        v___y_2029_ = v___x_2052_;
                        v___y_2030_ = v___y_2049_;
                        v___y_2031_ = v___y_2050_;
                        v___y_2032_ = v___x_2059_;
                        state = 33;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2052_);
                    v___x_2060_ = l_main___closed__42;
                    v___y_1966_ = v___y_2038_;
                    v___y_1967_ = v___y_2039_;
                    v___y_1968_ = v___y_2040_;
                    v___y_1969_ = v___y_2041_;
                    v___y_1970_ = v___y_2042_;
                    v___y_1971_ = v___y_2043_;
                    v___y_1972_ = v___y_2044_;
                    v___y_1973_ = v___y_2045_;
                    v___y_1974_ = v___y_2046_;
                    v___y_1975_ = v___y_2047_;
                    v___y_1976_ = v___y_2048_;
                    v___y_1977_ = v___y_2049_;
                    v___y_1978_ = v___y_2050_;
                    v___y_1979_ = v___x_2060_;
                    state = 29;
                    continue;
                }
            }
            35 => {
                crate::leanh::lean_inc_ref(v___y_2072_);
                v___x_2075_ = l_System_FilePath_fileStem(v___y_2072_);
                if crate::leanh::lean_obj_tag(v___x_2075_) == 0 {
                    v___x_2076_ = l_main___closed__42;
                    v___y_2038_ = v___y_2063_;
                    v___y_2039_ = v___y_2065_;
                    v___y_2040_ = v___y_2066_;
                    v___y_2041_ = v___y_2067_;
                    v___y_2042_ = v___y_2068_;
                    v___y_2043_ = v_rlib_2074_;
                    v___y_2044_ = v___y_2071_;
                    v___y_2045_ = v___y_2073_;
                    v___y_2046_ = v___y_2072_;
                    v___y_2047_ = v___y_2062_;
                    v___y_2048_ = v___y_2064_;
                    v___y_2049_ = v___y_2069_;
                    v___y_2050_ = v___y_2070_;
                    v___y_2051_ = v___x_2076_;
                    state = 34;
                    continue;
                } else {
                    v_val_2077_ = crate::leanh::lean_ctor_get(v___x_2075_, 0);
                    crate::leanh::lean_inc(v_val_2077_);
                    crate::leanh::lean_dec_ref_known(v___x_2075_, 1);
                    v___y_2038_ = v___y_2063_;
                    v___y_2039_ = v___y_2065_;
                    v___y_2040_ = v___y_2066_;
                    v___y_2041_ = v___y_2067_;
                    v___y_2042_ = v___y_2068_;
                    v___y_2043_ = v_rlib_2074_;
                    v___y_2044_ = v___y_2071_;
                    v___y_2045_ = v___y_2073_;
                    v___y_2046_ = v___y_2072_;
                    v___y_2047_ = v___y_2062_;
                    v___y_2048_ = v___y_2064_;
                    v___y_2049_ = v___y_2069_;
                    v___y_2050_ = v___y_2070_;
                    v___y_2051_ = v_val_2077_;
                    state = 34;
                    continue;
                }
            }
            36 => {
                v___x_2090_ = l_main___closed__43;
                crate::leanh::lean_inc_ref(v___y_2082_);
                v___x_2091_ = lean_string_append(v___y_2082_, v___x_2090_);
                v___x_2092_ = l_main___closed__44;
                crate::leanh::lean_inc_ref(v___x_2091_);
                v___x_2093_ = lean_string_append(v___x_2091_, v___x_2092_);
                v___x_2094_ = l_System_FilePath_pathExists(v___x_2093_);
                if v___x_2094_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2093_);
                    v___x_2095_ = l_main___closed__45;
                    crate::leanh::lean_inc_ref(v___x_2091_);
                    v___x_2096_ = lean_string_append(v___x_2091_, v___x_2095_);
                    v___y_2062_ = v___y_2079_;
                    v___y_2063_ = v___y_2080_;
                    v___y_2064_ = v___y_2081_;
                    v___y_2065_ = v___y_2082_;
                    v___y_2066_ = v___y_2083_;
                    v___y_2067_ = v___x_2091_;
                    v___y_2068_ = v___y_2084_;
                    v___y_2069_ = v___y_2085_;
                    v___y_2070_ = v___y_2087_;
                    v___y_2071_ = v___y_2086_;
                    v___y_2072_ = v___y_2088_;
                    v___y_2073_ = v___y_2089_;
                    v_rlib_2074_ = v___x_2096_;
                    state = 35;
                    continue;
                } else {
                    v___y_2062_ = v___y_2079_;
                    v___y_2063_ = v___y_2080_;
                    v___y_2064_ = v___y_2081_;
                    v___y_2065_ = v___y_2082_;
                    v___y_2066_ = v___y_2083_;
                    v___y_2067_ = v___x_2091_;
                    v___y_2068_ = v___y_2084_;
                    v___y_2069_ = v___y_2085_;
                    v___y_2070_ = v___y_2087_;
                    v___y_2071_ = v___y_2086_;
                    v___y_2072_ = v___y_2088_;
                    v___y_2073_ = v___y_2089_;
                    v_rlib_2074_ = v___x_2093_;
                    state = 35;
                    continue;
                }
            }
            37 => {
                crate::leanh::lean_inc_ref(v___y_2099_);
                v___x_2110_ = lean_string_append(v___y_2099_, v___y_2109_);
                crate::leanh::lean_dec_ref(v___y_2109_);
                v___x_2111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__7___closed__1;
                v___x_2112_ = lean_string_append(v___x_2110_, v___x_2111_);
                v___y_2079_ = v___y_2098_;
                v___y_2080_ = v___y_2100_;
                v___y_2081_ = v___y_2102_;
                v___y_2082_ = v___y_2101_;
                v___y_2083_ = v___y_2103_;
                v___y_2084_ = v___y_2104_;
                v___y_2085_ = v___y_2105_;
                v___y_2086_ = v___y_2107_;
                v___y_2087_ = v___y_2106_;
                v___y_2088_ = v___y_2108_;
                v___y_2089_ = v___x_2112_;
                state = 36;
                continue;
            }
            38 => {
                if crate::leanh::lean_obj_tag(v___y_2115_) == 0 {
                    v___x_2125_ = l_main___closed__46;
                    v___x_2126_ = lean_string_dec_eq(v___y_2124_, v___x_2125_);
                    if v___x_2126_ == 0 {
                        v___x_2127_ = l_panic___at___00main_spec__9___closed__0;
                        crate::leanh::lean_inc_ref(v___y_2123_);
                        v___x_2128_ = l_System_FilePath_withExtension(v___y_2123_, v___x_2127_);
                        v___y_2079_ = v___y_2114_;
                        v___y_2080_ = v___y_2116_;
                        v___y_2081_ = v___y_2118_;
                        v___y_2082_ = v___y_2117_;
                        v___y_2083_ = v___y_2119_;
                        v___y_2084_ = v___y_2124_;
                        v___y_2085_ = v___y_2120_;
                        v___y_2086_ = v___y_2122_;
                        v___y_2087_ = v___y_2121_;
                        v___y_2088_ = v___y_2123_;
                        v___y_2089_ = v___x_2128_;
                        state = 36;
                        continue;
                    } else {
                        v___x_2129_ = l_main___closed__47;
                        crate::leanh::lean_inc_ref(v___y_2123_);
                        v___x_2130_ = l_System_FilePath_fileStem(v___y_2123_);
                        if crate::leanh::lean_obj_tag(v___x_2130_) == 0 {
                            v___x_2131_ = l_main___closed__42;
                            v___y_2098_ = v___y_2114_;
                            v___y_2099_ = v___x_2129_;
                            v___y_2100_ = v___y_2116_;
                            v___y_2101_ = v___y_2117_;
                            v___y_2102_ = v___y_2118_;
                            v___y_2103_ = v___y_2119_;
                            v___y_2104_ = v___y_2124_;
                            v___y_2105_ = v___y_2120_;
                            v___y_2106_ = v___y_2121_;
                            v___y_2107_ = v___y_2122_;
                            v___y_2108_ = v___y_2123_;
                            v___y_2109_ = v___x_2131_;
                            state = 37;
                            continue;
                        } else {
                            v_val_2132_ = crate::leanh::lean_ctor_get(v___x_2130_, 0);
                            crate::leanh::lean_inc(v_val_2132_);
                            crate::leanh::lean_dec_ref_known(v___x_2130_, 1);
                            v___y_2098_ = v___y_2114_;
                            v___y_2099_ = v___x_2129_;
                            v___y_2100_ = v___y_2116_;
                            v___y_2101_ = v___y_2117_;
                            v___y_2102_ = v___y_2118_;
                            v___y_2103_ = v___y_2119_;
                            v___y_2104_ = v___y_2124_;
                            v___y_2105_ = v___y_2120_;
                            v___y_2106_ = v___y_2121_;
                            v___y_2107_ = v___y_2122_;
                            v___y_2108_ = v___y_2123_;
                            v___y_2109_ = v_val_2132_;
                            state = 37;
                            continue;
                        }
                    }
                } else {
                    v_val_2133_ = crate::leanh::lean_ctor_get(v___y_2115_, 0);
                    crate::leanh::lean_inc(v_val_2133_);
                    crate::leanh::lean_dec_ref_known(v___y_2115_, 1);
                    v___y_2079_ = v___y_2114_;
                    v___y_2080_ = v___y_2116_;
                    v___y_2081_ = v___y_2118_;
                    v___y_2082_ = v___y_2117_;
                    v___y_2083_ = v___y_2119_;
                    v___y_2084_ = v___y_2124_;
                    v___y_2085_ = v___y_2120_;
                    v___y_2086_ = v___y_2122_;
                    v___y_2087_ = v___y_2121_;
                    v___y_2088_ = v___y_2123_;
                    v___y_2089_ = v_val_2133_;
                    state = 36;
                    continue;
                }
            }
            39 => {
                v___x_2136_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2137_ = lean_array_get_size(v_args_1833_);
                v___x_2138_ = lean_nat_dec_lt(v___x_2136_, v___x_2137_);
                if v___x_2138_ == 0 {
                    v___y_1863_ = v___x_2136_;
                    v___y_1864_ = v_root_2135_;
                    state = 21;
                    continue;
                } else {
                    if v___x_2138_ == 0 {
                        v___y_1863_ = v___x_2136_;
                        v___y_1864_ = v_root_2135_;
                        state = 21;
                        continue;
                    } else {
                        v___x_2139_ = 0usize;
                        v___x_2140_ = lean_usize_of_nat(v___x_2137_);
                        v___x_2141_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__5(v_args_1833_, v___x_2139_, v___x_2140_);
                        if v___x_2141_ == 0 {
                            v___y_1863_ = v___x_2136_;
                            v___y_1864_ = v_root_2135_;
                            state = 21;
                            continue;
                        } else {
                            v___x_2142_ = crate::leanh::lean_box(0);
                            v___x_2143_ = l_main___closed__48;
                            v___x_2144_ = l_main___closed__49;
                            crate::leanh::lean_inc_ref(v_args_1833_);
                            v___x_2145_ = lean_array_to_list(v_args_1833_);
                            v___x_2146_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2146_, 0, v___x_2144_);
                            crate::leanh::lean_ctor_set(v___x_2146_, 1, v___x_2145_);
                            v___x_2147_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2147_, 0, v___x_2143_);
                            crate::leanh::lean_ctor_set(v___x_2147_, 1, v___x_2146_);
                            v___x_2148_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2148_, 0, v___x_2142_);
                            crate::leanh::lean_ctor_set(v___x_2148_, 1, v___x_2147_);
                            v___x_2149_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2149_, 0, v___x_2142_);
                            crate::leanh::lean_ctor_set(v___x_2149_, 1, v___x_2148_);
                            v___x_2150_ = l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg(v___x_2141_, v___x_2149_);
                            if crate::leanh::lean_obj_tag(v___x_2150_) == 0 {
                                v_a_2151_ = crate::leanh::lean_ctor_get(v___x_2150_, 0);
                                crate::leanh::lean_inc(v_a_2151_);
                                crate::leanh::lean_dec_ref_known(v___x_2150_, 1);
                                v_snd_2152_ = crate::leanh::lean_ctor_get(v_a_2151_, 1);
                                crate::leanh::lean_inc(v_snd_2152_);
                                v_fst_2153_ = crate::leanh::lean_ctor_get(v_snd_2152_, 0);
                                crate::leanh::lean_inc(v_fst_2153_);
                                if crate::leanh::lean_obj_tag(v_fst_2153_) == 1 {
                                    v_fst_2154_ = crate::leanh::lean_ctor_get(v_a_2151_, 0);
                                    crate::leanh::lean_inc(v_fst_2154_);
                                    crate::leanh::lean_dec(v_a_2151_);
                                    v_snd_2155_ = crate::leanh::lean_ctor_get(v_snd_2152_, 1);
                                    crate::leanh::lean_inc(v_snd_2155_);
                                    crate::leanh::lean_dec(v_snd_2152_);
                                    v_val_2156_ = crate::leanh::lean_ctor_get(v_fst_2153_, 0);
                                    crate::leanh::lean_inc(v_val_2156_);
                                    crate::leanh::lean_dec_ref_known(v_fst_2153_, 1);
                                    v___x_2157_ = l_main___closed__12;
                                    v___x_2158_ = l_Array_contains___at___00main_spec__1(
                                        v_args_1833_,
                                        v___x_2157_,
                                    );
                                    if v___x_2158_ == 0 {
                                        v_snd_2159_ = crate::leanh::lean_ctor_get(v_snd_2155_, 1);
                                        crate::leanh::lean_inc(v_snd_2159_);
                                        v_fst_2160_ = crate::leanh::lean_ctor_get(v_snd_2155_, 0);
                                        crate::leanh::lean_inc(v_fst_2160_);
                                        crate::leanh::lean_dec(v_snd_2155_);
                                        v_fst_2161_ = crate::leanh::lean_ctor_get(v_snd_2159_, 0);
                                        crate::leanh::lean_inc(v_fst_2161_);
                                        crate::leanh::lean_dec(v_snd_2159_);
                                        v___x_2162_ = l_main___closed__50;
                                        v___x_2163_ = l_Array_contains___at___00main_spec__1(
                                            v_args_1833_,
                                            v___x_2162_,
                                        );
                                        if v___x_2163_ == 0 {
                                            v___x_2164_ = l_main___closed__51;
                                            v___y_2114_ = v___x_2144_;
                                            v___y_2115_ = v_fst_2154_;
                                            v___y_2116_ = v___x_2136_;
                                            v___y_2117_ = v_root_2135_;
                                            v___y_2118_ = v___x_2141_;
                                            v___y_2119_ = v___x_2158_;
                                            v___y_2120_ = v___x_2139_;
                                            v___y_2121_ = v_fst_2161_;
                                            v___y_2122_ = v_fst_2160_;
                                            v___y_2123_ = v_val_2156_;
                                            v___y_2124_ = v___x_2164_;
                                            state = 38;
                                            continue;
                                        } else {
                                            v___x_2165_ = l_main___closed__46;
                                            v___y_2114_ = v___x_2144_;
                                            v___y_2115_ = v_fst_2154_;
                                            v___y_2116_ = v___x_2136_;
                                            v___y_2117_ = v_root_2135_;
                                            v___y_2118_ = v___x_2141_;
                                            v___y_2119_ = v___x_2158_;
                                            v___y_2120_ = v___x_2139_;
                                            v___y_2121_ = v_fst_2161_;
                                            v___y_2122_ = v_fst_2160_;
                                            v___y_2123_ = v_val_2156_;
                                            v___y_2124_ = v___x_2165_;
                                            state = 38;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_val_2156_);
                                        crate::leanh::lean_dec(v_snd_2155_);
                                        crate::leanh::lean_dec(v_fst_2154_);
                                        crate::leanh::lean_dec_ref(v_root_2135_);
                                        crate::leanh::lean_dec_ref(v_args_1833_);
                                        v___x_2166_ = l_main___closed__52;
                                        v___x_2167_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v___x_2166_);
                                        if crate::leanh::lean_obj_tag(v___x_2167_) == 0 {
                                            v_isSharedCheck_2175_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2167_))
                                                    as u8;
                                            if v_isSharedCheck_2175_ == 0 {
                                                v_unused_2176_ =
                                                    crate::leanh::lean_ctor_get(v___x_2167_, 0);
                                                crate::leanh::lean_dec(v_unused_2176_);
                                                v___x_2169_ = v___x_2167_;
                                                v_isShared_2170_ = v_isSharedCheck_2175_;
                                                state = 40;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v___x_2167_);
                                                v___x_2169_ = crate::leanh::lean_box(0);
                                                v_isShared_2170_ = v_isSharedCheck_2175_;
                                                state = 40;
                                                continue;
                                            }
                                        } else {
                                            v_a_2177_ = crate::leanh::lean_ctor_get(v___x_2167_, 0);
                                            v_isSharedCheck_2184_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2167_))
                                                    as u8;
                                            if v_isSharedCheck_2184_ == 0 {
                                                v___x_2179_ = v___x_2167_;
                                                v_isShared_2180_ = v_isSharedCheck_2184_;
                                                state = 42;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2177_);
                                                crate::leanh::lean_dec(v___x_2167_);
                                                v___x_2179_ = crate::leanh::lean_box(0);
                                                v_isShared_2180_ = v_isSharedCheck_2184_;
                                                state = 42;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_fst_2153_);
                                    crate::leanh::lean_dec(v_snd_2152_);
                                    crate::leanh::lean_dec(v_a_2151_);
                                    crate::leanh::lean_dec_ref(v_root_2135_);
                                    crate::leanh::lean_dec_ref(v_args_1833_);
                                    v___x_2185_ = l_main___closed__53;
                                    v___x_2186_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v___x_2185_);
                                    if crate::leanh::lean_obj_tag(v___x_2186_) == 0 {
                                        v_isSharedCheck_2194_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2186_)) as u8;
                                        if v_isSharedCheck_2194_ == 0 {
                                            v_unused_2195_ =
                                                crate::leanh::lean_ctor_get(v___x_2186_, 0);
                                            crate::leanh::lean_dec(v_unused_2195_);
                                            v___x_2188_ = v___x_2186_;
                                            v_isShared_2189_ = v_isSharedCheck_2194_;
                                            state = 44;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v___x_2186_);
                                            v___x_2188_ = crate::leanh::lean_box(0);
                                            v_isShared_2189_ = v_isSharedCheck_2194_;
                                            state = 44;
                                            continue;
                                        }
                                    } else {
                                        v_a_2196_ = crate::leanh::lean_ctor_get(v___x_2186_, 0);
                                        v_isSharedCheck_2203_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2186_)) as u8;
                                        if v_isSharedCheck_2203_ == 0 {
                                            v___x_2198_ = v___x_2186_;
                                            v_isShared_2199_ = v_isSharedCheck_2203_;
                                            state = 46;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2196_);
                                            crate::leanh::lean_dec(v___x_2186_);
                                            v___x_2198_ = crate::leanh::lean_box(0);
                                            v_isShared_2199_ = v_isSharedCheck_2203_;
                                            state = 46;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_root_2135_);
                                crate::leanh::lean_dec_ref(v_args_1833_);
                                v_a_2204_ = crate::leanh::lean_ctor_get(v___x_2150_, 0);
                                v_isSharedCheck_2211_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2150_)) as u8;
                                if v_isSharedCheck_2211_ == 0 {
                                    v___x_2206_ = v___x_2150_;
                                    v_isShared_2207_ = v_isSharedCheck_2211_;
                                    state = 48;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2204_);
                                    crate::leanh::lean_dec(v___x_2150_);
                                    v___x_2206_ = crate::leanh::lean_box(0);
                                    v_isShared_2207_ = v_isSharedCheck_2211_;
                                    state = 48;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            40 => {
                v___x_2171_ = l_main___boxed__const__1;
                if v_isShared_2170_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2169_, 0, v___x_2171_);
                    v___x_2173_ = v___x_2169_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_2174_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2171_);
                    v___x_2173_ = v_reuseFailAlloc_2174_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_2173_;
            }
            42 => {
                if v_isShared_2180_ == 0 {
                    v___x_2182_ = v___x_2179_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_2183_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
                    v___x_2182_ = v_reuseFailAlloc_2183_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_2182_;
            }
            44 => {
                v___x_2190_ = l_main___boxed__const__1;
                if v_isShared_2189_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2188_, 0, v___x_2190_);
                    v___x_2192_ = v___x_2188_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_2193_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
                    v___x_2192_ = v_reuseFailAlloc_2193_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_2192_;
            }
            46 => {
                if v_isShared_2199_ == 0 {
                    v___x_2201_ = v___x_2198_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_2202_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
                    v___x_2201_ = v_reuseFailAlloc_2202_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_2201_;
            }
            48 => {
                if v_isShared_2207_ == 0 {
                    v___x_2209_ = v___x_2206_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_2210_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
                    v___x_2209_ = v_reuseFailAlloc_2210_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_2209_;
            }
            50 => {
                if v_isShared_2221_ == 0 {
                    v___x_2223_ = v___x_2220_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_2224_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
                    v___x_2223_ = v_reuseFailAlloc_2224_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                return v___x_2223_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_main___boxed(
    mut v_args_2227_: *mut crate::leanh::LeanObject,
    mut v_a_2228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2229_ = _lean_main(v_args_2227_);
    return v_res_2229_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00main_spec__6(
    mut v___x_2230_: u8,
    mut v_inst_2231_: *mut crate::leanh::LeanObject,
    mut v_a_2232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2234_ = l___private_Init_While_0__whileM_erased___at___00main_spec__6___redArg(
        v___x_2230_,
        v_a_2232_,
    );
    return v___x_2234_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00main_spec__6___boxed(
    mut v___x_2235_: *mut crate::leanh::LeanObject,
    mut v_inst_2236_: *mut crate::leanh::LeanObject,
    mut v_a_2237_: *mut crate::leanh::LeanObject,
    mut v___y_2238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_14114__boxed_2239_: u8 = 0;
    let mut v_res_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_14114__boxed_2239_ = (crate::leanh::lean_unbox(v___x_2235_) as u8);
    v_res_2240_ = l___private_Init_While_0__whileM_erased___at___00main_spec__6(
        v___x_14114__boxed_2239_,
        v_inst_2236_,
        v_a_2237_,
    );
    return v_res_2240_;
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Leanc(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Lean_Compiler_FFI(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__4___boxed__const__1 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__4___boxed__const__1();
    crate::leanh::lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__4___closed__4___boxed__const__1);
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
    let res = initialize_Leanc(1 /* builtin */);
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
