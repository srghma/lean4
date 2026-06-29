// Lean compiler output
// Module: Init.System.FilePath
// Imports: Init.Data.String.Modify Init.Data.String.Search Init.Data.ToString.Basic Init.Data.Iterators.Consumers.Collect Init.System.Platform Init.Data.String.Length Init.Data.Iterators.Combinators.Take Init.Data.Iterators.Consumers.Access
use crate::r#gen::Init::Data::Iterators::Combinators::Take::{
    initialize_Init_Data_Iterators_Combinators_Take,
    runtime_initialize_Init_Data_Iterators_Combinators_Take,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Access::{
    initialize_Init_Data_Iterators_Consumers_Access,
    runtime_initialize_Init_Data_Iterators_Consumers_Access,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Collect::{
    initialize_Init_Data_Iterators_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Collect,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Option::Basic::l_Option_instDecidableEq___redArg;
use crate::r#gen::Init::Data::Repr::{l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::Data::String::Basic::{
    l_String_Slice_Pos_get_x3f, l_String_Slice_Pos_next_x3f, l_String_Slice_Pos_next_x21,
    l_String_Slice_Pos_nextn, l_String_Slice_pos_x21,
};
use crate::r#gen::Init::Data::String::Defs::{
    l_String_instDecidableEqPos___boxed, l_String_intercalate,
};
use crate::r#gen::Init::Data::String::FindPos::{
    l_String_Slice_posGE___redArg, l_String_Slice_posLE,
};
use crate::r#gen::Init::Data::String::Iterate::l_String_Slice_positions;
use crate::r#gen::Init::Data::String::Length::{
    initialize_Init_Data_String_Length, runtime_initialize_Init_Data_String_Length,
};
use crate::r#gen::Init::Data::String::Modify::{
    initialize_Init_Data_String_Modify, runtime_initialize_Init_Data_String_Modify,
};
use crate::r#gen::Init::Data::String::Pattern::String::l_String_Slice_Pattern_ForwardSliceSearcher_buildTable;
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_toString;
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Data::ToString::Basic::{
    initialize_Init_Data_ToString_Basic, runtime_initialize_Init_Data_ToString_Basic,
};
use crate::r#gen::Init::Prelude::{l_Char_utf8Size, l_List_lengthTR___redArg};
use crate::r#gen::Init::System::Platform::{
    initialize_Init_System_Platform, l_System_Platform_isWindows,
    runtime_initialize_Init_System_Platform,
};
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_extract, lean_string_utf8_get, lean_string_utf8_get_fast,
    lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Modify::lean_string_utf8_set;
use crate::lean_imports_rs::Init::Data::String::PosRaw::lean_string_get_byte_fast;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_uint32_add;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_push, lean_array_to_list, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_dec_eq, lean_string_hash,
    lean_string_utf8_byte_size, lean_uint8_dec_eq, lean_uint32_dec_eq, lean_uint32_dec_le,
    lean_uint64_mix_hash,
};
pub static l_System_instInhabitedFilePath_default___closed__0_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
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
static mut l_System_instInhabitedFilePath_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_System_instInhabitedFilePath_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_System_instInhabitedFilePath_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_System_instInhabitedFilePath_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_System_instInhabitedFilePath: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_System_instInhabitedFilePath_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_System_instHashableFilePath___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_System_instHashableFilePath_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_System_instHashableFilePath___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_System_instHashableFilePath___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_System_instHashableFilePath: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_System_instHashableFilePath___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_System_instReprFilePath___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    13,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [70, 105, 108, 101, 80, 97, 116, 104, 46, 109, 107, 32, 0],
};
static mut l_System_instReprFilePath___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_System_instReprFilePath___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_System_instReprFilePath___lam__0___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_System_instReprFilePath___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_System_instReprFilePath___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_System_instReprFilePath___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_System_instReprFilePath___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_System_instReprFilePath___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_System_instReprFilePath___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_System_instReprFilePath___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_System_instReprFilePath: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_System_instReprFilePath___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_System_instToStringFilePath___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_System_instToStringFilePath___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_System_instToStringFilePath___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_System_instToStringFilePath___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_System_instToStringFilePath: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_System_instToStringFilePath___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_System_FilePath_pathSeparator: u32 = 0;
pub static mut l_System_FilePath_pathSeparators___closed__0___boxed__const__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_System_FilePath_pathSeparators___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_System_FilePath_pathSeparators___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_System_FilePath_pathSeparators___closed__1___boxed__const__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_System_FilePath_pathSeparators___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_System_FilePath_pathSeparators___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_System_FilePath_pathSeparators: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_System_FilePath_extSeparator: u32 = 0;
pub static l_System_FilePath_exeExtension___closed__0_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [101, 120, 101, 0],
    };
static mut l_System_FilePath_exeExtension___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_System_FilePath_exeExtension___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_System_FilePath_exeExtension: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_System_FilePath_normalize___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_System_FilePath_normalize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_System_FilePath_normalize___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_System_FilePath_normalize___closed__1: u8 = 0;
pub static mut l_System_FilePath_isAbsolute___closed__0___boxed__const__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_System_FilePath_isAbsolute___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_System_FilePath_isAbsolute___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_System_FilePath_join___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_System_FilePath_join___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_System_FilePath_instDiv___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_System_FilePath_join as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_System_FilePath_instDiv___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_System_FilePath_instDiv___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_System_FilePath_instDiv: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_System_FilePath_instDiv___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_System_FilePath_instHDivString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_System_FilePath_instDiv___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_System_FilePath_fileName___closed__0_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [46, 46, 0],
    };
static mut l_System_FilePath_fileName___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_System_FilePath_fileName___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_System_FilePath_fileName___closed__1_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [46, 0],
    };
static mut l_System_FilePath_fileName___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_System_FilePath_fileName___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_System_FilePath_extension___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_System_FilePath_extension___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1: u8 = 0;
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__6_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_System_FilePath_components___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_System_FilePath_components___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_System_FilePath_components___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_System_instCoeStringFilePath___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_System_instCoeStringFilePath___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_System_instCoeStringFilePath___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_System_instCoeStringFilePath___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_System_instCoeStringFilePath: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_System_instCoeStringFilePath___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_System_SearchPath_separator: u32 = 0;
pub static l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_System_SearchPath_toString___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_System_SearchPath_toString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_System_instDecidableEqFilePath_decEq(
    mut v_x_861_: *mut crate::leanh::LeanObject,
    mut v_x_862_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_863_: u8 = 0;
    v___x_863_ = lean_string_dec_eq(v_x_861_, v_x_862_);
    return v___x_863_;
}
pub unsafe fn l_System_instDecidableEqFilePath_decEq___boxed(
    mut v_x_864_: *mut crate::leanh::LeanObject,
    mut v_x_865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_866_: u8 = 0;
    let mut v_r_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_866_ = l_System_instDecidableEqFilePath_decEq(v_x_864_, v_x_865_);
    crate::leanh::lean_dec_ref(v_x_865_);
    crate::leanh::lean_dec_ref(v_x_864_);
    v_r_867_ = crate::leanh::lean_box((v_res_866_) as usize);
    return v_r_867_;
}
pub unsafe fn l_System_instDecidableEqFilePath(
    mut v_x_868_: *mut crate::leanh::LeanObject,
    mut v_x_869_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_870_: u8 = 0;
    v___x_870_ = lean_string_dec_eq(v_x_868_, v_x_869_);
    return v___x_870_;
}
pub unsafe fn l_System_instDecidableEqFilePath___boxed(
    mut v_x_871_: *mut crate::leanh::LeanObject,
    mut v_x_872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_873_: u8 = 0;
    let mut v_r_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_873_ = l_System_instDecidableEqFilePath(v_x_871_, v_x_872_);
    crate::leanh::lean_dec_ref(v_x_872_);
    crate::leanh::lean_dec_ref(v_x_871_);
    v_r_874_ = crate::leanh::lean_box((v_res_873_) as usize);
    return v_r_874_;
}
pub unsafe fn l_System_instHashableFilePath_hash(
    mut v_x_875_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___x_876_: u64 = 0;
    let mut v___x_877_: u64 = 0;
    let mut v___x_878_: u64 = 0;
    v___x_876_ = 0u64;
    v___x_877_ = lean_string_hash(v_x_875_);
    v___x_878_ = lean_uint64_mix_hash(v___x_876_, v___x_877_);
    return v___x_878_;
}
pub unsafe fn l_System_instHashableFilePath_hash___boxed(
    mut v_x_879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_880_: u64 = 0;
    let mut v_r_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_880_ = l_System_instHashableFilePath_hash(v_x_879_);
    crate::leanh::lean_dec_ref(v_x_879_);
    v_r_881_ = crate::leanh::lean_box_uint64(v_res_880_);
    return v_r_881_;
}
pub unsafe fn l_System_instReprFilePath___lam__0(
    mut v_p_887_: *mut crate::leanh::LeanObject,
    mut v___y_888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_889_ = l_System_instReprFilePath___lam__0___closed__1;
    v___x_890_ = l_String_quote(v_p_887_);
    v___x_891_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_891_, 0, v___x_890_);
    v___x_892_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_892_, 0, v___x_889_);
    crate::leanh::lean_ctor_set(v___x_892_, 1, v___x_891_);
    v___x_893_ = l_Repr_addAppParen(v___x_892_, v___y_888_);
    return v___x_893_;
}
pub unsafe fn l_System_instReprFilePath___lam__0___boxed(
    mut v_p_894_: *mut crate::leanh::LeanObject,
    mut v___y_895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_896_ = l_System_instReprFilePath___lam__0(v_p_894_, v___y_895_);
    crate::leanh::lean_dec(v___y_895_);
    return v_res_896_;
}
pub unsafe fn l_System_instToStringFilePath___lam__0(
    mut v_p_899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_p_899_);
    return v_p_899_;
}
pub unsafe fn l_System_instToStringFilePath___lam__0___boxed(
    mut v_p_900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_901_ = l_System_instToStringFilePath___lam__0(v_p_900_);
    crate::leanh::lean_dec_ref(v_p_900_);
    return v_res_901_;
}
pub unsafe fn _init_l_System_FilePath_pathSeparator() -> u32 {
    let mut v___x_904_: u8 = 0;
    v___x_904_ = l_System_Platform_isWindows;
    if v___x_904_ == 0 {
        let mut v___x_905_: u32 = 0;
        v___x_905_ = 47;
        return v___x_905_;
    } else {
        let mut v___x_906_: u32 = 0;
        v___x_906_ = 92;
        return v___x_906_;
    }
}
pub unsafe fn _init_l_System_FilePath_pathSeparators___closed__0___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_907_: u32 = 0;
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_907_ = 47;
    v___x_908_ = crate::leanh::lean_box_uint32(v___x_907_);
    return v___x_908_;
}
pub unsafe fn _init_l_System_FilePath_pathSeparators___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_909_ = crate::leanh::lean_box(0);
    v___x_910_ = l_System_FilePath_pathSeparators___closed__0___boxed__const__1;
    v___x_911_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_911_, 0, v___x_910_);
    crate::leanh::lean_ctor_set(v___x_911_, 1, v___x_909_);
    return v___x_911_;
}
pub unsafe fn _init_l_System_FilePath_pathSeparators___closed__1___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_912_: u32 = 0;
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_912_ = 92;
    v___x_913_ = crate::leanh::lean_box_uint32(v___x_912_);
    return v___x_913_;
}
pub unsafe fn _init_l_System_FilePath_pathSeparators___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_914_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_FilePath_pathSeparators___closed__0),
        core::ptr::addr_of_mut!(l_System_FilePath_pathSeparators___closed__0_once),
        _init_l_System_FilePath_pathSeparators___closed__0,
    );
    v___x_915_ = l_System_FilePath_pathSeparators___closed__1___boxed__const__1;
    v___x_916_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_916_, 0, v___x_915_);
    crate::leanh::lean_ctor_set(v___x_916_, 1, v___x_914_);
    return v___x_916_;
}
pub unsafe fn _init_l_System_FilePath_pathSeparators() -> *mut crate::leanh::LeanObject {
    let mut v___x_917_: u8 = 0;
    v___x_917_ = l_System_Platform_isWindows;
    if v___x_917_ == 0 {
        let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_918_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_System_FilePath_pathSeparators___closed__0),
            core::ptr::addr_of_mut!(l_System_FilePath_pathSeparators___closed__0_once),
            _init_l_System_FilePath_pathSeparators___closed__0,
        );
        return v___x_918_;
    } else {
        let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_919_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_System_FilePath_pathSeparators___closed__1),
            core::ptr::addr_of_mut!(l_System_FilePath_pathSeparators___closed__1_once),
            _init_l_System_FilePath_pathSeparators___closed__1,
        );
        return v___x_919_;
    }
}
pub unsafe fn _init_l_System_FilePath_extSeparator() -> u32 {
    let mut v___x_920_: u32 = 0;
    v___x_920_ = 46;
    return v___x_920_;
}
pub unsafe fn _init_l_System_FilePath_exeExtension() -> *mut crate::leanh::LeanObject {
    let mut v___x_922_: u8 = 0;
    v___x_922_ = l_System_Platform_isWindows;
    if v___x_922_ == 0 {
        let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_923_ = l_System_instInhabitedFilePath_default___closed__0;
        return v___x_923_;
    } else {
        let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_924_ = l_System_FilePath_exeExtension___closed__0;
        return v___x_924_;
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(
    mut v___x_925_: *mut crate::leanh::LeanObject,
    mut v___x_926_: *mut crate::leanh::LeanObject,
    mut v_a_927_: *mut crate::leanh::LeanObject,
    mut v_b_928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_countdown_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inner_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_933_: u8 = 0;
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: u8 = 0;
    let mut v_startInclusive_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: u8 = 0;
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: u32 = 0;
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_countdown_929_ = crate::leanh::lean_ctor_get(v_a_927_, 0);
                v_inner_930_ = crate::leanh::lean_ctor_get(v_a_927_, 1);
                v_isSharedCheck_949_ = (!crate::leanh::lean_is_exclusive(v_a_927_)) as u8;
                if v_isSharedCheck_949_ == 0 {
                    v___x_932_ = v_a_927_;
                    v_isShared_933_ = v_isSharedCheck_949_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inner_930_);
                    crate::leanh::lean_inc(v_countdown_929_);
                    crate::leanh::lean_dec(v_a_927_);
                    v___x_932_ = crate::leanh::lean_box(0);
                    v_isShared_933_ = v_isSharedCheck_949_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_934_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_935_ = lean_nat_dec_eq(v_countdown_929_, v___x_934_);
                if v___x_935_ == 0 {
                    v_startInclusive_936_ = crate::leanh::lean_ctor_get(v___x_925_, 1);
                    v_endExclusive_937_ = crate::leanh::lean_ctor_get(v___x_925_, 2);
                    v___x_938_ = lean_nat_sub(v_endExclusive_937_, v_startInclusive_936_);
                    v___x_939_ = lean_nat_dec_eq(v_inner_930_, v___x_938_);
                    crate::leanh::lean_dec(v___x_938_);
                    if v___x_939_ == 0 {
                        v___x_940_ = lean_string_utf8_next_fast(v___x_926_, v_inner_930_);
                        v___x_941_ = lean_string_utf8_get_fast(v___x_926_, v_inner_930_);
                        crate::leanh::lean_dec(v_inner_930_);
                        v___x_942_ = lean_nat_sub(v_countdown_929_, v___x_934_);
                        crate::leanh::lean_dec(v_countdown_929_);
                        if v_isShared_933_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_932_, 1, v___x_940_);
                            crate::leanh::lean_ctor_set(v___x_932_, 0, v___x_942_);
                            v___x_944_ = v___x_932_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_948_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_942_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_948_, 1, v___x_940_);
                            v___x_944_ = v_reuseFailAlloc_948_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_932_);
                        crate::leanh::lean_dec(v_inner_930_);
                        crate::leanh::lean_dec(v_countdown_929_);
                        return v_b_928_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_932_);
                    crate::leanh::lean_dec(v_inner_930_);
                    crate::leanh::lean_dec(v_countdown_929_);
                    return v_b_928_;
                }
            }
            2 => {
                v___x_945_ = crate::leanh::lean_box_uint32(v___x_941_);
                v___x_946_ = lean_array_push(v_b_928_, v___x_945_);
                v_a_927_ = v___x_944_;
                v_b_928_ = v___x_946_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg___boxed(
    mut v___x_950_: *mut crate::leanh::LeanObject,
    mut v___x_951_: *mut crate::leanh::LeanObject,
    mut v_a_952_: *mut crate::leanh::LeanObject,
    mut v_b_953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_954_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(v___x_950_, v___x_951_, v_a_952_, v_b_953_);
    crate::leanh::lean_dec_ref(v___x_951_);
    crate::leanh::lean_dec_ref(v___x_950_);
    return v_res_954_;
}
pub unsafe fn l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter(
    mut v_p_957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_959_: u8 = 0;
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: u32 = 0;
    let mut v___x_962_: u32 = 0;
    let mut v___x_963_: u8 = 0;
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: u32 = 0;
    let mut v___x_966_: u8 = 0;
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: u32 = 0;
    let mut v___x_969_: u32 = 0;
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: u8 = 0;
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: u32 = 0;
    let mut v___x_986_: u32 = 0;
    let mut v___x_987_: u8 = 0;
    let mut v___x_988_: u32 = 0;
    let mut v___x_989_: u32 = 0;
    let mut v___x_990_: u8 = 0;
    let mut v___x_991_: u32 = 0;
    let mut v___x_992_: u32 = 0;
    let mut v___x_993_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_971_ = l_System_Platform_isWindows;
                if v___x_971_ == 0 {
                    return v_p_957_;
                } else {
                    v___x_972_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_973_ = lean_string_utf8_byte_size(v_p_957_);
                    crate::leanh::lean_inc_ref(v_p_957_);
                    v___x_974_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_974_, 0, v_p_957_);
                    crate::leanh::lean_ctor_set(v___x_974_, 1, v___x_972_);
                    crate::leanh::lean_ctor_set(v___x_974_, 2, v___x_973_);
                    v___x_975_ = l_String_Slice_positions(v___x_974_);
                    v___x_976_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_977_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_977_, 0, v___x_976_);
                    crate::leanh::lean_ctor_set(v___x_977_, 1, v___x_975_);
                    v___x_978_ = l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0;
                    v___x_979_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(v___x_974_, v_p_957_, v___x_977_, v___x_978_);
                    crate::leanh::lean_dec_ref_known(v___x_974_, 3);
                    v___x_980_ = lean_array_to_list(v___x_979_);
                    if crate::leanh::lean_obj_tag(v___x_980_) == 1 {
                        v_tail_981_ = crate::leanh::lean_ctor_get(v___x_980_, 1);
                        crate::leanh::lean_inc(v_tail_981_);
                        if crate::leanh::lean_obj_tag(v_tail_981_) == 1 {
                            v_head_982_ = crate::leanh::lean_ctor_get(v___x_980_, 0);
                            crate::leanh::lean_inc(v_head_982_);
                            crate::leanh::lean_dec_ref_known(v___x_980_, 2);
                            v_head_983_ = crate::leanh::lean_ctor_get(v_tail_981_, 0);
                            crate::leanh::lean_inc(v_head_983_);
                            v_tail_984_ = crate::leanh::lean_ctor_get(v_tail_981_, 1);
                            crate::leanh::lean_inc(v_tail_984_);
                            crate::leanh::lean_dec_ref_known(v_tail_981_, 2);
                            v___x_985_ = 58;
                            v___x_986_ = crate::leanh::lean_unbox_uint32(v_head_983_);
                            crate::leanh::lean_dec(v_head_983_);
                            v___x_987_ = lean_uint32_dec_eq(v___x_986_, v___x_985_);
                            if v___x_987_ == 0 {
                                crate::leanh::lean_dec(v_tail_984_);
                                crate::leanh::lean_dec(v_head_982_);
                                return v_p_957_;
                            } else {
                                if crate::leanh::lean_obj_tag(v_tail_984_) == 0 {
                                    v___x_988_ = 97;
                                    v___x_989_ = crate::leanh::lean_unbox_uint32(v_head_982_);
                                    v___x_990_ = lean_uint32_dec_le(v___x_988_, v___x_989_);
                                    if v___x_990_ == 0 {
                                        crate::leanh::lean_dec(v_head_982_);
                                        v___y_959_ = v___x_990_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_991_ = 122;
                                        v___x_992_ = crate::leanh::lean_unbox_uint32(v_head_982_);
                                        crate::leanh::lean_dec(v_head_982_);
                                        v___x_993_ = lean_uint32_dec_le(v___x_992_, v___x_991_);
                                        v___y_959_ = v___x_993_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_tail_984_);
                                    crate::leanh::lean_dec(v_head_982_);
                                    return v_p_957_;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_tail_981_);
                            crate::leanh::lean_dec_ref_known(v___x_980_, 2);
                            return v_p_957_;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_980_);
                        return v_p_957_;
                    }
                }
            }
            1 => {
                if v___y_959_ == 0 {
                    return v_p_957_;
                } else {
                    v___x_960_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_961_ = lean_string_utf8_get(v_p_957_, v___x_960_);
                    v___x_962_ = 97;
                    v___x_963_ = lean_uint32_dec_le(v___x_962_, v___x_961_);
                    if v___x_963_ == 0 {
                        v___x_964_ = lean_string_utf8_set(v_p_957_, v___x_960_, v___x_961_);
                        return v___x_964_;
                    } else {
                        v___x_965_ = 122;
                        v___x_966_ = lean_uint32_dec_le(v___x_961_, v___x_965_);
                        if v___x_966_ == 0 {
                            v___x_967_ = lean_string_utf8_set(v_p_957_, v___x_960_, v___x_961_);
                            return v___x_967_;
                        } else {
                            v___x_968_ = 4294967264;
                            v___x_969_ = lean_uint32_add(v___x_961_, v___x_968_);
                            v___x_970_ = lean_string_utf8_set(v_p_957_, v___x_960_, v___x_969_);
                            return v___x_970_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0(
    mut v___x_994_: *mut crate::leanh::LeanObject,
    mut v___x_995_: *mut crate::leanh::LeanObject,
    mut v_inst_996_: *mut crate::leanh::LeanObject,
    mut v_R_997_: *mut crate::leanh::LeanObject,
    mut v_a_998_: *mut crate::leanh::LeanObject,
    mut v_b_999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1000_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(v___x_994_, v___x_995_, v_a_998_, v_b_999_);
    return v___x_1000_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___boxed(
    mut v___x_1001_: *mut crate::leanh::LeanObject,
    mut v___x_1002_: *mut crate::leanh::LeanObject,
    mut v_inst_1003_: *mut crate::leanh::LeanObject,
    mut v_R_1004_: *mut crate::leanh::LeanObject,
    mut v_a_1005_: *mut crate::leanh::LeanObject,
    mut v_b_1006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1007_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0(v___x_1001_, v___x_1002_, v_inst_1003_, v_R_1004_, v_a_1005_, v_b_1006_);
    crate::leanh::lean_dec_ref(v___x_1002_);
    crate::leanh::lean_dec_ref(v___x_1001_);
    return v_res_1007_;
}
pub unsafe fn l_List_elem___at___00System_FilePath_normalize_spec__0(
    mut v_a_1008_: u32,
    mut v_x_1009_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1010_: u8 = 0;
    let mut v_head_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: u32 = 0;
    let mut v___x_1014_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1009_) == 0 {
                    v___x_1010_ = 0;
                    return v___x_1010_;
                } else {
                    v_head_1011_ = crate::leanh::lean_ctor_get(v_x_1009_, 0);
                    v_tail_1012_ = crate::leanh::lean_ctor_get(v_x_1009_, 1);
                    v___x_1013_ = crate::leanh::lean_unbox_uint32(v_head_1011_);
                    v___x_1014_ = lean_uint32_dec_eq(v_a_1008_, v___x_1013_);
                    if v___x_1014_ == 0 {
                        v_x_1009_ = v_tail_1012_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1014_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00System_FilePath_normalize_spec__0___boxed(
    mut v_a_1016_: *mut crate::leanh::LeanObject,
    mut v_x_1017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_1018_: u32 = 0;
    let mut v_res_1019_: u8 = 0;
    let mut v_r_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1018_ = crate::leanh::lean_unbox_uint32(v_a_1016_);
    crate::leanh::lean_dec(v_a_1016_);
    v_res_1019_ =
        l_List_elem___at___00System_FilePath_normalize_spec__0(v_a_boxed_1018_, v_x_1017_);
    crate::leanh::lean_dec(v_x_1017_);
    v_r_1020_ = crate::leanh::lean_box((v_res_1019_) as usize);
    return v_r_1020_;
}
pub unsafe fn l_String_mapAux___at___00System_FilePath_normalize_spec__1(
    mut v_s_1021_: *mut crate::leanh::LeanObject,
    mut v_p_1022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1024_: u32 = 0;
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: u8 = 0;
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: u32 = 0;
    let mut v___x_1033_: u8 = 0;
    let mut v___x_1034_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1029_ = lean_string_utf8_byte_size(v_s_1021_);
                v___x_1030_ = lean_nat_dec_eq(v_p_1022_, v___x_1029_);
                if v___x_1030_ == 0 {
                    v___x_1031_ = l_System_FilePath_pathSeparators;
                    v___x_1032_ = lean_string_utf8_get_fast(v_s_1021_, v_p_1022_);
                    v___x_1033_ = l_List_elem___at___00System_FilePath_normalize_spec__0(
                        v___x_1032_,
                        v___x_1031_,
                    );
                    if v___x_1033_ == 0 {
                        v___y_1024_ = v___x_1032_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1034_ = l_System_FilePath_pathSeparator;
                        v___y_1024_ = v___x_1034_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_p_1022_);
                    return v_s_1021_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_p_1022_);
                v___x_1025_ = lean_string_utf8_set(v_s_1021_, v_p_1022_, v___y_1024_);
                v___x_1026_ = l_Char_utf8Size(v___y_1024_);
                v___x_1027_ = lean_nat_add(v_p_1022_, v___x_1026_);
                crate::leanh::lean_dec(v___x_1026_);
                crate::leanh::lean_dec(v_p_1022_);
                v_s_1021_ = v___x_1025_;
                v_p_1022_ = v___x_1027_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_System_FilePath_normalize___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1035_ = l_System_FilePath_pathSeparators;
    v___x_1036_ = l_List_lengthTR___redArg(v___x_1035_);
    return v___x_1036_;
}
pub unsafe fn _init_l_System_FilePath_normalize___closed__1() -> u8 {
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: u8 = 0;
    v___x_1037_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1038_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_FilePath_normalize___closed__0),
        core::ptr::addr_of_mut!(l_System_FilePath_normalize___closed__0_once),
        _init_l_System_FilePath_normalize___closed__0,
    );
    v___x_1039_ = lean_nat_dec_eq(v___x_1038_, v___x_1037_);
    return v___x_1039_;
}
pub unsafe fn l_System_FilePath_normalize(
    mut v_p_1040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: u8 = 0;
    v_p_1041_ = l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter(
        v_p_1040_,
    );
    v___x_1042_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_System_FilePath_normalize___closed__1),
        core::ptr::addr_of_mut!(l_System_FilePath_normalize___closed__1_once),
        _init_l_System_FilePath_normalize___closed__1,
    );
    if v___x_1042_ == 0 {
        let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1043_ = crate::leanh::lean_unsigned_to_nat(0);
        v_p_1044_ =
            l_String_mapAux___at___00System_FilePath_normalize_spec__1(v_p_1041_, v___x_1043_);
        return v_p_1044_;
    } else {
        return v_p_1041_;
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__1(
    mut v_x_1045_: *mut crate::leanh::LeanObject,
    mut v_x_1046_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1045_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_1046_) == 0 {
            let mut v___x_1047_: u8 = 0;
            v___x_1047_ = 1;
            return v___x_1047_;
        } else {
            let mut v___x_1048_: u8 = 0;
            v___x_1048_ = 0;
            return v___x_1048_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_1046_) == 0 {
            let mut v___x_1049_: u8 = 0;
            v___x_1049_ = 0;
            return v___x_1049_;
        } else {
            let mut v_val_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1052_: u32 = 0;
            let mut v___x_1053_: u32 = 0;
            let mut v___x_1054_: u8 = 0;
            v_val_1050_ = crate::leanh::lean_ctor_get(v_x_1045_, 0);
            v_val_1051_ = crate::leanh::lean_ctor_get(v_x_1046_, 0);
            v___x_1052_ = crate::leanh::lean_unbox_uint32(v_val_1050_);
            v___x_1053_ = crate::leanh::lean_unbox_uint32(v_val_1051_);
            v___x_1054_ = lean_uint32_dec_eq(v___x_1052_, v___x_1053_);
            return v___x_1054_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__1___boxed(
    mut v_x_1055_: *mut crate::leanh::LeanObject,
    mut v_x_1056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1057_: u8 = 0;
    let mut v_r_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1057_ =
        l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__1(v_x_1055_, v_x_1056_);
    crate::leanh::lean_dec(v_x_1056_);
    crate::leanh::lean_dec(v_x_1055_);
    v_r_1058_ = crate::leanh::lean_box((v_res_1057_) as usize);
    return v_r_1058_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(
    mut v___x_1059_: *mut crate::leanh::LeanObject,
    mut v___x_1060_: *mut crate::leanh::LeanObject,
    mut v_a_1061_: *mut crate::leanh::LeanObject,
    mut v_b_1062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: u8 = 0;
    let mut v_zero_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1069_: u8 = 0;
    let mut v___x_1070_: u32 = 0;
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1063_ = crate::leanh::lean_ctor_get(v___x_1060_, 0);
                v_startInclusive_1064_ = crate::leanh::lean_ctor_get(v___x_1060_, 1);
                v_endExclusive_1065_ = crate::leanh::lean_ctor_get(v___x_1060_, 2);
                v___x_1066_ = lean_nat_sub(v_endExclusive_1065_, v_startInclusive_1064_);
                v___x_1067_ = lean_nat_dec_eq(v_a_1061_, v___x_1066_);
                crate::leanh::lean_dec(v___x_1066_);
                if v___x_1067_ == 0 {
                    v_zero_1068_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_isZero_1069_ = lean_nat_dec_eq(v_b_1062_, v_zero_1068_);
                    if v_isZero_1069_ == 1 {
                        crate::leanh::lean_dec(v_b_1062_);
                        v___x_1070_ = lean_string_utf8_get_fast(v___x_1059_, v_a_1061_);
                        crate::leanh::lean_dec(v_a_1061_);
                        v___x_1071_ = crate::leanh::lean_box_uint32(v___x_1070_);
                        v___x_1072_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1072_, 0, v___x_1071_);
                        return v___x_1072_;
                    } else {
                        v___x_1073_ = lean_nat_add(v_startInclusive_1064_, v_a_1061_);
                        crate::leanh::lean_dec(v_a_1061_);
                        v___x_1074_ = lean_string_utf8_next_fast(v_str_1063_, v___x_1073_);
                        crate::leanh::lean_dec(v___x_1073_);
                        v___x_1075_ = lean_nat_sub(v___x_1074_, v_startInclusive_1064_);
                        v_one_1076_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_n_1077_ = lean_nat_sub(v_b_1062_, v_one_1076_);
                        crate::leanh::lean_dec(v_b_1062_);
                        v_a_1061_ = v___x_1075_;
                        v_b_1062_ = v_n_1077_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_1062_);
                    crate::leanh::lean_dec(v_a_1061_);
                    v___x_1079_ = crate::leanh::lean_box(0);
                    return v___x_1079_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg___boxed(
    mut v___x_1080_: *mut crate::leanh::LeanObject,
    mut v___x_1081_: *mut crate::leanh::LeanObject,
    mut v_a_1082_: *mut crate::leanh::LeanObject,
    mut v_b_1083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1084_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_1080_, v___x_1081_, v_a_1082_, v_b_1083_);
    crate::leanh::lean_dec_ref(v___x_1081_);
    crate::leanh::lean_dec_ref(v___x_1080_);
    return v_res_1084_;
}
pub unsafe fn _init_l_System_FilePath_isAbsolute___closed__0___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1085_: u32 = 0;
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1085_ = 58;
    v___x_1086_ = crate::leanh::lean_box_uint32(v___x_1085_);
    return v___x_1086_;
}
pub unsafe fn _init_l_System_FilePath_isAbsolute___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1087_ = l_System_FilePath_isAbsolute___closed__0___boxed__const__1;
    v___x_1088_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1088_, 0, v___x_1087_);
    return v___x_1088_;
}
pub unsafe fn l_System_FilePath_isAbsolute(mut v_p_1089_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1092_: u32 = 0;
    let mut v___x_1093_: u8 = 0;
    let mut v___x_1094_: u8 = 0;
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: u8 = 0;
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: u32 = 0;
    let mut v_val_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1090_ = l_System_FilePath_pathSeparators;
                v___x_1103_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1104_ = lean_string_utf8_byte_size(v_p_1089_);
                crate::leanh::lean_inc_ref(v_p_1089_);
                v___x_1105_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1105_, 0, v_p_1089_);
                crate::leanh::lean_ctor_set(v___x_1105_, 1, v___x_1103_);
                crate::leanh::lean_ctor_set(v___x_1105_, 2, v___x_1104_);
                v___x_1106_ = l_String_Slice_Pos_get_x3f(v___x_1105_, v___x_1103_);
                crate::leanh::lean_dec_ref_known(v___x_1105_, 3);
                if crate::leanh::lean_obj_tag(v___x_1106_) == 0 {
                    v___x_1107_ = 65;
                    v___y_1092_ = v___x_1107_;
                    state = 1;
                    continue;
                } else {
                    v_val_1108_ = crate::leanh::lean_ctor_get(v___x_1106_, 0);
                    crate::leanh::lean_inc(v_val_1108_);
                    crate::leanh::lean_dec_ref_known(v___x_1106_, 1);
                    v___x_1109_ = crate::leanh::lean_unbox_uint32(v_val_1108_);
                    crate::leanh::lean_dec(v_val_1108_);
                    v___y_1092_ = v___x_1109_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1093_ = l_List_elem___at___00System_FilePath_normalize_spec__0(
                    v___y_1092_,
                    v___x_1090_,
                );
                if v___x_1093_ == 0 {
                    v___x_1094_ = l_System_Platform_isWindows;
                    if v___x_1094_ == 0 {
                        crate::leanh::lean_dec_ref(v_p_1089_);
                        return v___x_1094_;
                    } else {
                        v___x_1095_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1096_ = lean_string_utf8_byte_size(v_p_1089_);
                        crate::leanh::lean_inc_ref(v_p_1089_);
                        v___x_1097_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1097_, 0, v_p_1089_);
                        crate::leanh::lean_ctor_set(v___x_1097_, 1, v___x_1095_);
                        crate::leanh::lean_ctor_set(v___x_1097_, 2, v___x_1096_);
                        v___x_1098_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1099_ = l_String_Slice_positions(v___x_1097_);
                        v___x_1100_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v_p_1089_, v___x_1097_, v___x_1099_, v___x_1098_);
                        crate::leanh::lean_dec_ref_known(v___x_1097_, 3);
                        crate::leanh::lean_dec_ref(v_p_1089_);
                        v___x_1101_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_System_FilePath_isAbsolute___closed__0),
                            core::ptr::addr_of_mut!(l_System_FilePath_isAbsolute___closed__0_once),
                            _init_l_System_FilePath_isAbsolute___closed__0,
                        );
                        v___x_1102_ =
                            l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__1(
                                v___x_1100_,
                                v___x_1101_,
                            );
                        crate::leanh::lean_dec(v___x_1100_);
                        return v___x_1102_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_p_1089_);
                    return v___x_1093_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_System_FilePath_isAbsolute___boxed(
    mut v_p_1110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1111_: u8 = 0;
    let mut v_r_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1111_ = l_System_FilePath_isAbsolute(v_p_1110_);
    v_r_1112_ = crate::leanh::lean_box((v_res_1111_) as usize);
    return v_r_1112_;
}
pub unsafe fn l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0(
    mut v___x_1113_: *mut crate::leanh::LeanObject,
    mut v___x_1114_: *mut crate::leanh::LeanObject,
    mut v_n_1115_: *mut crate::leanh::LeanObject,
    mut v_it_1116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1117_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_1114_, v___x_1113_, v_it_1116_, v_n_1115_);
    return v___x_1117_;
}
pub unsafe fn l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0___boxed(
    mut v___x_1118_: *mut crate::leanh::LeanObject,
    mut v___x_1119_: *mut crate::leanh::LeanObject,
    mut v_n_1120_: *mut crate::leanh::LeanObject,
    mut v_it_1121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1122_ = l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0(
        v___x_1118_,
        v___x_1119_,
        v_n_1120_,
        v_it_1121_,
    );
    crate::leanh::lean_dec_ref(v___x_1119_);
    crate::leanh::lean_dec_ref(v___x_1118_);
    return v_res_1122_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0(
    mut v___x_1123_: *mut crate::leanh::LeanObject,
    mut v___x_1124_: *mut crate::leanh::LeanObject,
    mut v_inst_1125_: *mut crate::leanh::LeanObject,
    mut v_R_1126_: *mut crate::leanh::LeanObject,
    mut v_a_1127_: *mut crate::leanh::LeanObject,
    mut v_b_1128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1129_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_1123_, v___x_1124_, v_a_1127_, v_b_1128_);
    return v___x_1129_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___boxed(
    mut v___x_1130_: *mut crate::leanh::LeanObject,
    mut v___x_1131_: *mut crate::leanh::LeanObject,
    mut v_inst_1132_: *mut crate::leanh::LeanObject,
    mut v_R_1133_: *mut crate::leanh::LeanObject,
    mut v_a_1134_: *mut crate::leanh::LeanObject,
    mut v_b_1135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1136_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0(v___x_1130_, v___x_1131_, v_inst_1132_, v_R_1133_, v_a_1134_, v_b_1135_);
    crate::leanh::lean_dec_ref(v___x_1131_);
    crate::leanh::lean_dec_ref(v___x_1130_);
    return v_res_1136_;
}
pub unsafe fn l_System_FilePath_isRelative(mut v_p_1137_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_1138_: u8 = 0;
    v___x_1138_ = l_System_FilePath_isAbsolute(v_p_1137_);
    if v___x_1138_ == 0 {
        let mut v___x_1139_: u8 = 0;
        v___x_1139_ = 1;
        return v___x_1139_;
    } else {
        let mut v___x_1140_: u8 = 0;
        v___x_1140_ = 0;
        return v___x_1140_;
    }
}
pub unsafe fn l_System_FilePath_isRelative___boxed(
    mut v_p_1141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1142_: u8 = 0;
    let mut v_r_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1142_ = l_System_FilePath_isRelative(v_p_1141_);
    v_r_1143_ = crate::leanh::lean_box((v_res_1142_) as usize);
    return v_r_1143_;
}
pub unsafe fn _init_l_System_FilePath_join___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1144_: u32 = 0;
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1144_ = l_System_FilePath_pathSeparator;
    v___x_1145_ = l_System_instInhabitedFilePath_default___closed__0;
    v___x_1146_ = lean_string_push(v___x_1145_, v___x_1144_);
    return v___x_1146_;
}
pub unsafe fn l_System_FilePath_join(
    mut v_p_1147_: *mut crate::leanh::LeanObject,
    mut v_sub_1148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1149_: u8 = 0;
    crate::leanh::lean_inc_ref(v_sub_1148_);
    v___x_1149_ = l_System_FilePath_isAbsolute(v_sub_1148_);
    if v___x_1149_ == 0 {
        let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1150_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_System_FilePath_join___closed__0),
            core::ptr::addr_of_mut!(l_System_FilePath_join___closed__0_once),
            _init_l_System_FilePath_join___closed__0,
        );
        v___x_1151_ = lean_string_append(v_p_1147_, v___x_1150_);
        v___x_1152_ = lean_string_append(v___x_1151_, v_sub_1148_);
        crate::leanh::lean_dec_ref(v_sub_1148_);
        return v___x_1152_;
    } else {
        crate::leanh::lean_dec_ref(v_p_1147_);
        return v_sub_1148_;
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(
    mut v_s_1156_: *mut crate::leanh::LeanObject,
    mut v_a_1157_: *mut crate::leanh::LeanObject,
    mut v_b_1158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: u8 = 0;
    let mut v_str_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: u32 = 0;
    let mut v___x_1172_: u8 = 0;
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1159_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1160_ = lean_nat_dec_eq(v_a_1157_, v___x_1159_);
                if v___x_1160_ == 0 {
                    v_str_1161_ = crate::leanh::lean_ctor_get(v_s_1156_, 0);
                    v_startInclusive_1162_ = crate::leanh::lean_ctor_get(v_s_1156_, 1);
                    v___x_1163_ = l_System_FilePath_pathSeparators;
                    v___x_1164_ = lean_nat_add(v_startInclusive_1162_, v_a_1157_);
                    crate::leanh::lean_inc(v___x_1164_);
                    crate::leanh::lean_inc(v_startInclusive_1162_);
                    crate::leanh::lean_inc_ref(v_str_1161_);
                    v___x_1165_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1165_, 0, v_str_1161_);
                    crate::leanh::lean_ctor_set(v___x_1165_, 1, v_startInclusive_1162_);
                    crate::leanh::lean_ctor_set(v___x_1165_, 2, v___x_1164_);
                    v___x_1166_ = lean_nat_sub(v___x_1164_, v_startInclusive_1162_);
                    crate::leanh::lean_dec(v___x_1164_);
                    v___x_1167_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1168_ = lean_nat_sub(v___x_1166_, v___x_1167_);
                    crate::leanh::lean_dec(v___x_1166_);
                    v___x_1169_ = l_String_Slice_posLE(v___x_1165_, v___x_1168_);
                    crate::leanh::lean_dec_ref_known(v___x_1165_, 3);
                    v___x_1170_ = lean_nat_add(v_startInclusive_1162_, v___x_1169_);
                    v___x_1171_ = lean_string_utf8_get_fast(v_str_1161_, v___x_1170_);
                    crate::leanh::lean_dec(v___x_1170_);
                    v___x_1172_ = l_List_elem___at___00System_FilePath_normalize_spec__0(
                        v___x_1171_,
                        v___x_1163_,
                    );
                    if v___x_1172_ == 0 {
                        crate::leanh::lean_dec(v___x_1169_);
                        v___x_1173_ = crate::leanh::lean_box(0);
                        v___x_1174_ = lean_nat_sub(v_a_1157_, v___x_1167_);
                        crate::leanh::lean_dec(v_a_1157_);
                        v___x_1175_ = l_String_Slice_posLE(v_s_1156_, v___x_1174_);
                        v_a_1157_ = v___x_1175_;
                        v_b_1158_ = v___x_1173_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_1157_);
                        v___x_1177_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1177_, 0, v___x_1169_);
                        return v___x_1177_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1157_);
                    crate::leanh::lean_inc(v_b_1158_);
                    return v_b_1158_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg___boxed(
    mut v_s_1178_: *mut crate::leanh::LeanObject,
    mut v_a_1179_: *mut crate::leanh::LeanObject,
    mut v_b_1180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1181_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_1178_, v_a_1179_, v_b_1180_);
    crate::leanh::lean_dec(v_b_1180_);
    crate::leanh::lean_dec_ref(v_s_1178_);
    return v_res_1181_;
}
pub unsafe fn l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(
    mut v_s_1182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_1183_ = crate::leanh::lean_ctor_get(v_s_1182_, 1);
    v_endExclusive_1184_ = crate::leanh::lean_ctor_get(v_s_1182_, 2);
    v_searcher_1185_ = lean_nat_sub(v_endExclusive_1184_, v_startInclusive_1183_);
    v___x_1186_ = crate::leanh::lean_box(0);
    v___x_1187_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_1182_, v_searcher_1185_, v___x_1186_);
    return v___x_1187_;
}
pub unsafe fn l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___boxed(
    mut v_s_1188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1189_ = l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(v_s_1188_);
    crate::leanh::lean_dec_ref(v_s_1188_);
    return v_res_1189_;
}
pub unsafe fn l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(
    mut v_p_1190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1199_: u8 = 0;
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1203_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1191_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1192_ = lean_string_utf8_byte_size(v_p_1190_);
                v___x_1193_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1193_, 0, v_p_1190_);
                crate::leanh::lean_ctor_set(v___x_1193_, 1, v___x_1191_);
                crate::leanh::lean_ctor_set(v___x_1193_, 2, v___x_1192_);
                v___x_1194_ = l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(v___x_1193_);
                crate::leanh::lean_dec_ref_known(v___x_1193_, 3);
                if crate::leanh::lean_obj_tag(v___x_1194_) == 0 {
                    v___x_1195_ = crate::leanh::lean_box(0);
                    return v___x_1195_;
                } else {
                    v_val_1196_ = crate::leanh::lean_ctor_get(v___x_1194_, 0);
                    v_isSharedCheck_1203_ = (!crate::leanh::lean_is_exclusive(v___x_1194_)) as u8;
                    if v_isSharedCheck_1203_ == 0 {
                        v___x_1198_ = v___x_1194_;
                        v_isShared_1199_ = v_isSharedCheck_1203_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1196_);
                        crate::leanh::lean_dec(v___x_1194_);
                        v___x_1198_ = crate::leanh::lean_box(0);
                        v_isShared_1199_ = v_isSharedCheck_1203_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1199_ == 0 {
                    v___x_1201_ = v___x_1198_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1202_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_val_1196_);
                    v___x_1201_ = v_reuseFailAlloc_1202_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1201_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0(
    mut v_s_1204_: *mut crate::leanh::LeanObject,
    mut v_inst_1205_: *mut crate::leanh::LeanObject,
    mut v_R_1206_: *mut crate::leanh::LeanObject,
    mut v_a_1207_: *mut crate::leanh::LeanObject,
    mut v_b_1208_: *mut crate::leanh::LeanObject,
    mut v_c_1209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1210_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_1204_, v_a_1207_, v_b_1208_);
    return v___x_1210_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___boxed(
    mut v_s_1211_: *mut crate::leanh::LeanObject,
    mut v_inst_1212_: *mut crate::leanh::LeanObject,
    mut v_R_1213_: *mut crate::leanh::LeanObject,
    mut v_a_1214_: *mut crate::leanh::LeanObject,
    mut v_b_1215_: *mut crate::leanh::LeanObject,
    mut v_c_1216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1217_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0(v_s_1211_, v_inst_1212_, v_R_1213_, v_a_1214_, v_b_1215_, v_c_1216_);
    crate::leanh::lean_dec(v_b_1215_);
    crate::leanh::lean_dec_ref(v_s_1211_);
    return v_res_1217_;
}
pub unsafe fn l___private_Init_System_FilePath_0__System_FilePath_afterRootDirectory(
    mut v_p_1218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1221_: u32 = 0;
    let mut v___x_1222_: u8 = 0;
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: u32 = 0;
    let mut v_val_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1219_ = l_System_FilePath_pathSeparators;
                v___x_1233_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1234_ = lean_string_utf8_byte_size(v_p_1218_);
                crate::leanh::lean_inc_ref(v_p_1218_);
                v___x_1235_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1235_, 0, v_p_1218_);
                crate::leanh::lean_ctor_set(v___x_1235_, 1, v___x_1233_);
                crate::leanh::lean_ctor_set(v___x_1235_, 2, v___x_1234_);
                v___x_1236_ = l_String_Slice_Pos_get_x3f(v___x_1235_, v___x_1233_);
                crate::leanh::lean_dec_ref_known(v___x_1235_, 3);
                if crate::leanh::lean_obj_tag(v___x_1236_) == 0 {
                    v___x_1237_ = 65;
                    v___y_1221_ = v___x_1237_;
                    state = 1;
                    continue;
                } else {
                    v_val_1238_ = crate::leanh::lean_ctor_get(v___x_1236_, 0);
                    crate::leanh::lean_inc(v_val_1238_);
                    crate::leanh::lean_dec_ref_known(v___x_1236_, 1);
                    v___x_1239_ = crate::leanh::lean_unbox_uint32(v_val_1238_);
                    crate::leanh::lean_dec(v_val_1238_);
                    v___y_1221_ = v___x_1239_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1222_ = l_List_elem___at___00System_FilePath_normalize_spec__0(
                    v___y_1221_,
                    v___x_1219_,
                );
                if v___x_1222_ == 0 {
                    v___x_1223_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1224_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1225_ = lean_string_utf8_byte_size(v_p_1218_);
                    v___x_1226_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1226_, 0, v_p_1218_);
                    crate::leanh::lean_ctor_set(v___x_1226_, 1, v___x_1223_);
                    crate::leanh::lean_ctor_set(v___x_1226_, 2, v___x_1225_);
                    v___x_1227_ = l_String_Slice_Pos_nextn(v___x_1226_, v___x_1223_, v___x_1224_);
                    crate::leanh::lean_dec_ref_known(v___x_1226_, 3);
                    return v___x_1227_;
                } else {
                    v___x_1228_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1229_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1230_ = lean_string_utf8_byte_size(v_p_1218_);
                    v___x_1231_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1231_, 0, v_p_1218_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 1, v___x_1228_);
                    crate::leanh::lean_ctor_set(v___x_1231_, 2, v___x_1230_);
                    v___x_1232_ = l_String_Slice_Pos_nextn(v___x_1231_, v___x_1228_, v___x_1229_);
                    crate::leanh::lean_dec_ref_known(v___x_1231_, 3);
                    return v___x_1232_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_System_FilePath_parent(
    mut v_p_1240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: u8 = 0;
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: u8 = 0;
    let mut v_afterRootDirectory_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: u8 = 0;
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1267_: u8 = 0;
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1271_: u8 = 0;
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_p_1240_);
                v___x_1251_ =
                    l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(v_p_1240_);
                if crate::leanh::lean_obj_tag(v___x_1251_) == 0 {
                    v___x_1273_ = crate::leanh::lean_box(0);
                    v___y_1253_ = v___x_1273_;
                    state = 2;
                    continue;
                } else {
                    v_val_1274_ = crate::leanh::lean_ctor_get(v___x_1251_, 0);
                    crate::leanh::lean_inc(v_val_1274_);
                    v___x_1275_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1276_ = lean_string_utf8_extract(v_p_1240_, v___x_1275_, v_val_1274_);
                    crate::leanh::lean_dec(v_val_1274_);
                    v___x_1277_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1277_, 0, v___x_1276_);
                    v___y_1253_ = v___x_1277_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_1242_);
                v___x_1246_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1246_, 0, v___y_1242_);
                v___x_1247_ =
                    l_Option_instDecidableEq___redArg(v___y_1243_, v___y_1245_, v___x_1246_);
                if v___x_1247_ == 0 {
                    crate::leanh::lean_dec(v___y_1242_);
                    crate::leanh::lean_dec_ref(v_p_1240_);
                    return v___y_1244_;
                } else {
                    crate::leanh::lean_dec(v___y_1244_);
                    v___x_1248_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1249_ = lean_string_utf8_extract(v_p_1240_, v___x_1248_, v___y_1242_);
                    crate::leanh::lean_dec(v___y_1242_);
                    crate::leanh::lean_dec_ref(v_p_1240_);
                    v___x_1250_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1250_, 0, v___x_1249_);
                    return v___x_1250_;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_p_1240_);
                v___x_1254_ = l_System_FilePath_isAbsolute(v_p_1240_);
                if v___x_1254_ == 0 {
                    crate::leanh::lean_dec(v___x_1251_);
                    crate::leanh::lean_dec_ref(v_p_1240_);
                    return v___y_1253_;
                } else {
                    crate::leanh::lean_inc_ref(v_p_1240_);
                    v_afterRootDirectory_1255_ =
                        l___private_Init_System_FilePath_0__System_FilePath_afterRootDirectory(
                            v_p_1240_,
                        );
                    v___x_1256_ = lean_string_utf8_byte_size(v_p_1240_);
                    v___x_1257_ = lean_nat_dec_eq(v_afterRootDirectory_1255_, v___x_1256_);
                    if v___x_1257_ == 0 {
                        crate::leanh::lean_inc_ref(v_p_1240_);
                        v___x_1258_ = crate::leanh::lean_alloc_closure(
                            l_String_instDecidableEqPos___boxed as *mut core::ffi::c_void,
                            3,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___x_1258_, 0, v_p_1240_);
                        if crate::leanh::lean_obj_tag(v___x_1251_) == 0 {
                            v___y_1242_ = v_afterRootDirectory_1255_;
                            v___y_1243_ = v___x_1258_;
                            v___y_1244_ = v___y_1253_;
                            v___y_1245_ = v___x_1251_;
                            state = 1;
                            continue;
                        } else {
                            v_val_1259_ = crate::leanh::lean_ctor_get(v___x_1251_, 0);
                            crate::leanh::lean_inc(v_val_1259_);
                            crate::leanh::lean_dec_ref_known(v___x_1251_, 1);
                            v___x_1260_ = crate::leanh::lean_unsigned_to_nat(0);
                            crate::leanh::lean_inc_ref(v_p_1240_);
                            v___x_1261_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1261_, 0, v_p_1240_);
                            crate::leanh::lean_ctor_set(v___x_1261_, 1, v___x_1260_);
                            crate::leanh::lean_ctor_set(v___x_1261_, 2, v___x_1256_);
                            v___x_1262_ = l_String_Slice_Pos_next_x3f(v___x_1261_, v_val_1259_);
                            crate::leanh::lean_dec(v_val_1259_);
                            crate::leanh::lean_dec_ref_known(v___x_1261_, 3);
                            if crate::leanh::lean_obj_tag(v___x_1262_) == 0 {
                                v___x_1263_ = crate::leanh::lean_box(0);
                                v___y_1242_ = v_afterRootDirectory_1255_;
                                v___y_1243_ = v___x_1258_;
                                v___y_1244_ = v___y_1253_;
                                v___y_1245_ = v___x_1263_;
                                state = 1;
                                continue;
                            } else {
                                v_val_1264_ = crate::leanh::lean_ctor_get(v___x_1262_, 0);
                                v_isSharedCheck_1271_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1262_)) as u8;
                                if v_isSharedCheck_1271_ == 0 {
                                    v___x_1266_ = v___x_1262_;
                                    v_isShared_1267_ = v_isSharedCheck_1271_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_1264_);
                                    crate::leanh::lean_dec(v___x_1262_);
                                    v___x_1266_ = crate::leanh::lean_box(0);
                                    v_isShared_1267_ = v_isSharedCheck_1271_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_afterRootDirectory_1255_);
                        crate::leanh::lean_dec(v___y_1253_);
                        crate::leanh::lean_dec(v___x_1251_);
                        crate::leanh::lean_dec_ref(v_p_1240_);
                        v___x_1272_ = crate::leanh::lean_box(0);
                        return v___x_1272_;
                    }
                }
            }
            3 => {
                if v_isShared_1267_ == 0 {
                    v___x_1269_ = v___x_1266_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1270_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_val_1264_);
                    v___x_1269_ = v_reuseFailAlloc_1270_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_1242_ = v_afterRootDirectory_1255_;
                v___y_1243_ = v___x_1258_;
                v___y_1244_ = v___y_1253_;
                v___y_1245_ = v___x_1269_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_System_FilePath_fileName(
    mut v_p_1280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1283_: u8 = 0;
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: u8 = 0;
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: u8 = 0;
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: u8 = 0;
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_p_1280_);
                v___x_1296_ =
                    l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(v_p_1280_);
                if crate::leanh::lean_obj_tag(v___x_1296_) == 0 {
                    v___y_1290_ = v_p_1280_;
                    state = 2;
                    continue;
                } else {
                    v_val_1297_ = crate::leanh::lean_ctor_get(v___x_1296_, 0);
                    crate::leanh::lean_inc(v_val_1297_);
                    crate::leanh::lean_dec_ref_known(v___x_1296_, 1);
                    v___x_1298_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1299_ = lean_string_utf8_byte_size(v_p_1280_);
                    crate::leanh::lean_inc_ref(v_p_1280_);
                    v___x_1300_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1300_, 0, v_p_1280_);
                    crate::leanh::lean_ctor_set(v___x_1300_, 1, v___x_1298_);
                    crate::leanh::lean_ctor_set(v___x_1300_, 2, v___x_1299_);
                    v___x_1301_ = l_String_Slice_Pos_next_x21(v___x_1300_, v_val_1297_);
                    crate::leanh::lean_dec(v_val_1297_);
                    crate::leanh::lean_dec_ref_known(v___x_1300_, 3);
                    v___x_1302_ = lean_string_utf8_extract(v_p_1280_, v___x_1301_, v___x_1299_);
                    crate::leanh::lean_dec(v___x_1301_);
                    crate::leanh::lean_dec_ref(v_p_1280_);
                    v___y_1290_ = v___x_1302_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v___y_1283_ == 0 {
                    v___x_1284_ = l_System_FilePath_fileName___closed__0;
                    v___x_1285_ = lean_string_dec_eq(v___y_1282_, v___x_1284_);
                    if v___x_1285_ == 0 {
                        v___x_1286_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1286_, 0, v___y_1282_);
                        return v___x_1286_;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_1282_);
                        v___x_1287_ = crate::leanh::lean_box(0);
                        return v___x_1287_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_1282_);
                    v___x_1288_ = crate::leanh::lean_box(0);
                    return v___x_1288_;
                }
            }
            2 => {
                v___x_1291_ = lean_string_utf8_byte_size(v___y_1290_);
                v___x_1292_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1293_ = lean_nat_dec_eq(v___x_1291_, v___x_1292_);
                if v___x_1293_ == 0 {
                    v___x_1294_ = l_System_FilePath_fileName___closed__1;
                    v___x_1295_ = lean_string_dec_eq(v___y_1290_, v___x_1294_);
                    v___y_1282_ = v___y_1290_;
                    v___y_1283_ = v___x_1295_;
                    state = 1;
                    continue;
                } else {
                    v___y_1282_ = v___y_1290_;
                    v___y_1283_ = v___x_1293_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(
    mut v_s_1303_: *mut crate::leanh::LeanObject,
    mut v_a_1304_: *mut crate::leanh::LeanObject,
    mut v_b_1305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: u8 = 0;
    let mut v_str_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: u32 = 0;
    let mut v___x_1318_: u32 = 0;
    let mut v___x_1319_: u8 = 0;
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1306_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1307_ = lean_nat_dec_eq(v_a_1304_, v___x_1306_);
                if v___x_1307_ == 0 {
                    v_str_1308_ = crate::leanh::lean_ctor_get(v_s_1303_, 0);
                    v_startInclusive_1309_ = crate::leanh::lean_ctor_get(v_s_1303_, 1);
                    v___x_1310_ = lean_nat_add(v_startInclusive_1309_, v_a_1304_);
                    crate::leanh::lean_inc(v___x_1310_);
                    crate::leanh::lean_inc(v_startInclusive_1309_);
                    crate::leanh::lean_inc_ref(v_str_1308_);
                    v___x_1311_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1311_, 0, v_str_1308_);
                    crate::leanh::lean_ctor_set(v___x_1311_, 1, v_startInclusive_1309_);
                    crate::leanh::lean_ctor_set(v___x_1311_, 2, v___x_1310_);
                    v___x_1312_ = lean_nat_sub(v___x_1310_, v_startInclusive_1309_);
                    crate::leanh::lean_dec(v___x_1310_);
                    v___x_1313_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1314_ = lean_nat_sub(v___x_1312_, v___x_1313_);
                    crate::leanh::lean_dec(v___x_1312_);
                    v___x_1315_ = l_String_Slice_posLE(v___x_1311_, v___x_1314_);
                    crate::leanh::lean_dec_ref_known(v___x_1311_, 3);
                    v___x_1316_ = lean_nat_add(v_startInclusive_1309_, v___x_1315_);
                    v___x_1317_ = lean_string_utf8_get_fast(v_str_1308_, v___x_1316_);
                    crate::leanh::lean_dec(v___x_1316_);
                    v___x_1318_ = 46;
                    v___x_1319_ = lean_uint32_dec_eq(v___x_1317_, v___x_1318_);
                    if v___x_1319_ == 0 {
                        crate::leanh::lean_dec(v___x_1315_);
                        v___x_1320_ = crate::leanh::lean_box(0);
                        v___x_1321_ = lean_nat_sub(v_a_1304_, v___x_1313_);
                        crate::leanh::lean_dec(v_a_1304_);
                        v___x_1322_ = l_String_Slice_posLE(v_s_1303_, v___x_1321_);
                        v_a_1304_ = v___x_1322_;
                        v_b_1305_ = v___x_1320_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_1304_);
                        v___x_1324_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1324_, 0, v___x_1315_);
                        return v___x_1324_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1304_);
                    crate::leanh::lean_inc(v_b_1305_);
                    return v_b_1305_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg___boxed(
    mut v_s_1325_: *mut crate::leanh::LeanObject,
    mut v_a_1326_: *mut crate::leanh::LeanObject,
    mut v_b_1327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1328_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_1325_, v_a_1326_, v_b_1327_);
    crate::leanh::lean_dec(v_b_1327_);
    crate::leanh::lean_dec_ref(v_s_1325_);
    return v_res_1328_;
}
pub unsafe fn l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(
    mut v_s_1329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_1330_ = crate::leanh::lean_ctor_get(v_s_1329_, 1);
    v_endExclusive_1331_ = crate::leanh::lean_ctor_get(v_s_1329_, 2);
    v_searcher_1332_ = lean_nat_sub(v_endExclusive_1331_, v_startInclusive_1330_);
    v___x_1333_ = crate::leanh::lean_box(0);
    v___x_1334_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_1329_, v_searcher_1332_, v___x_1333_);
    return v___x_1334_;
}
pub unsafe fn l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0___boxed(
    mut v_s_1335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1336_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v_s_1335_);
    crate::leanh::lean_dec_ref(v_s_1335_);
    return v_res_1336_;
}
pub unsafe fn l_System_FilePath_fileStem(
    mut v_p_1337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1347_: u8 = 0;
    let mut v___x_1348_: u8 = 0;
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1353_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1338_ = l_System_FilePath_fileName(v_p_1337_);
                if crate::leanh::lean_obj_tag(v___x_1338_) == 0 {
                    return v___x_1338_;
                } else {
                    v_val_1339_ = crate::leanh::lean_ctor_get(v___x_1338_, 0);
                    crate::leanh::lean_inc_n(v_val_1339_, 2);
                    v___x_1340_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1341_ = lean_string_utf8_byte_size(v_val_1339_);
                    v___x_1342_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1342_, 0, v_val_1339_);
                    crate::leanh::lean_ctor_set(v___x_1342_, 1, v___x_1340_);
                    crate::leanh::lean_ctor_set(v___x_1342_, 2, v___x_1341_);
                    v___x_1343_ =
                        l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(
                            v___x_1342_,
                        );
                    crate::leanh::lean_dec_ref_known(v___x_1342_, 3);
                    if crate::leanh::lean_obj_tag(v___x_1343_) == 0 {
                        crate::leanh::lean_dec(v_val_1339_);
                        return v___x_1338_;
                    } else {
                        v_val_1344_ = crate::leanh::lean_ctor_get(v___x_1343_, 0);
                        v_isSharedCheck_1353_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1343_)) as u8;
                        if v_isSharedCheck_1353_ == 0 {
                            v___x_1346_ = v___x_1343_;
                            v_isShared_1347_ = v_isSharedCheck_1353_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1344_);
                            crate::leanh::lean_dec(v___x_1343_);
                            v___x_1346_ = crate::leanh::lean_box(0);
                            v_isShared_1347_ = v_isSharedCheck_1353_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1348_ = lean_nat_dec_eq(v_val_1344_, v___x_1340_);
                if v___x_1348_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1338_, 1);
                    v___x_1349_ = lean_string_utf8_extract(v_val_1339_, v___x_1340_, v_val_1344_);
                    crate::leanh::lean_dec(v_val_1344_);
                    crate::leanh::lean_dec(v_val_1339_);
                    if v_isShared_1347_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1346_, 0, v___x_1349_);
                        v___x_1351_ = v___x_1346_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1352_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1349_);
                        v___x_1351_ = v_reuseFailAlloc_1352_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1346_);
                    crate::leanh::lean_dec(v_val_1344_);
                    crate::leanh::lean_dec(v_val_1339_);
                    return v___x_1338_;
                }
            }
            2 => {
                return v___x_1351_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0(
    mut v_s_1354_: *mut crate::leanh::LeanObject,
    mut v_inst_1355_: *mut crate::leanh::LeanObject,
    mut v_R_1356_: *mut crate::leanh::LeanObject,
    mut v_a_1357_: *mut crate::leanh::LeanObject,
    mut v_b_1358_: *mut crate::leanh::LeanObject,
    mut v_c_1359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1360_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_1354_, v_a_1357_, v_b_1358_);
    return v___x_1360_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___boxed(
    mut v_s_1361_: *mut crate::leanh::LeanObject,
    mut v_inst_1362_: *mut crate::leanh::LeanObject,
    mut v_R_1363_: *mut crate::leanh::LeanObject,
    mut v_a_1364_: *mut crate::leanh::LeanObject,
    mut v_b_1365_: *mut crate::leanh::LeanObject,
    mut v_c_1366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1367_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0(v_s_1361_, v_inst_1362_, v_R_1363_, v_a_1364_, v_b_1365_, v_c_1366_);
    crate::leanh::lean_dec(v_b_1365_);
    crate::leanh::lean_dec_ref(v_s_1361_);
    return v_res_1367_;
}
pub unsafe fn _init_l_System_FilePath_extension___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1368_: u32 = 0;
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1368_ = 46;
    v___x_1369_ = l_Char_utf8Size(v___x_1368_);
    return v___x_1369_;
}
pub unsafe fn l_System_FilePath_extension(
    mut v_p_1370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1381_: u8 = 0;
    let mut v___x_1382_: u8 = 0;
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1390_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1371_ = l_System_FilePath_fileName(v_p_1370_);
                if crate::leanh::lean_obj_tag(v___x_1371_) == 0 {
                    return v___x_1371_;
                } else {
                    v_val_1372_ = crate::leanh::lean_ctor_get(v___x_1371_, 0);
                    crate::leanh::lean_inc_n(v_val_1372_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1371_, 1);
                    v___x_1373_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1374_ = lean_string_utf8_byte_size(v_val_1372_);
                    v___x_1375_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1375_, 0, v_val_1372_);
                    crate::leanh::lean_ctor_set(v___x_1375_, 1, v___x_1373_);
                    crate::leanh::lean_ctor_set(v___x_1375_, 2, v___x_1374_);
                    v___x_1376_ =
                        l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(
                            v___x_1375_,
                        );
                    crate::leanh::lean_dec_ref_known(v___x_1375_, 3);
                    if crate::leanh::lean_obj_tag(v___x_1376_) == 0 {
                        crate::leanh::lean_dec(v_val_1372_);
                        v___x_1377_ = crate::leanh::lean_box(0);
                        return v___x_1377_;
                    } else {
                        v_val_1378_ = crate::leanh::lean_ctor_get(v___x_1376_, 0);
                        v_isSharedCheck_1390_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1376_)) as u8;
                        if v_isSharedCheck_1390_ == 0 {
                            v___x_1380_ = v___x_1376_;
                            v_isShared_1381_ = v_isSharedCheck_1390_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1378_);
                            crate::leanh::lean_dec(v___x_1376_);
                            v___x_1380_ = crate::leanh::lean_box(0);
                            v_isShared_1381_ = v_isSharedCheck_1390_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1382_ = lean_nat_dec_eq(v_val_1378_, v___x_1373_);
                if v___x_1382_ == 0 {
                    v___x_1383_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_System_FilePath_extension___closed__0),
                        core::ptr::addr_of_mut!(l_System_FilePath_extension___closed__0_once),
                        _init_l_System_FilePath_extension___closed__0,
                    );
                    v___x_1384_ = lean_nat_add(v_val_1378_, v___x_1383_);
                    crate::leanh::lean_dec(v_val_1378_);
                    v___x_1385_ = lean_string_utf8_extract(v_val_1372_, v___x_1384_, v___x_1374_);
                    crate::leanh::lean_dec(v___x_1384_);
                    crate::leanh::lean_dec(v_val_1372_);
                    if v_isShared_1381_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1380_, 0, v___x_1385_);
                        v___x_1387_ = v___x_1380_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1388_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
                        v___x_1387_ = v_reuseFailAlloc_1388_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1380_);
                    crate::leanh::lean_dec(v_val_1378_);
                    crate::leanh::lean_dec(v_val_1372_);
                    v___x_1389_ = crate::leanh::lean_box(0);
                    return v___x_1389_;
                }
            }
            2 => {
                return v___x_1387_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_System_FilePath_withFileName(
    mut v_p_1391_: *mut crate::leanh::LeanObject,
    mut v_fname_1392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1393_ = l_System_FilePath_parent(v_p_1391_);
    if crate::leanh::lean_obj_tag(v___x_1393_) == 0 {
        return v_fname_1392_;
    } else {
        let mut v_val_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1394_ = crate::leanh::lean_ctor_get(v___x_1393_, 0);
        crate::leanh::lean_inc(v_val_1394_);
        crate::leanh::lean_dec_ref_known(v___x_1393_, 1);
        v___x_1395_ = l_System_FilePath_join(v_val_1394_, v_fname_1392_);
        return v___x_1395_;
    }
}
pub unsafe fn l_System_FilePath_addExtension(
    mut v_p_1396_: *mut crate::leanh::LeanObject,
    mut v_ext_1397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_p_1396_);
    v___x_1398_ = l_System_FilePath_fileName(v_p_1396_);
    if crate::leanh::lean_obj_tag(v___x_1398_) == 0 {
        return v_p_1396_;
    } else {
        let mut v_val_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1402_: u8 = 0;
        v_val_1399_ = crate::leanh::lean_ctor_get(v___x_1398_, 0);
        crate::leanh::lean_inc(v_val_1399_);
        crate::leanh::lean_dec_ref_known(v___x_1398_, 1);
        v___x_1400_ = lean_string_utf8_byte_size(v_ext_1397_);
        v___x_1401_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1402_ = lean_nat_dec_eq(v___x_1400_, v___x_1401_);
        if v___x_1402_ == 0 {
            let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1403_ = l_System_FilePath_fileName___closed__1;
            v___x_1404_ = lean_string_append(v_val_1399_, v___x_1403_);
            v___x_1405_ = lean_string_append(v___x_1404_, v_ext_1397_);
            v___x_1406_ = l_System_FilePath_withFileName(v_p_1396_, v___x_1405_);
            return v___x_1406_;
        } else {
            let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1407_ = l_System_FilePath_withFileName(v_p_1396_, v_val_1399_);
            return v___x_1407_;
        }
    }
}
pub unsafe fn l_System_FilePath_addExtension___boxed(
    mut v_p_1408_: *mut crate::leanh::LeanObject,
    mut v_ext_1409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1410_ = l_System_FilePath_addExtension(v_p_1408_, v_ext_1409_);
    crate::leanh::lean_dec_ref(v_ext_1409_);
    return v_res_1410_;
}
pub unsafe fn l_System_FilePath_withExtension(
    mut v_p_1411_: *mut crate::leanh::LeanObject,
    mut v_ext_1412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_p_1411_);
    v___x_1413_ = l_System_FilePath_fileStem(v_p_1411_);
    if crate::leanh::lean_obj_tag(v___x_1413_) == 0 {
        return v_p_1411_;
    } else {
        let mut v_val_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1417_: u8 = 0;
        v_val_1414_ = crate::leanh::lean_ctor_get(v___x_1413_, 0);
        crate::leanh::lean_inc(v_val_1414_);
        crate::leanh::lean_dec_ref_known(v___x_1413_, 1);
        v___x_1415_ = lean_string_utf8_byte_size(v_ext_1412_);
        v___x_1416_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1417_ = lean_nat_dec_eq(v___x_1415_, v___x_1416_);
        if v___x_1417_ == 0 {
            let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1418_ = l_System_FilePath_fileName___closed__1;
            v___x_1419_ = lean_string_append(v_val_1414_, v___x_1418_);
            v___x_1420_ = lean_string_append(v___x_1419_, v_ext_1412_);
            v___x_1421_ = l_System_FilePath_withFileName(v_p_1411_, v___x_1420_);
            return v___x_1421_;
        } else {
            let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1422_ = l_System_FilePath_withFileName(v_p_1411_, v_val_1414_);
            return v___x_1422_;
        }
    }
}
pub unsafe fn l_System_FilePath_withExtension___boxed(
    mut v_p_1423_: *mut crate::leanh::LeanObject,
    mut v_ext_1424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1425_ = l_System_FilePath_withExtension(v_p_1423_, v_ext_1424_);
    crate::leanh::lean_dec_ref(v_ext_1424_);
    return v_res_1425_;
}
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1426_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_FilePath_join___closed__0),
        core::ptr::addr_of_mut!(l_System_FilePath_join___closed__0_once),
        _init_l_System_FilePath_join___closed__0,
    );
    v___x_1427_ = lean_string_utf8_byte_size(v___x_1426_);
    return v___x_1427_;
}
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1()
-> u8 {
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: u8 = 0;
    v___x_1428_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1429_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once), _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0);
    v___x_1430_ = lean_nat_dec_eq(v___x_1429_, v___x_1428_);
    return v___x_1430_;
}
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1431_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once), _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0);
    v___x_1432_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1433_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_FilePath_join___closed__0),
        core::ptr::addr_of_mut!(l_System_FilePath_join___closed__0_once),
        _init_l_System_FilePath_join___closed__0,
    );
    v___x_1434_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1434_, 0, v___x_1433_);
    crate::leanh::lean_ctor_set(v___x_1434_, 1, v___x_1432_);
    crate::leanh::lean_ctor_set(v___x_1434_, 2, v___x_1431_);
    return v___x_1434_;
}
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1435_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2_once), _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2);
    v___x_1436_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1435_);
    return v___x_1436_;
}
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1437_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1438_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3_once), _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3);
    v___x_1439_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2_once), _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2);
    v___x_1440_ = crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1440_, 0, v___x_1439_);
    crate::leanh::lean_ctor_set(v___x_1440_, 1, v___x_1438_);
    crate::leanh::lean_ctor_set(v___x_1440_, 2, v___x_1437_);
    crate::leanh::lean_ctor_set(v___x_1440_, 3, v___x_1437_);
    return v___x_1440_;
}
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1441_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4_once), _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4);
    v___x_1442_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1443_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1443_, 0, v___x_1442_);
    crate::leanh::lean_ctor_set(v___x_1443_, 1, v___x_1441_);
    return v___x_1443_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(
    mut v_s_1449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1450_: u8 = 0;
    v___x_1450_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1_once), _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1);
    if v___x_1450_ == 0 {
        let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1451_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5_once), _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5);
        return v___x_1451_;
    } else {
        let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1452_ =
            l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__7;
        return v___x_1452_;
    }
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___boxed(
    mut v_s_1453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1454_ =
        l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(v_s_1453_);
    crate::leanh::lean_dec_ref(v_s_1453_);
    return v_res_1454_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(
    mut v___x_1455_: *mut crate::leanh::LeanObject,
    mut v___x_1456_: *mut crate::leanh::LeanObject,
    mut v___x_1457_: *mut crate::leanh::LeanObject,
    mut v_a_1458_: *mut crate::leanh::LeanObject,
    mut v_b_1459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1472_: u8 = 0;
    let mut v_it_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1488_: u8 = 0;
    let mut v_nextIt_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1492_: u8 = 0;
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1498_: u8 = 0;
    let mut v_startInclusive_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: u8 = 0;
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1507_: u8 = 0;
    let mut v_pos_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1511_: u8 = 0;
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1516_: u8 = 0;
    let mut v_needle_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_table_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackPos_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_needlePos_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1523_: u8 = 0;
    let mut v_str_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePos_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: u8 = 0;
    let mut v___x_1531_: u8 = 0;
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackByte_1533_: u8 = 0;
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_patByte_1535_: u8 = 0;
    let mut v___x_1536_: u8 = 0;
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: u8 = 0;
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNeedlePos_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: u8 = 0;
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextNeedlePos_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: u8 = 0;
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1572_: u8 = 0;
    let mut v_isSharedCheck_1573_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1458_) == 0 {
                    v_currPos_1468_ = crate::leanh::lean_ctor_get(v_a_1458_, 0);
                    v_searcher_1469_ = crate::leanh::lean_ctor_get(v_a_1458_, 1);
                    v_isSharedCheck_1573_ = (!crate::leanh::lean_is_exclusive(v_a_1458_)) as u8;
                    if v_isSharedCheck_1573_ == 0 {
                        v___x_1471_ = v_a_1458_;
                        v_isShared_1472_ = v_isSharedCheck_1573_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_1469_);
                        crate::leanh::lean_inc(v_currPos_1468_);
                        crate::leanh::lean_dec(v_a_1458_);
                        v___x_1471_ = crate::leanh::lean_box(0);
                        v_isShared_1472_ = v_isSharedCheck_1573_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1457_);
                    crate::leanh::lean_dec_ref(v___x_1455_);
                    return v_b_1459_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___x_1455_);
                v___x_1464_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1464_, 0, v___x_1455_);
                crate::leanh::lean_ctor_set(v___x_1464_, 1, v_startInclusive_1462_);
                crate::leanh::lean_ctor_set(v___x_1464_, 2, v_endExclusive_1463_);
                v___x_1465_ = l_String_Slice_toString(v___x_1464_);
                crate::leanh::lean_dec_ref_known(v___x_1464_, 3);
                v___x_1466_ = lean_array_push(v_b_1459_, v___x_1465_);
                v_a_1458_ = v_it_1461_;
                v_b_1459_ = v___x_1466_;
                state = 0;
                continue;
            }
            2 => match crate::leanh::lean_obj_tag(v_searcher_1469_) {
                0 => {
                    crate::leanh::lean_del_object(v___x_1471_);
                    v_pos_1495_ = crate::leanh::lean_ctor_get(v_searcher_1469_, 0);
                    v_isSharedCheck_1507_ =
                        (!crate::leanh::lean_is_exclusive(v_searcher_1469_)) as u8;
                    if v_isSharedCheck_1507_ == 0 {
                        v___x_1497_ = v_searcher_1469_;
                        v_isShared_1498_ = v_isSharedCheck_1507_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_pos_1495_);
                        crate::leanh::lean_dec(v_searcher_1469_);
                        v___x_1497_ = crate::leanh::lean_box(0);
                        v_isShared_1498_ = v_isSharedCheck_1507_;
                        state = 9;
                        continue;
                    }
                }
                1 => {
                    v_pos_1508_ = crate::leanh::lean_ctor_get(v_searcher_1469_, 0);
                    v_isSharedCheck_1516_ =
                        (!crate::leanh::lean_is_exclusive(v_searcher_1469_)) as u8;
                    if v_isSharedCheck_1516_ == 0 {
                        v___x_1510_ = v_searcher_1469_;
                        v_isShared_1511_ = v_isSharedCheck_1516_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_pos_1508_);
                        crate::leanh::lean_dec(v_searcher_1469_);
                        v___x_1510_ = crate::leanh::lean_box(0);
                        v_isShared_1511_ = v_isSharedCheck_1516_;
                        state = 11;
                        continue;
                    }
                }
                2 => {
                    v_needle_1517_ = crate::leanh::lean_ctor_get(v_searcher_1469_, 0);
                    v_table_1518_ = crate::leanh::lean_ctor_get(v_searcher_1469_, 1);
                    v_stackPos_1519_ = crate::leanh::lean_ctor_get(v_searcher_1469_, 2);
                    v_needlePos_1520_ = crate::leanh::lean_ctor_get(v_searcher_1469_, 3);
                    v_isSharedCheck_1572_ =
                        (!crate::leanh::lean_is_exclusive(v_searcher_1469_)) as u8;
                    if v_isSharedCheck_1572_ == 0 {
                        v___x_1522_ = v_searcher_1469_;
                        v_isShared_1523_ = v_isSharedCheck_1572_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_needlePos_1520_);
                        crate::leanh::lean_inc(v_stackPos_1519_);
                        crate::leanh::lean_inc(v_table_1518_);
                        crate::leanh::lean_inc(v_needle_1517_);
                        crate::leanh::lean_dec(v_searcher_1469_);
                        v___x_1522_ = crate::leanh::lean_box(0);
                        v_isShared_1523_ = v_isSharedCheck_1572_;
                        state = 13;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_del_object(v___x_1471_);
                    state = 8;
                    continue;
                }
            },
            3 => {
                if v_isShared_1472_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1471_, 1, v_it_1474_);
                    v___x_1476_ = v___x_1471_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1478_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_currPos_1468_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_it_1474_);
                    v___x_1476_ = v_reuseFailAlloc_1478_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_1458_ = v___x_1476_;
                state = 0;
                continue;
            }
            5 => {
                v_slice_1483_ =
                    l_String_Slice_subslice_x21(v___x_1456_, v_currPos_1468_, v_startPos_1481_);
                v_startInclusive_1484_ = crate::leanh::lean_ctor_get(v_slice_1483_, 0);
                v_endExclusive_1485_ = crate::leanh::lean_ctor_get(v_slice_1483_, 1);
                v_isSharedCheck_1492_ = (!crate::leanh::lean_is_exclusive(v_slice_1483_)) as u8;
                if v_isSharedCheck_1492_ == 0 {
                    v___x_1487_ = v_slice_1483_;
                    v_isShared_1488_ = v_isSharedCheck_1492_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_endExclusive_1485_);
                    crate::leanh::lean_inc(v_startInclusive_1484_);
                    crate::leanh::lean_dec(v_slice_1483_);
                    v___x_1487_ = crate::leanh::lean_box(0);
                    v_isShared_1488_ = v_isSharedCheck_1492_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1488_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1487_, 1, v_it_1480_);
                    crate::leanh::lean_ctor_set(v___x_1487_, 0, v_endPos_1482_);
                    v_nextIt_1490_ = v___x_1487_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1491_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_endPos_1482_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_it_1480_);
                    v_nextIt_1490_ = v_reuseFailAlloc_1491_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_it_1461_ = v_nextIt_1490_;
                v_startInclusive_1462_ = v_startInclusive_1484_;
                v_endExclusive_1463_ = v_endExclusive_1485_;
                state = 1;
                continue;
            }
            8 => {
                v___x_1494_ = crate::leanh::lean_box(1);
                crate::leanh::lean_inc(v___x_1457_);
                v_it_1461_ = v___x_1494_;
                v_startInclusive_1462_ = v_currPos_1468_;
                v_endExclusive_1463_ = v___x_1457_;
                state = 1;
                continue;
            }
            9 => {
                v_startInclusive_1499_ = crate::leanh::lean_ctor_get(v___x_1456_, 1);
                v_endExclusive_1500_ = crate::leanh::lean_ctor_get(v___x_1456_, 2);
                v___x_1501_ = lean_nat_sub(v_endExclusive_1500_, v_startInclusive_1499_);
                v___x_1502_ = lean_nat_dec_eq(v_pos_1495_, v___x_1501_);
                crate::leanh::lean_dec(v___x_1501_);
                if v___x_1502_ == 0 {
                    crate::leanh::lean_inc(v_pos_1495_);
                    if v_isShared_1498_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1497_, 1);
                        v___x_1504_ = v___x_1497_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1505_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_pos_1495_);
                        v___x_1504_ = v_reuseFailAlloc_1505_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1497_);
                    v___x_1506_ = crate::leanh::lean_box(3);
                    crate::leanh::lean_inc(v_pos_1495_);
                    v_it_1480_ = v___x_1506_;
                    v_startPos_1481_ = v_pos_1495_;
                    v_endPos_1482_ = v_pos_1495_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                crate::leanh::lean_inc(v_pos_1495_);
                v_it_1480_ = v___x_1504_;
                v_startPos_1481_ = v_pos_1495_;
                v_endPos_1482_ = v_pos_1495_;
                state = 5;
                continue;
            }
            11 => {
                v___x_1512_ = lean_string_utf8_next_fast(v___x_1455_, v_pos_1508_);
                crate::leanh::lean_dec(v_pos_1508_);
                if v_isShared_1511_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1510_, 0);
                    crate::leanh::lean_ctor_set(v___x_1510_, 0, v___x_1512_);
                    v___x_1514_ = v___x_1510_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1515_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1512_);
                    v___x_1514_ = v_reuseFailAlloc_1515_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v_it_1474_ = v___x_1514_;
                state = 3;
                continue;
            }
            13 => {
                v_str_1524_ = crate::leanh::lean_ctor_get(v_needle_1517_, 0);
                v_startInclusive_1525_ = crate::leanh::lean_ctor_get(v_needle_1517_, 1);
                v_endExclusive_1526_ = crate::leanh::lean_ctor_get(v_needle_1517_, 2);
                v_basePos_1527_ = lean_nat_sub(v_stackPos_1519_, v_needlePos_1520_);
                v___x_1528_ = lean_nat_sub(v_endExclusive_1526_, v_startInclusive_1525_);
                v___x_1529_ = lean_nat_add(v_basePos_1527_, v___x_1528_);
                v___x_1530_ = lean_nat_dec_le(v___x_1529_, v___x_1457_);
                crate::leanh::lean_dec(v___x_1529_);
                if v___x_1530_ == 0 {
                    crate::leanh::lean_dec(v___x_1528_);
                    crate::leanh::lean_del_object(v___x_1522_);
                    crate::leanh::lean_dec(v_needlePos_1520_);
                    crate::leanh::lean_dec(v_stackPos_1519_);
                    crate::leanh::lean_dec_ref(v_table_1518_);
                    crate::leanh::lean_dec_ref(v_needle_1517_);
                    v___x_1531_ = lean_nat_dec_lt(v_basePos_1527_, v___x_1457_);
                    crate::leanh::lean_dec(v_basePos_1527_);
                    if v___x_1531_ == 0 {
                        crate::leanh::lean_del_object(v___x_1471_);
                        state = 8;
                        continue;
                    } else {
                        v___x_1532_ = crate::leanh::lean_box(3);
                        v_it_1474_ = v___x_1532_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_basePos_1527_);
                    crate::leanh::lean_inc(v_stackPos_1519_);
                    v_stackByte_1533_ = lean_string_get_byte_fast(v___x_1455_, v_stackPos_1519_);
                    v___x_1534_ = lean_nat_add(v_startInclusive_1525_, v_needlePos_1520_);
                    v_patByte_1535_ = lean_string_get_byte_fast(v_str_1524_, v___x_1534_);
                    v___x_1536_ = lean_uint8_dec_eq(v_stackByte_1533_, v_patByte_1535_);
                    if v___x_1536_ == 0 {
                        crate::leanh::lean_dec(v___x_1528_);
                        v___x_1537_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1538_ = lean_nat_dec_eq(v_needlePos_1520_, v___x_1537_);
                        if v___x_1538_ == 0 {
                            v___x_1539_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1540_ = lean_nat_sub(v_needlePos_1520_, v___x_1539_);
                            crate::leanh::lean_dec(v_needlePos_1520_);
                            v_newNeedlePos_1541_ =
                                lean_array_fget_borrowed(v_table_1518_, v___x_1540_);
                            crate::leanh::lean_dec(v___x_1540_);
                            v___x_1542_ = lean_nat_dec_eq(v_newNeedlePos_1541_, v___x_1537_);
                            if v___x_1542_ == 0 {
                                crate::leanh::lean_inc(v_newNeedlePos_1541_);
                                if v_isShared_1523_ == 0 {
                                    crate::leanh::lean_ctor_set(
                                        v___x_1522_,
                                        3,
                                        v_newNeedlePos_1541_,
                                    );
                                    v___x_1544_ = v___x_1522_;
                                    state = 14;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1545_ =
                                        crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1545_,
                                        0,
                                        v_needle_1517_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1545_,
                                        1,
                                        v_table_1518_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1545_,
                                        2,
                                        v_stackPos_1519_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1545_,
                                        3,
                                        v_newNeedlePos_1541_,
                                    );
                                    v___x_1544_ = v_reuseFailAlloc_1545_;
                                    state = 14;
                                    continue;
                                }
                            } else {
                                v_nextStackPos_1546_ =
                                    l_String_Slice_posGE___redArg(v___x_1456_, v_stackPos_1519_);
                                if v_isShared_1523_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1522_, 3, v___x_1537_);
                                    crate::leanh::lean_ctor_set(
                                        v___x_1522_,
                                        2,
                                        v_nextStackPos_1546_,
                                    );
                                    v___x_1548_ = v___x_1522_;
                                    state = 15;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1549_ =
                                        crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1549_,
                                        0,
                                        v_needle_1517_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1549_,
                                        1,
                                        v_table_1518_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1549_,
                                        2,
                                        v_nextStackPos_1546_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1549_,
                                        3,
                                        v___x_1537_,
                                    );
                                    v___x_1548_ = v_reuseFailAlloc_1549_;
                                    state = 15;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_needlePos_1520_);
                            v___x_1550_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1551_ = lean_nat_add(v_stackPos_1519_, v___x_1550_);
                            crate::leanh::lean_dec(v_stackPos_1519_);
                            v_nextStackPos_1552_ =
                                l_String_Slice_posGE___redArg(v___x_1456_, v___x_1551_);
                            if v_isShared_1523_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1522_, 3, v___x_1537_);
                                crate::leanh::lean_ctor_set(v___x_1522_, 2, v_nextStackPos_1552_);
                                v___x_1554_ = v___x_1522_;
                                state = 16;
                                continue;
                            } else {
                                v_reuseFailAlloc_1555_ =
                                    crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1555_,
                                    0,
                                    v_needle_1517_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1555_,
                                    1,
                                    v_table_1518_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1555_,
                                    2,
                                    v_nextStackPos_1552_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1555_, 3, v___x_1537_);
                                v___x_1554_ = v_reuseFailAlloc_1555_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1471_);
                        v___x_1556_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_nextStackPos_1557_ = lean_nat_add(v_stackPos_1519_, v___x_1556_);
                        crate::leanh::lean_dec(v_stackPos_1519_);
                        v_nextNeedlePos_1558_ = lean_nat_add(v_needlePos_1520_, v___x_1556_);
                        crate::leanh::lean_dec(v_needlePos_1520_);
                        v___x_1559_ = lean_nat_dec_eq(v_nextNeedlePos_1558_, v___x_1528_);
                        crate::leanh::lean_dec(v___x_1528_);
                        if v___x_1559_ == 0 {
                            if v_isShared_1523_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1522_, 3, v_nextNeedlePos_1558_);
                                crate::leanh::lean_ctor_set(v___x_1522_, 2, v_nextStackPos_1557_);
                                v___x_1561_ = v___x_1522_;
                                state = 17;
                                continue;
                            } else {
                                v_reuseFailAlloc_1564_ =
                                    crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1564_,
                                    0,
                                    v_needle_1517_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1564_,
                                    1,
                                    v_table_1518_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1564_,
                                    2,
                                    v_nextStackPos_1557_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1564_,
                                    3,
                                    v_nextNeedlePos_1558_,
                                );
                                v___x_1561_ = v_reuseFailAlloc_1564_;
                                state = 17;
                                continue;
                            }
                        } else {
                            v___x_1565_ = lean_nat_sub(v_nextStackPos_1557_, v_nextNeedlePos_1558_);
                            crate::leanh::lean_dec(v_nextNeedlePos_1558_);
                            v___x_1566_ = l_String_Slice_pos_x21(v___x_1456_, v___x_1565_);
                            crate::leanh::lean_dec(v___x_1565_);
                            v___x_1567_ = l_String_Slice_pos_x21(v___x_1456_, v_nextStackPos_1557_);
                            v___x_1568_ = crate::leanh::lean_unsigned_to_nat(0);
                            if v_isShared_1523_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1522_, 3, v___x_1568_);
                                crate::leanh::lean_ctor_set(v___x_1522_, 2, v_nextStackPos_1557_);
                                v___x_1570_ = v___x_1522_;
                                state = 18;
                                continue;
                            } else {
                                v_reuseFailAlloc_1571_ =
                                    crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1571_,
                                    0,
                                    v_needle_1517_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1571_,
                                    1,
                                    v_table_1518_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1571_,
                                    2,
                                    v_nextStackPos_1557_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 3, v___x_1568_);
                                v___x_1570_ = v_reuseFailAlloc_1571_;
                                state = 18;
                                continue;
                            }
                        }
                    }
                }
            }
            14 => {
                v_it_1474_ = v___x_1544_;
                state = 3;
                continue;
            }
            15 => {
                v_it_1474_ = v___x_1548_;
                state = 3;
                continue;
            }
            16 => {
                v_it_1474_ = v___x_1554_;
                state = 3;
                continue;
            }
            17 => {
                v___x_1562_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1562_, 0, v_currPos_1468_);
                crate::leanh::lean_ctor_set(v___x_1562_, 1, v___x_1561_);
                v_a_1458_ = v___x_1562_;
                state = 0;
                continue;
            }
            18 => {
                v_it_1480_ = v___x_1570_;
                v_startPos_1481_ = v___x_1566_;
                v_endPos_1482_ = v___x_1567_;
                state = 5;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg___boxed(
    mut v___x_1574_: *mut crate::leanh::LeanObject,
    mut v___x_1575_: *mut crate::leanh::LeanObject,
    mut v___x_1576_: *mut crate::leanh::LeanObject,
    mut v_a_1577_: *mut crate::leanh::LeanObject,
    mut v_b_1578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1579_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_1574_, v___x_1575_, v___x_1576_, v_a_1577_, v_b_1578_);
    crate::leanh::lean_dec_ref(v___x_1575_);
    return v_res_1579_;
}
pub unsafe fn l_System_FilePath_components(
    mut v_p_1582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1583_ = l_System_FilePath_normalize(v_p_1582_);
    v___x_1584_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1585_ = lean_string_utf8_byte_size(v___x_1583_);
    crate::leanh::lean_inc_ref(v___x_1583_);
    v___x_1586_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1586_, 0, v___x_1583_);
    crate::leanh::lean_ctor_set(v___x_1586_, 1, v___x_1584_);
    crate::leanh::lean_ctor_set(v___x_1586_, 2, v___x_1585_);
    v___x_1587_ =
        l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(v___x_1586_);
    v___x_1588_ = l_System_FilePath_components___closed__0;
    v___x_1589_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_1583_, v___x_1586_, v___x_1585_, v___x_1587_, v___x_1588_);
    crate::leanh::lean_dec_ref_known(v___x_1586_, 3);
    v___x_1590_ = lean_array_to_list(v___x_1589_);
    return v___x_1590_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(
    mut v___x_1591_: *mut crate::leanh::LeanObject,
    mut v___x_1592_: *mut crate::leanh::LeanObject,
    mut v___x_1593_: *mut crate::leanh::LeanObject,
    mut v_inst_1594_: *mut crate::leanh::LeanObject,
    mut v_R_1595_: *mut crate::leanh::LeanObject,
    mut v_a_1596_: *mut crate::leanh::LeanObject,
    mut v_b_1597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1598_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_1591_, v___x_1592_, v___x_1593_, v_a_1596_, v_b_1597_);
    return v___x_1598_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___boxed(
    mut v___x_1599_: *mut crate::leanh::LeanObject,
    mut v___x_1600_: *mut crate::leanh::LeanObject,
    mut v___x_1601_: *mut crate::leanh::LeanObject,
    mut v_inst_1602_: *mut crate::leanh::LeanObject,
    mut v_R_1603_: *mut crate::leanh::LeanObject,
    mut v_a_1604_: *mut crate::leanh::LeanObject,
    mut v_b_1605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1606_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(v___x_1599_, v___x_1600_, v___x_1601_, v_inst_1602_, v_R_1603_, v_a_1604_, v_b_1605_);
    crate::leanh::lean_dec_ref(v___x_1600_);
    return v_res_1606_;
}
pub unsafe fn l_System_mkFilePath(
    mut v_parts_1607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1608_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_FilePath_join___closed__0),
        core::ptr::addr_of_mut!(l_System_FilePath_join___closed__0_once),
        _init_l_System_FilePath_join___closed__0,
    );
    v___x_1609_ = l_String_intercalate(v___x_1608_, v_parts_1607_);
    return v___x_1609_;
}
pub unsafe fn l_System_instCoeStringFilePath___lam__0(
    mut v_toString_1610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_toString_1610_);
    return v_toString_1610_;
}
pub unsafe fn l_System_instCoeStringFilePath___lam__0___boxed(
    mut v_toString_1611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1612_ = l_System_instCoeStringFilePath___lam__0(v_toString_1611_);
    crate::leanh::lean_dec_ref(v_toString_1611_);
    return v_res_1612_;
}
pub unsafe fn _init_l_System_SearchPath_separator() -> u32 {
    let mut v___x_1615_: u8 = 0;
    v___x_1615_ = l_System_Platform_isWindows;
    if v___x_1615_ == 0 {
        let mut v___x_1616_: u32 = 0;
        v___x_1616_ = 58;
        return v___x_1616_;
    } else {
        let mut v___x_1617_: u32 = 0;
        v___x_1617_ = 59;
        return v___x_1617_;
    }
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(
    mut v_s_1620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1621_ =
        l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0;
    return v___x_1621_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___boxed(
    mut v_s_1622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1623_ =
        l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(v_s_1622_);
    crate::leanh::lean_dec_ref(v_s_1622_);
    return v_res_1623_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(
    mut v_s_1624_: *mut crate::leanh::LeanObject,
    mut v___x_1625_: *mut crate::leanh::LeanObject,
    mut v___x_1626_: *mut crate::leanh::LeanObject,
    mut v_a_1627_: *mut crate::leanh::LeanObject,
    mut v_b_1628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1640_: u8 = 0;
    let mut v_startInclusive_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: u8 = 0;
    let mut v___x_1645_: u32 = 0;
    let mut v___x_1646_: u32 = 0;
    let mut v___x_1647_: u8 = 0;
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1663_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1627_) == 0 {
                    v_currPos_1636_ = crate::leanh::lean_ctor_get(v_a_1627_, 0);
                    v_searcher_1637_ = crate::leanh::lean_ctor_get(v_a_1627_, 1);
                    v_isSharedCheck_1663_ = (!crate::leanh::lean_is_exclusive(v_a_1627_)) as u8;
                    if v_isSharedCheck_1663_ == 0 {
                        v___x_1639_ = v_a_1627_;
                        v_isShared_1640_ = v_isSharedCheck_1663_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_1637_);
                        crate::leanh::lean_inc(v_currPos_1636_);
                        crate::leanh::lean_dec(v_a_1627_);
                        v___x_1639_ = crate::leanh::lean_box(0);
                        v_isShared_1640_ = v_isSharedCheck_1663_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1626_);
                    return v_b_1628_;
                }
            }
            1 => {
                v___x_1633_ = lean_string_utf8_extract(
                    v_s_1624_,
                    v_startInclusive_1631_,
                    v_endExclusive_1632_,
                );
                crate::leanh::lean_dec(v_endExclusive_1632_);
                crate::leanh::lean_dec(v_startInclusive_1631_);
                v___x_1634_ = lean_array_push(v_b_1628_, v___x_1633_);
                v_a_1627_ = v_it_1630_;
                v_b_1628_ = v___x_1634_;
                state = 0;
                continue;
            }
            2 => {
                v_startInclusive_1641_ = crate::leanh::lean_ctor_get(v___x_1625_, 1);
                v_endExclusive_1642_ = crate::leanh::lean_ctor_get(v___x_1625_, 2);
                v___x_1643_ = lean_nat_sub(v_endExclusive_1642_, v_startInclusive_1641_);
                v___x_1644_ = lean_nat_dec_eq(v_searcher_1637_, v___x_1643_);
                crate::leanh::lean_dec(v___x_1643_);
                if v___x_1644_ == 0 {
                    v___x_1645_ = l_System_SearchPath_separator;
                    v___x_1646_ = lean_string_utf8_get_fast(v_s_1624_, v_searcher_1637_);
                    v___x_1647_ = lean_uint32_dec_eq(v___x_1646_, v___x_1645_);
                    if v___x_1647_ == 0 {
                        v___x_1648_ = lean_string_utf8_next_fast(v_s_1624_, v_searcher_1637_);
                        crate::leanh::lean_dec(v_searcher_1637_);
                        if v_isShared_1640_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1639_, 1, v___x_1648_);
                            v___x_1650_ = v___x_1639_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1652_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_currPos_1636_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1652_, 1, v___x_1648_);
                            v___x_1650_ = v_reuseFailAlloc_1652_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1653_ = lean_string_utf8_next_fast(v_s_1624_, v_searcher_1637_);
                        v___x_1654_ = lean_nat_sub(v___x_1653_, v_searcher_1637_);
                        v___x_1655_ = lean_nat_add(v_searcher_1637_, v___x_1654_);
                        crate::leanh::lean_dec(v___x_1654_);
                        v_slice_1656_ = l_String_Slice_subslice_x21(
                            v___x_1625_,
                            v_currPos_1636_,
                            v_searcher_1637_,
                        );
                        crate::leanh::lean_inc(v___x_1655_);
                        if v_isShared_1640_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1639_, 1, v___x_1655_);
                            crate::leanh::lean_ctor_set(v___x_1639_, 0, v___x_1655_);
                            v_nextIt_1658_ = v___x_1639_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1661_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1655_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1661_, 1, v___x_1655_);
                            v_nextIt_1658_ = v_reuseFailAlloc_1661_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1639_);
                    crate::leanh::lean_dec(v_searcher_1637_);
                    v___x_1662_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc(v___x_1626_);
                    v_it_1630_ = v___x_1662_;
                    v_startInclusive_1631_ = v_currPos_1636_;
                    v_endExclusive_1632_ = v___x_1626_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_1627_ = v___x_1650_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_1659_ = crate::leanh::lean_ctor_get(v_slice_1656_, 0);
                crate::leanh::lean_inc(v_startInclusive_1659_);
                v_endExclusive_1660_ = crate::leanh::lean_ctor_get(v_slice_1656_, 1);
                crate::leanh::lean_inc(v_endExclusive_1660_);
                crate::leanh::lean_dec_ref(v_slice_1656_);
                v_it_1630_ = v_nextIt_1658_;
                v_startInclusive_1631_ = v_startInclusive_1659_;
                v_endExclusive_1632_ = v_endExclusive_1660_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg___boxed(
    mut v_s_1664_: *mut crate::leanh::LeanObject,
    mut v___x_1665_: *mut crate::leanh::LeanObject,
    mut v___x_1666_: *mut crate::leanh::LeanObject,
    mut v_a_1667_: *mut crate::leanh::LeanObject,
    mut v_b_1668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1669_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_1664_, v___x_1665_, v___x_1666_, v_a_1667_, v_b_1668_);
    crate::leanh::lean_dec_ref(v___x_1665_);
    crate::leanh::lean_dec_ref(v_s_1664_);
    return v_res_1669_;
}
pub unsafe fn l_System_SearchPath_parse(
    mut v_s_1670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1671_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1672_ = lean_string_utf8_byte_size(v_s_1670_);
    crate::leanh::lean_inc_ref(v_s_1670_);
    v___x_1673_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1673_, 0, v_s_1670_);
    crate::leanh::lean_ctor_set(v___x_1673_, 1, v___x_1671_);
    crate::leanh::lean_ctor_set(v___x_1673_, 2, v___x_1672_);
    v___x_1674_ =
        l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(v___x_1673_);
    v___x_1675_ = l_System_FilePath_components___closed__0;
    v___x_1676_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_1670_, v___x_1673_, v___x_1672_, v___x_1674_, v___x_1675_);
    crate::leanh::lean_dec_ref_known(v___x_1673_, 3);
    crate::leanh::lean_dec_ref(v_s_1670_);
    v___x_1677_ = lean_array_to_list(v___x_1676_);
    return v___x_1677_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(
    mut v_s_1678_: *mut crate::leanh::LeanObject,
    mut v___x_1679_: *mut crate::leanh::LeanObject,
    mut v___x_1680_: *mut crate::leanh::LeanObject,
    mut v_inst_1681_: *mut crate::leanh::LeanObject,
    mut v_R_1682_: *mut crate::leanh::LeanObject,
    mut v_a_1683_: *mut crate::leanh::LeanObject,
    mut v_b_1684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1685_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_1678_, v___x_1679_, v___x_1680_, v_a_1683_, v_b_1684_);
    return v___x_1685_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___boxed(
    mut v_s_1686_: *mut crate::leanh::LeanObject,
    mut v___x_1687_: *mut crate::leanh::LeanObject,
    mut v___x_1688_: *mut crate::leanh::LeanObject,
    mut v_inst_1689_: *mut crate::leanh::LeanObject,
    mut v_R_1690_: *mut crate::leanh::LeanObject,
    mut v_a_1691_: *mut crate::leanh::LeanObject,
    mut v_b_1692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1693_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(v_s_1686_, v___x_1687_, v___x_1688_, v_inst_1689_, v_R_1690_, v_a_1691_, v_b_1692_);
    crate::leanh::lean_dec_ref(v___x_1687_);
    crate::leanh::lean_dec_ref(v_s_1686_);
    return v_res_1693_;
}
pub unsafe fn l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(
    mut v_a_1694_: *mut crate::leanh::LeanObject,
    mut v_a_1695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1701_: u8 = 0;
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1706_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1694_) == 0 {
                    v___x_1696_ = l_List_reverse___redArg(v_a_1695_);
                    return v___x_1696_;
                } else {
                    v_head_1697_ = crate::leanh::lean_ctor_get(v_a_1694_, 0);
                    v_tail_1698_ = crate::leanh::lean_ctor_get(v_a_1694_, 1);
                    v_isSharedCheck_1706_ = (!crate::leanh::lean_is_exclusive(v_a_1694_)) as u8;
                    if v_isSharedCheck_1706_ == 0 {
                        v___x_1700_ = v_a_1694_;
                        v_isShared_1701_ = v_isSharedCheck_1706_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1698_);
                        crate::leanh::lean_inc(v_head_1697_);
                        crate::leanh::lean_dec(v_a_1694_);
                        v___x_1700_ = crate::leanh::lean_box(0);
                        v_isShared_1701_ = v_isSharedCheck_1706_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1701_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1700_, 1, v_a_1695_);
                    v___x_1703_ = v___x_1700_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1705_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_head_1697_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1705_, 1, v_a_1695_);
                    v___x_1703_ = v_reuseFailAlloc_1705_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1694_ = v_tail_1698_;
                v_a_1695_ = v___x_1703_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_System_SearchPath_toString___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1707_: u32 = 0;
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1707_ = l_System_SearchPath_separator;
    v___x_1708_ = l_System_instInhabitedFilePath_default___closed__0;
    v___x_1709_ = lean_string_push(v___x_1708_, v___x_1707_);
    return v___x_1709_;
}
pub unsafe fn l_System_SearchPath_toString(
    mut v_path_1710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1711_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_System_SearchPath_toString___closed__0),
        core::ptr::addr_of_mut!(l_System_SearchPath_toString___closed__0_once),
        _init_l_System_SearchPath_toString___closed__0,
    );
    v___x_1712_ = crate::leanh::lean_box(0);
    v___x_1713_ =
        l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(v_path_1710_, v___x_1712_);
    v___x_1714_ = l_String_intercalate(v___x_1711_, v___x_1713_);
    return v___x_1714_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_System_FilePath(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Modify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_Platform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Length(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Take(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Access(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_System_FilePath_pathSeparator = _init_l_System_FilePath_pathSeparator();
    l_System_FilePath_pathSeparators___closed__0___boxed__const__1 =
        _init_l_System_FilePath_pathSeparators___closed__0___boxed__const__1();
    crate::leanh::lean_mark_persistent(
        l_System_FilePath_pathSeparators___closed__0___boxed__const__1,
    );
    l_System_FilePath_pathSeparators___closed__1___boxed__const__1 =
        _init_l_System_FilePath_pathSeparators___closed__1___boxed__const__1();
    crate::leanh::lean_mark_persistent(
        l_System_FilePath_pathSeparators___closed__1___boxed__const__1,
    );
    l_System_FilePath_pathSeparators = _init_l_System_FilePath_pathSeparators();
    crate::leanh::lean_mark_persistent(l_System_FilePath_pathSeparators);
    l_System_FilePath_extSeparator = _init_l_System_FilePath_extSeparator();
    l_System_FilePath_exeExtension = _init_l_System_FilePath_exeExtension();
    crate::leanh::lean_mark_persistent(l_System_FilePath_exeExtension);
    l_System_FilePath_isAbsolute___closed__0___boxed__const__1 =
        _init_l_System_FilePath_isAbsolute___closed__0___boxed__const__1();
    crate::leanh::lean_mark_persistent(l_System_FilePath_isAbsolute___closed__0___boxed__const__1);
    l_System_SearchPath_separator = _init_l_System_SearchPath_separator();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_System_FilePath(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_System_FilePath(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Modify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_System_Platform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Length(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_Take(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Access(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_FilePath(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_System_FilePath(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_System_FilePath(builtin);
}
