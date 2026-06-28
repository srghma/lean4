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
    lean_array_fget_borrowed, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_string_dec_eq, lean_string_hash,
    lean_string_utf8_byte_size, lean_uint8_dec_eq, lean_uint32_dec_eq, lean_uint32_dec_le,
    lean_uint64_mix_hash,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_box_uint32, lean_box_uint64, lean_closure_set, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint8_once, lean_unbox_uint32,
    lean_unsigned_to_nat,
};
pub static l_System_instInhabitedFilePath_default___closed__0_value: LeanStringObject<1> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_System_instInhabitedFilePath_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_System_instInhabitedFilePath_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_System_instInhabitedFilePath_default: *mut LeanObject =
    core::ptr::addr_of!(l_System_instInhabitedFilePath_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_System_instInhabitedFilePath: *mut LeanObject =
    core::ptr::addr_of!(l_System_instInhabitedFilePath_default___closed__0_value)
        as *mut LeanObject;
pub static l_System_instHashableFilePath___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_System_instHashableFilePath_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_System_instHashableFilePath___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_System_instHashableFilePath___closed__0_value) as *mut LeanObject;
pub static mut l_System_instHashableFilePath: *mut LeanObject =
    core::ptr::addr_of!(l_System_instHashableFilePath___closed__0_value) as *mut LeanObject;
pub static l_System_instReprFilePath___lam__0___closed__0_value: LeanStringObject<13> =
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
        m_data: [70, 105, 108, 101, 80, 97, 116, 104, 46, 109, 107, 32, 0],
    };
static mut l_System_instReprFilePath___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_System_instReprFilePath___lam__0___closed__0_value) as *mut LeanObject;
pub static l_System_instReprFilePath___lam__0___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_System_instReprFilePath___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_System_instReprFilePath___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_System_instReprFilePath___lam__0___closed__1_value) as *mut LeanObject;
pub static l_System_instReprFilePath___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_System_instReprFilePath___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_System_instReprFilePath___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_System_instReprFilePath___closed__0_value) as *mut LeanObject;
pub static mut l_System_instReprFilePath: *mut LeanObject =
    core::ptr::addr_of!(l_System_instReprFilePath___closed__0_value) as *mut LeanObject;
pub static l_System_instToStringFilePath___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_System_instToStringFilePath___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_System_instToStringFilePath___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_System_instToStringFilePath___closed__0_value) as *mut LeanObject;
pub static mut l_System_instToStringFilePath: *mut LeanObject =
    core::ptr::addr_of!(l_System_instToStringFilePath___closed__0_value) as *mut LeanObject;
pub static mut l_System_FilePath_pathSeparator: u32 = 0;
pub static mut l_System_FilePath_pathSeparators___closed__0___boxed__const__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_System_FilePath_pathSeparators___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_FilePath_pathSeparators___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_System_FilePath_pathSeparators___closed__1___boxed__const__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_System_FilePath_pathSeparators___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_FilePath_pathSeparators___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_System_FilePath_pathSeparators: *mut LeanObject = core::ptr::null_mut();
pub static mut l_System_FilePath_extSeparator: u32 = 0;
pub static l_System_FilePath_exeExtension___closed__0_value: LeanStringObject<4> =
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
        m_data: [101, 120, 101, 0],
    };
static mut l_System_FilePath_exeExtension___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_System_FilePath_exeExtension___closed__0_value) as *mut LeanObject;
pub static mut l_System_FilePath_exeExtension: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0_value) as *mut LeanObject;
static mut l_System_FilePath_normalize___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_FilePath_normalize___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_System_FilePath_normalize___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_FilePath_normalize___closed__1: u8 = 0;
pub static mut l_System_FilePath_isAbsolute___closed__0___boxed__const__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_System_FilePath_isAbsolute___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_FilePath_isAbsolute___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_System_FilePath_join___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_FilePath_join___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_System_FilePath_instDiv___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_System_FilePath_join as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_System_FilePath_instDiv___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_System_FilePath_instDiv___closed__0_value) as *mut LeanObject;
pub static mut l_System_FilePath_instDiv: *mut LeanObject =
    core::ptr::addr_of!(l_System_FilePath_instDiv___closed__0_value) as *mut LeanObject;
pub static mut l_System_FilePath_instHDivString: *mut LeanObject =
    core::ptr::addr_of!(l_System_FilePath_instDiv___closed__0_value) as *mut LeanObject;
pub static l_System_FilePath_fileName___closed__0_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_System_FilePath_fileName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_System_FilePath_fileName___closed__0_value) as *mut LeanObject;
pub static l_System_FilePath_fileName___closed__1_value: LeanStringObject<2> = LeanStringObject {
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
static mut l_System_FilePath_fileName___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_System_FilePath_fileName___closed__1_value) as *mut LeanObject;
static mut l_System_FilePath_extension___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_FilePath_extension___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1: u8 = 0;
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__6_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__6_value) as *mut LeanObject;
pub static l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__7_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__6_value) as *mut LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__7_value) as *mut LeanObject;
pub static l_System_FilePath_components___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_System_FilePath_components___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_System_FilePath_components___closed__0_value) as *mut LeanObject;
pub static l_System_instCoeStringFilePath___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_System_instCoeStringFilePath___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_System_instCoeStringFilePath___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_System_instCoeStringFilePath___closed__0_value) as *mut LeanObject;
pub static mut l_System_instCoeStringFilePath: *mut LeanObject =
    core::ptr::addr_of!(l_System_instCoeStringFilePath___closed__0_value) as *mut LeanObject;
pub static mut l_System_SearchPath_separator: u32 = 0;
pub static l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0_value
) as *mut LeanObject;
static mut l_System_SearchPath_toString___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_SearchPath_toString___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_System_instDecidableEqFilePath_decEq(
    mut v_x_861_: *mut LeanObject,
    mut v_x_862_: *mut LeanObject,
) -> u8 {
    let mut v___x_863_: u8 = 0;
    v___x_863_ = lean_string_dec_eq(v_x_861_, v_x_862_);
    return v___x_863_;
}
pub unsafe fn l_System_instDecidableEqFilePath_decEq___boxed(
    mut v_x_864_: *mut LeanObject,
    mut v_x_865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_866_: u8 = 0;
    let mut v_r_867_: *mut LeanObject = core::ptr::null_mut();
    v_res_866_ = l_System_instDecidableEqFilePath_decEq(v_x_864_, v_x_865_);
    lean_dec_ref(v_x_865_);
    lean_dec_ref(v_x_864_);
    v_r_867_ = lean_box((v_res_866_) as usize);
    return v_r_867_;
}
pub unsafe fn l_System_instDecidableEqFilePath(
    mut v_x_868_: *mut LeanObject,
    mut v_x_869_: *mut LeanObject,
) -> u8 {
    let mut v___x_870_: u8 = 0;
    v___x_870_ = lean_string_dec_eq(v_x_868_, v_x_869_);
    return v___x_870_;
}
pub unsafe fn l_System_instDecidableEqFilePath___boxed(
    mut v_x_871_: *mut LeanObject,
    mut v_x_872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_873_: u8 = 0;
    let mut v_r_874_: *mut LeanObject = core::ptr::null_mut();
    v_res_873_ = l_System_instDecidableEqFilePath(v_x_871_, v_x_872_);
    lean_dec_ref(v_x_872_);
    lean_dec_ref(v_x_871_);
    v_r_874_ = lean_box((v_res_873_) as usize);
    return v_r_874_;
}
pub unsafe fn l_System_instHashableFilePath_hash(mut v_x_875_: *mut LeanObject) -> u64 {
    let mut v___x_876_: u64 = 0;
    let mut v___x_877_: u64 = 0;
    let mut v___x_878_: u64 = 0;
    v___x_876_ = 0u64;
    v___x_877_ = lean_string_hash(v_x_875_);
    v___x_878_ = lean_uint64_mix_hash(v___x_876_, v___x_877_);
    return v___x_878_;
}
pub unsafe fn l_System_instHashableFilePath_hash___boxed(
    mut v_x_879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_880_: u64 = 0;
    let mut v_r_881_: *mut LeanObject = core::ptr::null_mut();
    v_res_880_ = l_System_instHashableFilePath_hash(v_x_879_);
    lean_dec_ref(v_x_879_);
    v_r_881_ = lean_box_uint64(v_res_880_);
    return v_r_881_;
}
pub unsafe fn l_System_instReprFilePath___lam__0(
    mut v_p_887_: *mut LeanObject,
    mut v___y_888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    v___x_889_ = l_System_instReprFilePath___lam__0___closed__1;
    v___x_890_ = l_String_quote(v_p_887_);
    v___x_891_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_891_, 0, v___x_890_);
    v___x_892_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_892_, 0, v___x_889_);
    lean_ctor_set(v___x_892_, 1, v___x_891_);
    v___x_893_ = l_Repr_addAppParen(v___x_892_, v___y_888_);
    return v___x_893_;
}
pub unsafe fn l_System_instReprFilePath___lam__0___boxed(
    mut v_p_894_: *mut LeanObject,
    mut v___y_895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_896_: *mut LeanObject = core::ptr::null_mut();
    v_res_896_ = l_System_instReprFilePath___lam__0(v_p_894_, v___y_895_);
    lean_dec(v___y_895_);
    return v_res_896_;
}
pub unsafe fn l_System_instToStringFilePath___lam__0(
    mut v_p_899_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_p_899_);
    return v_p_899_;
}
pub unsafe fn l_System_instToStringFilePath___lam__0___boxed(
    mut v_p_900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_901_: *mut LeanObject = core::ptr::null_mut();
    v_res_901_ = l_System_instToStringFilePath___lam__0(v_p_900_);
    lean_dec_ref(v_p_900_);
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
-> *mut LeanObject {
    let mut v___x_907_: u32 = 0;
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    v___x_907_ = 47;
    v___x_908_ = lean_box_uint32(v___x_907_);
    return v___x_908_;
}
pub unsafe fn _init_l_System_FilePath_pathSeparators___closed__0() -> *mut LeanObject {
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    v___x_909_ = lean_box(0);
    v___x_910_ = l_System_FilePath_pathSeparators___closed__0___boxed__const__1;
    v___x_911_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_911_, 0, v___x_910_);
    lean_ctor_set(v___x_911_, 1, v___x_909_);
    return v___x_911_;
}
pub unsafe fn _init_l_System_FilePath_pathSeparators___closed__1___boxed__const__1()
-> *mut LeanObject {
    let mut v___x_912_: u32 = 0;
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    v___x_912_ = 92;
    v___x_913_ = lean_box_uint32(v___x_912_);
    return v___x_913_;
}
pub unsafe fn _init_l_System_FilePath_pathSeparators___closed__1() -> *mut LeanObject {
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    v___x_914_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_System_FilePath_pathSeparators___closed__0),
        core::ptr::addr_of_mut!(l_System_FilePath_pathSeparators___closed__0_once),
        _init_l_System_FilePath_pathSeparators___closed__0,
    );
    v___x_915_ = l_System_FilePath_pathSeparators___closed__1___boxed__const__1;
    v___x_916_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_916_, 0, v___x_915_);
    lean_ctor_set(v___x_916_, 1, v___x_914_);
    return v___x_916_;
}
pub unsafe fn _init_l_System_FilePath_pathSeparators() -> *mut LeanObject {
    let mut v___x_917_: u8 = 0;
    v___x_917_ = l_System_Platform_isWindows;
    if v___x_917_ == 0 {
        let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
        v___x_918_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_System_FilePath_pathSeparators___closed__0),
            core::ptr::addr_of_mut!(l_System_FilePath_pathSeparators___closed__0_once),
            _init_l_System_FilePath_pathSeparators___closed__0,
        );
        return v___x_918_;
    } else {
        let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
        v___x_919_ = lean_obj_once(
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
pub unsafe fn _init_l_System_FilePath_exeExtension() -> *mut LeanObject {
    let mut v___x_922_: u8 = 0;
    v___x_922_ = l_System_Platform_isWindows;
    if v___x_922_ == 0 {
        let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
        v___x_923_ = l_System_instInhabitedFilePath_default___closed__0;
        return v___x_923_;
    } else {
        let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
        v___x_924_ = l_System_FilePath_exeExtension___closed__0;
        return v___x_924_;
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(
    mut v___x_925_: *mut LeanObject,
    mut v___x_926_: *mut LeanObject,
    mut v_a_927_: *mut LeanObject,
    mut v_b_928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_countdown_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inner_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_933_: u8 = 0;
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: u8 = 0;
    let mut v_startInclusive_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: u8 = 0;
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: u32 = 0;
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_countdown_929_ = lean_ctor_get(v_a_927_, 0);
                v_inner_930_ = lean_ctor_get(v_a_927_, 1);
                v_isSharedCheck_949_ = (!lean_is_exclusive(v_a_927_)) as u8;
                if v_isSharedCheck_949_ == 0 {
                    v___x_932_ = v_a_927_;
                    v_isShared_933_ = v_isSharedCheck_949_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_inner_930_);
                    lean_inc(v_countdown_929_);
                    lean_dec(v_a_927_);
                    v___x_932_ = lean_box(0);
                    v_isShared_933_ = v_isSharedCheck_949_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_934_ = lean_unsigned_to_nat(1);
                v___x_935_ = lean_nat_dec_eq(v_countdown_929_, v___x_934_);
                if v___x_935_ == 0 {
                    v_startInclusive_936_ = lean_ctor_get(v___x_925_, 1);
                    v_endExclusive_937_ = lean_ctor_get(v___x_925_, 2);
                    v___x_938_ = lean_nat_sub(v_endExclusive_937_, v_startInclusive_936_);
                    v___x_939_ = lean_nat_dec_eq(v_inner_930_, v___x_938_);
                    lean_dec(v___x_938_);
                    if v___x_939_ == 0 {
                        v___x_940_ = lean_string_utf8_next_fast(v___x_926_, v_inner_930_);
                        v___x_941_ = lean_string_utf8_get_fast(v___x_926_, v_inner_930_);
                        lean_dec(v_inner_930_);
                        v___x_942_ = lean_nat_sub(v_countdown_929_, v___x_934_);
                        lean_dec(v_countdown_929_);
                        if v_isShared_933_ == 0 {
                            lean_ctor_set(v___x_932_, 1, v___x_940_);
                            lean_ctor_set(v___x_932_, 0, v___x_942_);
                            v___x_944_ = v___x_932_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_942_);
                            lean_ctor_set(v_reuseFailAlloc_948_, 1, v___x_940_);
                            v___x_944_ = v_reuseFailAlloc_948_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_932_);
                        lean_dec(v_inner_930_);
                        lean_dec(v_countdown_929_);
                        return v_b_928_;
                    }
                } else {
                    lean_del_object(v___x_932_);
                    lean_dec(v_inner_930_);
                    lean_dec(v_countdown_929_);
                    return v_b_928_;
                }
            }
            2 => {
                v___x_945_ = lean_box_uint32(v___x_941_);
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
    mut v___x_950_: *mut LeanObject,
    mut v___x_951_: *mut LeanObject,
    mut v_a_952_: *mut LeanObject,
    mut v_b_953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_954_: *mut LeanObject = core::ptr::null_mut();
    v_res_954_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(v___x_950_, v___x_951_, v_a_952_, v_b_953_);
    lean_dec_ref(v___x_951_);
    lean_dec_ref(v___x_950_);
    return v_res_954_;
}
pub unsafe fn l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter(
    mut v_p_957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_959_: u8 = 0;
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_961_: u32 = 0;
    let mut v___x_962_: u32 = 0;
    let mut v___x_963_: u8 = 0;
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: u32 = 0;
    let mut v___x_966_: u8 = 0;
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: u32 = 0;
    let mut v___x_969_: u32 = 0;
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_971_: u8 = 0;
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_984_: *mut LeanObject = core::ptr::null_mut();
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
                    v___x_972_ = lean_unsigned_to_nat(0);
                    v___x_973_ = lean_string_utf8_byte_size(v_p_957_);
                    lean_inc_ref(v_p_957_);
                    v___x_974_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_974_, 0, v_p_957_);
                    lean_ctor_set(v___x_974_, 1, v___x_972_);
                    lean_ctor_set(v___x_974_, 2, v___x_973_);
                    v___x_975_ = l_String_Slice_positions(v___x_974_);
                    v___x_976_ = lean_unsigned_to_nat(3);
                    v___x_977_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_977_, 0, v___x_976_);
                    lean_ctor_set(v___x_977_, 1, v___x_975_);
                    v___x_978_ = l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter___closed__0;
                    v___x_979_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(v___x_974_, v_p_957_, v___x_977_, v___x_978_);
                    lean_dec_ref_known(v___x_974_, 3);
                    v___x_980_ = lean_array_to_list(v___x_979_);
                    if lean_obj_tag(v___x_980_) == 1 {
                        v_tail_981_ = lean_ctor_get(v___x_980_, 1);
                        lean_inc(v_tail_981_);
                        if lean_obj_tag(v_tail_981_) == 1 {
                            v_head_982_ = lean_ctor_get(v___x_980_, 0);
                            lean_inc(v_head_982_);
                            lean_dec_ref_known(v___x_980_, 2);
                            v_head_983_ = lean_ctor_get(v_tail_981_, 0);
                            lean_inc(v_head_983_);
                            v_tail_984_ = lean_ctor_get(v_tail_981_, 1);
                            lean_inc(v_tail_984_);
                            lean_dec_ref_known(v_tail_981_, 2);
                            v___x_985_ = 58;
                            v___x_986_ = lean_unbox_uint32(v_head_983_);
                            lean_dec(v_head_983_);
                            v___x_987_ = lean_uint32_dec_eq(v___x_986_, v___x_985_);
                            if v___x_987_ == 0 {
                                lean_dec(v_tail_984_);
                                lean_dec(v_head_982_);
                                return v_p_957_;
                            } else {
                                if lean_obj_tag(v_tail_984_) == 0 {
                                    v___x_988_ = 97;
                                    v___x_989_ = lean_unbox_uint32(v_head_982_);
                                    v___x_990_ = lean_uint32_dec_le(v___x_988_, v___x_989_);
                                    if v___x_990_ == 0 {
                                        lean_dec(v_head_982_);
                                        v___y_959_ = v___x_990_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_991_ = 122;
                                        v___x_992_ = lean_unbox_uint32(v_head_982_);
                                        lean_dec(v_head_982_);
                                        v___x_993_ = lean_uint32_dec_le(v___x_992_, v___x_991_);
                                        v___y_959_ = v___x_993_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_tail_984_);
                                    lean_dec(v_head_982_);
                                    return v_p_957_;
                                }
                            }
                        } else {
                            lean_dec(v_tail_981_);
                            lean_dec_ref_known(v___x_980_, 2);
                            return v_p_957_;
                        }
                    } else {
                        lean_dec(v___x_980_);
                        return v_p_957_;
                    }
                }
            }
            1 => {
                if v___y_959_ == 0 {
                    return v_p_957_;
                } else {
                    v___x_960_ = lean_unsigned_to_nat(0);
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
    mut v___x_994_: *mut LeanObject,
    mut v___x_995_: *mut LeanObject,
    mut v_inst_996_: *mut LeanObject,
    mut v_R_997_: *mut LeanObject,
    mut v_a_998_: *mut LeanObject,
    mut v_b_999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    v___x_1000_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___redArg(v___x_994_, v___x_995_, v_a_998_, v_b_999_);
    return v___x_1000_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0___boxed(
    mut v___x_1001_: *mut LeanObject,
    mut v___x_1002_: *mut LeanObject,
    mut v_inst_1003_: *mut LeanObject,
    mut v_R_1004_: *mut LeanObject,
    mut v_a_1005_: *mut LeanObject,
    mut v_b_1006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1007_: *mut LeanObject = core::ptr::null_mut();
    v_res_1007_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter_spec__0(v___x_1001_, v___x_1002_, v_inst_1003_, v_R_1004_, v_a_1005_, v_b_1006_);
    lean_dec_ref(v___x_1002_);
    lean_dec_ref(v___x_1001_);
    return v_res_1007_;
}
pub unsafe fn l_List_elem___at___00System_FilePath_normalize_spec__0(
    mut v_a_1008_: u32,
    mut v_x_1009_: *mut LeanObject,
) -> u8 {
    let mut v___x_1010_: u8 = 0;
    let mut v_head_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: u32 = 0;
    let mut v___x_1014_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1009_) == 0 {
                    v___x_1010_ = 0;
                    return v___x_1010_;
                } else {
                    v_head_1011_ = lean_ctor_get(v_x_1009_, 0);
                    v_tail_1012_ = lean_ctor_get(v_x_1009_, 1);
                    v___x_1013_ = lean_unbox_uint32(v_head_1011_);
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
    mut v_a_1016_: *mut LeanObject,
    mut v_x_1017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_1018_: u32 = 0;
    let mut v_res_1019_: u8 = 0;
    let mut v_r_1020_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_1018_ = lean_unbox_uint32(v_a_1016_);
    lean_dec(v_a_1016_);
    v_res_1019_ =
        l_List_elem___at___00System_FilePath_normalize_spec__0(v_a_boxed_1018_, v_x_1017_);
    lean_dec(v_x_1017_);
    v_r_1020_ = lean_box((v_res_1019_) as usize);
    return v_r_1020_;
}
pub unsafe fn l_String_mapAux___at___00System_FilePath_normalize_spec__1(
    mut v_s_1021_: *mut LeanObject,
    mut v_p_1022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1024_: u32 = 0;
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: u8 = 0;
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_dec(v_p_1022_);
                    return v_s_1021_;
                }
            }
            1 => {
                lean_inc(v_p_1022_);
                v___x_1025_ = lean_string_utf8_set(v_s_1021_, v_p_1022_, v___y_1024_);
                v___x_1026_ = l_Char_utf8Size(v___y_1024_);
                v___x_1027_ = lean_nat_add(v_p_1022_, v___x_1026_);
                lean_dec(v___x_1026_);
                lean_dec(v_p_1022_);
                v_s_1021_ = v___x_1025_;
                v_p_1022_ = v___x_1027_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_System_FilePath_normalize___closed__0() -> *mut LeanObject {
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    v___x_1035_ = l_System_FilePath_pathSeparators;
    v___x_1036_ = l_List_lengthTR___redArg(v___x_1035_);
    return v___x_1036_;
}
pub unsafe fn _init_l_System_FilePath_normalize___closed__1() -> u8 {
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: u8 = 0;
    v___x_1037_ = lean_unsigned_to_nat(1);
    v___x_1038_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_System_FilePath_normalize___closed__0),
        core::ptr::addr_of_mut!(l_System_FilePath_normalize___closed__0_once),
        _init_l_System_FilePath_normalize___closed__0,
    );
    v___x_1039_ = lean_nat_dec_eq(v___x_1038_, v___x_1037_);
    return v___x_1039_;
}
pub unsafe fn l_System_FilePath_normalize(mut v_p_1040_: *mut LeanObject) -> *mut LeanObject {
    let mut v_p_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: u8 = 0;
    v_p_1041_ = l___private_Init_System_FilePath_0__System_FilePath_normalize_normalizeDriveLetter(
        v_p_1040_,
    );
    v___x_1042_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_System_FilePath_normalize___closed__1),
        core::ptr::addr_of_mut!(l_System_FilePath_normalize___closed__1_once),
        _init_l_System_FilePath_normalize___closed__1,
    );
    if v___x_1042_ == 0 {
        let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_1044_: *mut LeanObject = core::ptr::null_mut();
        v___x_1043_ = lean_unsigned_to_nat(0);
        v_p_1044_ =
            l_String_mapAux___at___00System_FilePath_normalize_spec__1(v_p_1041_, v___x_1043_);
        return v_p_1044_;
    } else {
        return v_p_1041_;
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__1(
    mut v_x_1045_: *mut LeanObject,
    mut v_x_1046_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_1045_) == 0 {
        if lean_obj_tag(v_x_1046_) == 0 {
            let mut v___x_1047_: u8 = 0;
            v___x_1047_ = 1;
            return v___x_1047_;
        } else {
            let mut v___x_1048_: u8 = 0;
            v___x_1048_ = 0;
            return v___x_1048_;
        }
    } else {
        if lean_obj_tag(v_x_1046_) == 0 {
            let mut v___x_1049_: u8 = 0;
            v___x_1049_ = 0;
            return v___x_1049_;
        } else {
            let mut v_val_1050_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_1051_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1052_: u32 = 0;
            let mut v___x_1053_: u32 = 0;
            let mut v___x_1054_: u8 = 0;
            v_val_1050_ = lean_ctor_get(v_x_1045_, 0);
            v_val_1051_ = lean_ctor_get(v_x_1046_, 0);
            v___x_1052_ = lean_unbox_uint32(v_val_1050_);
            v___x_1053_ = lean_unbox_uint32(v_val_1051_);
            v___x_1054_ = lean_uint32_dec_eq(v___x_1052_, v___x_1053_);
            return v___x_1054_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__1___boxed(
    mut v_x_1055_: *mut LeanObject,
    mut v_x_1056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1057_: u8 = 0;
    let mut v_r_1058_: *mut LeanObject = core::ptr::null_mut();
    v_res_1057_ =
        l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__1(v_x_1055_, v_x_1056_);
    lean_dec(v_x_1056_);
    lean_dec(v_x_1055_);
    v_r_1058_ = lean_box((v_res_1057_) as usize);
    return v_r_1058_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(
    mut v___x_1059_: *mut LeanObject,
    mut v___x_1060_: *mut LeanObject,
    mut v_a_1061_: *mut LeanObject,
    mut v_b_1062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: u8 = 0;
    let mut v_zero_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1069_: u8 = 0;
    let mut v___x_1070_: u32 = 0;
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1063_ = lean_ctor_get(v___x_1060_, 0);
                v_startInclusive_1064_ = lean_ctor_get(v___x_1060_, 1);
                v_endExclusive_1065_ = lean_ctor_get(v___x_1060_, 2);
                v___x_1066_ = lean_nat_sub(v_endExclusive_1065_, v_startInclusive_1064_);
                v___x_1067_ = lean_nat_dec_eq(v_a_1061_, v___x_1066_);
                lean_dec(v___x_1066_);
                if v___x_1067_ == 0 {
                    v_zero_1068_ = lean_unsigned_to_nat(0);
                    v_isZero_1069_ = lean_nat_dec_eq(v_b_1062_, v_zero_1068_);
                    if v_isZero_1069_ == 1 {
                        lean_dec(v_b_1062_);
                        v___x_1070_ = lean_string_utf8_get_fast(v___x_1059_, v_a_1061_);
                        lean_dec(v_a_1061_);
                        v___x_1071_ = lean_box_uint32(v___x_1070_);
                        v___x_1072_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1072_, 0, v___x_1071_);
                        return v___x_1072_;
                    } else {
                        v___x_1073_ = lean_nat_add(v_startInclusive_1064_, v_a_1061_);
                        lean_dec(v_a_1061_);
                        v___x_1074_ = lean_string_utf8_next_fast(v_str_1063_, v___x_1073_);
                        lean_dec(v___x_1073_);
                        v___x_1075_ = lean_nat_sub(v___x_1074_, v_startInclusive_1064_);
                        v_one_1076_ = lean_unsigned_to_nat(1);
                        v_n_1077_ = lean_nat_sub(v_b_1062_, v_one_1076_);
                        lean_dec(v_b_1062_);
                        v_a_1061_ = v___x_1075_;
                        v_b_1062_ = v_n_1077_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec(v_b_1062_);
                    lean_dec(v_a_1061_);
                    v___x_1079_ = lean_box(0);
                    return v___x_1079_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg___boxed(
    mut v___x_1080_: *mut LeanObject,
    mut v___x_1081_: *mut LeanObject,
    mut v_a_1082_: *mut LeanObject,
    mut v_b_1083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1084_: *mut LeanObject = core::ptr::null_mut();
    v_res_1084_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_1080_, v___x_1081_, v_a_1082_, v_b_1083_);
    lean_dec_ref(v___x_1081_);
    lean_dec_ref(v___x_1080_);
    return v_res_1084_;
}
pub unsafe fn _init_l_System_FilePath_isAbsolute___closed__0___boxed__const__1() -> *mut LeanObject
{
    let mut v___x_1085_: u32 = 0;
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    v___x_1085_ = 58;
    v___x_1086_ = lean_box_uint32(v___x_1085_);
    return v___x_1086_;
}
pub unsafe fn _init_l_System_FilePath_isAbsolute___closed__0() -> *mut LeanObject {
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
    v___x_1087_ = l_System_FilePath_isAbsolute___closed__0___boxed__const__1;
    v___x_1088_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1088_, 0, v___x_1087_);
    return v___x_1088_;
}
pub unsafe fn l_System_FilePath_isAbsolute(mut v_p_1089_: *mut LeanObject) -> u8 {
    let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1092_: u32 = 0;
    let mut v___x_1093_: u8 = 0;
    let mut v___x_1094_: u8 = 0;
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: u8 = 0;
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: u32 = 0;
    let mut v_val_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1090_ = l_System_FilePath_pathSeparators;
                v___x_1103_ = lean_unsigned_to_nat(0);
                v___x_1104_ = lean_string_utf8_byte_size(v_p_1089_);
                lean_inc_ref(v_p_1089_);
                v___x_1105_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1105_, 0, v_p_1089_);
                lean_ctor_set(v___x_1105_, 1, v___x_1103_);
                lean_ctor_set(v___x_1105_, 2, v___x_1104_);
                v___x_1106_ = l_String_Slice_Pos_get_x3f(v___x_1105_, v___x_1103_);
                lean_dec_ref_known(v___x_1105_, 3);
                if lean_obj_tag(v___x_1106_) == 0 {
                    v___x_1107_ = 65;
                    v___y_1092_ = v___x_1107_;
                    state = 1;
                    continue;
                } else {
                    v_val_1108_ = lean_ctor_get(v___x_1106_, 0);
                    lean_inc(v_val_1108_);
                    lean_dec_ref_known(v___x_1106_, 1);
                    v___x_1109_ = lean_unbox_uint32(v_val_1108_);
                    lean_dec(v_val_1108_);
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
                        lean_dec_ref(v_p_1089_);
                        return v___x_1094_;
                    } else {
                        v___x_1095_ = lean_unsigned_to_nat(0);
                        v___x_1096_ = lean_string_utf8_byte_size(v_p_1089_);
                        lean_inc_ref(v_p_1089_);
                        v___x_1097_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_1097_, 0, v_p_1089_);
                        lean_ctor_set(v___x_1097_, 1, v___x_1095_);
                        lean_ctor_set(v___x_1097_, 2, v___x_1096_);
                        v___x_1098_ = lean_unsigned_to_nat(1);
                        v___x_1099_ = l_String_Slice_positions(v___x_1097_);
                        v___x_1100_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v_p_1089_, v___x_1097_, v___x_1099_, v___x_1098_);
                        lean_dec_ref_known(v___x_1097_, 3);
                        lean_dec_ref(v_p_1089_);
                        v___x_1101_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_System_FilePath_isAbsolute___closed__0),
                            core::ptr::addr_of_mut!(l_System_FilePath_isAbsolute___closed__0_once),
                            _init_l_System_FilePath_isAbsolute___closed__0,
                        );
                        v___x_1102_ =
                            l_Option_instBEq_beq___at___00System_FilePath_isAbsolute_spec__1(
                                v___x_1100_,
                                v___x_1101_,
                            );
                        lean_dec(v___x_1100_);
                        return v___x_1102_;
                    }
                } else {
                    lean_dec_ref(v_p_1089_);
                    return v___x_1093_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_System_FilePath_isAbsolute___boxed(
    mut v_p_1110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1111_: u8 = 0;
    let mut v_r_1112_: *mut LeanObject = core::ptr::null_mut();
    v_res_1111_ = l_System_FilePath_isAbsolute(v_p_1110_);
    v_r_1112_ = lean_box((v_res_1111_) as usize);
    return v_r_1112_;
}
pub unsafe fn l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0(
    mut v___x_1113_: *mut LeanObject,
    mut v___x_1114_: *mut LeanObject,
    mut v_n_1115_: *mut LeanObject,
    mut v_it_1116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    v___x_1117_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_1114_, v___x_1113_, v_it_1116_, v_n_1115_);
    return v___x_1117_;
}
pub unsafe fn l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0___boxed(
    mut v___x_1118_: *mut LeanObject,
    mut v___x_1119_: *mut LeanObject,
    mut v_n_1120_: *mut LeanObject,
    mut v_it_1121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1122_: *mut LeanObject = core::ptr::null_mut();
    v_res_1122_ = l_Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0(
        v___x_1118_,
        v___x_1119_,
        v_n_1120_,
        v_it_1121_,
    );
    lean_dec_ref(v___x_1119_);
    lean_dec_ref(v___x_1118_);
    return v_res_1122_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0(
    mut v___x_1123_: *mut LeanObject,
    mut v___x_1124_: *mut LeanObject,
    mut v_inst_1125_: *mut LeanObject,
    mut v_R_1126_: *mut LeanObject,
    mut v_a_1127_: *mut LeanObject,
    mut v_b_1128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    v___x_1129_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___redArg(v___x_1123_, v___x_1124_, v_a_1127_, v_b_1128_);
    return v___x_1129_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0___boxed(
    mut v___x_1130_: *mut LeanObject,
    mut v___x_1131_: *mut LeanObject,
    mut v_inst_1132_: *mut LeanObject,
    mut v_R_1133_: *mut LeanObject,
    mut v_a_1134_: *mut LeanObject,
    mut v_b_1135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1136_: *mut LeanObject = core::ptr::null_mut();
    v_res_1136_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_atIdxSlow_x3f___at___00System_FilePath_isAbsolute_spec__0_spec__0(v___x_1130_, v___x_1131_, v_inst_1132_, v_R_1133_, v_a_1134_, v_b_1135_);
    lean_dec_ref(v___x_1131_);
    lean_dec_ref(v___x_1130_);
    return v_res_1136_;
}
pub unsafe fn l_System_FilePath_isRelative(mut v_p_1137_: *mut LeanObject) -> u8 {
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
    mut v_p_1141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1142_: u8 = 0;
    let mut v_r_1143_: *mut LeanObject = core::ptr::null_mut();
    v_res_1142_ = l_System_FilePath_isRelative(v_p_1141_);
    v_r_1143_ = lean_box((v_res_1142_) as usize);
    return v_r_1143_;
}
pub unsafe fn _init_l_System_FilePath_join___closed__0() -> *mut LeanObject {
    let mut v___x_1144_: u32 = 0;
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    v___x_1144_ = l_System_FilePath_pathSeparator;
    v___x_1145_ = l_System_instInhabitedFilePath_default___closed__0;
    v___x_1146_ = lean_string_push(v___x_1145_, v___x_1144_);
    return v___x_1146_;
}
pub unsafe fn l_System_FilePath_join(
    mut v_p_1147_: *mut LeanObject,
    mut v_sub_1148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1149_: u8 = 0;
    lean_inc_ref(v_sub_1148_);
    v___x_1149_ = l_System_FilePath_isAbsolute(v_sub_1148_);
    if v___x_1149_ == 0 {
        let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
        v___x_1150_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_System_FilePath_join___closed__0),
            core::ptr::addr_of_mut!(l_System_FilePath_join___closed__0_once),
            _init_l_System_FilePath_join___closed__0,
        );
        v___x_1151_ = lean_string_append(v_p_1147_, v___x_1150_);
        v___x_1152_ = lean_string_append(v___x_1151_, v_sub_1148_);
        lean_dec_ref(v_sub_1148_);
        return v___x_1152_;
    } else {
        lean_dec_ref(v_p_1147_);
        return v_sub_1148_;
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(
    mut v_s_1156_: *mut LeanObject,
    mut v_a_1157_: *mut LeanObject,
    mut v_b_1158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: u8 = 0;
    let mut v_str_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: u32 = 0;
    let mut v___x_1172_: u8 = 0;
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1159_ = lean_unsigned_to_nat(0);
                v___x_1160_ = lean_nat_dec_eq(v_a_1157_, v___x_1159_);
                if v___x_1160_ == 0 {
                    v_str_1161_ = lean_ctor_get(v_s_1156_, 0);
                    v_startInclusive_1162_ = lean_ctor_get(v_s_1156_, 1);
                    v___x_1163_ = l_System_FilePath_pathSeparators;
                    v___x_1164_ = lean_nat_add(v_startInclusive_1162_, v_a_1157_);
                    lean_inc(v___x_1164_);
                    lean_inc(v_startInclusive_1162_);
                    lean_inc_ref(v_str_1161_);
                    v___x_1165_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1165_, 0, v_str_1161_);
                    lean_ctor_set(v___x_1165_, 1, v_startInclusive_1162_);
                    lean_ctor_set(v___x_1165_, 2, v___x_1164_);
                    v___x_1166_ = lean_nat_sub(v___x_1164_, v_startInclusive_1162_);
                    lean_dec(v___x_1164_);
                    v___x_1167_ = lean_unsigned_to_nat(1);
                    v___x_1168_ = lean_nat_sub(v___x_1166_, v___x_1167_);
                    lean_dec(v___x_1166_);
                    v___x_1169_ = l_String_Slice_posLE(v___x_1165_, v___x_1168_);
                    lean_dec_ref_known(v___x_1165_, 3);
                    v___x_1170_ = lean_nat_add(v_startInclusive_1162_, v___x_1169_);
                    v___x_1171_ = lean_string_utf8_get_fast(v_str_1161_, v___x_1170_);
                    lean_dec(v___x_1170_);
                    v___x_1172_ = l_List_elem___at___00System_FilePath_normalize_spec__0(
                        v___x_1171_,
                        v___x_1163_,
                    );
                    if v___x_1172_ == 0 {
                        lean_dec(v___x_1169_);
                        v___x_1173_ = lean_box(0);
                        v___x_1174_ = lean_nat_sub(v_a_1157_, v___x_1167_);
                        lean_dec(v_a_1157_);
                        v___x_1175_ = l_String_Slice_posLE(v_s_1156_, v___x_1174_);
                        v_a_1157_ = v___x_1175_;
                        v_b_1158_ = v___x_1173_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_a_1157_);
                        v___x_1177_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1177_, 0, v___x_1169_);
                        return v___x_1177_;
                    }
                } else {
                    lean_dec(v_a_1157_);
                    lean_inc(v_b_1158_);
                    return v_b_1158_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg___boxed(
    mut v_s_1178_: *mut LeanObject,
    mut v_a_1179_: *mut LeanObject,
    mut v_b_1180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1181_: *mut LeanObject = core::ptr::null_mut();
    v_res_1181_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_1178_, v_a_1179_, v_b_1180_);
    lean_dec(v_b_1180_);
    lean_dec_ref(v_s_1178_);
    return v_res_1181_;
}
pub unsafe fn l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(
    mut v_s_1182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_startInclusive_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    v_startInclusive_1183_ = lean_ctor_get(v_s_1182_, 1);
    v_endExclusive_1184_ = lean_ctor_get(v_s_1182_, 2);
    v_searcher_1185_ = lean_nat_sub(v_endExclusive_1184_, v_startInclusive_1183_);
    v___x_1186_ = lean_box(0);
    v___x_1187_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_1182_, v_searcher_1185_, v___x_1186_);
    return v___x_1187_;
}
pub unsafe fn l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0___boxed(
    mut v_s_1188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1189_: *mut LeanObject = core::ptr::null_mut();
    v_res_1189_ = l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(v_s_1188_);
    lean_dec_ref(v_s_1188_);
    return v_res_1189_;
}
pub unsafe fn l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(
    mut v_p_1190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1199_: u8 = 0;
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1203_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1191_ = lean_unsigned_to_nat(0);
                v___x_1192_ = lean_string_utf8_byte_size(v_p_1190_);
                v___x_1193_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1193_, 0, v_p_1190_);
                lean_ctor_set(v___x_1193_, 1, v___x_1191_);
                lean_ctor_set(v___x_1193_, 2, v___x_1192_);
                v___x_1194_ = l_String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0(v___x_1193_);
                lean_dec_ref_known(v___x_1193_, 3);
                if lean_obj_tag(v___x_1194_) == 0 {
                    v___x_1195_ = lean_box(0);
                    return v___x_1195_;
                } else {
                    v_val_1196_ = lean_ctor_get(v___x_1194_, 0);
                    v_isSharedCheck_1203_ = (!lean_is_exclusive(v___x_1194_)) as u8;
                    if v_isSharedCheck_1203_ == 0 {
                        v___x_1198_ = v___x_1194_;
                        v_isShared_1199_ = v_isSharedCheck_1203_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1196_);
                        lean_dec(v___x_1194_);
                        v___x_1198_ = lean_box(0);
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
                    v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_val_1196_);
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
    mut v_s_1204_: *mut LeanObject,
    mut v_inst_1205_: *mut LeanObject,
    mut v_R_1206_: *mut LeanObject,
    mut v_a_1207_: *mut LeanObject,
    mut v_b_1208_: *mut LeanObject,
    mut v_c_1209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    v___x_1210_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___redArg(v_s_1204_, v_a_1207_, v_b_1208_);
    return v___x_1210_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0___boxed(
    mut v_s_1211_: *mut LeanObject,
    mut v_inst_1212_: *mut LeanObject,
    mut v_R_1213_: *mut LeanObject,
    mut v_a_1214_: *mut LeanObject,
    mut v_b_1215_: *mut LeanObject,
    mut v_c_1216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1217_: *mut LeanObject = core::ptr::null_mut();
    v_res_1217_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00__private_Init_System_FilePath_0__System_FilePath_posOfLastSep_spec__0_spec__0(v_s_1211_, v_inst_1212_, v_R_1213_, v_a_1214_, v_b_1215_, v_c_1216_);
    lean_dec(v_b_1215_);
    lean_dec_ref(v_s_1211_);
    return v_res_1217_;
}
pub unsafe fn l___private_Init_System_FilePath_0__System_FilePath_afterRootDirectory(
    mut v_p_1218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1221_: u32 = 0;
    let mut v___x_1222_: u8 = 0;
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: u32 = 0;
    let mut v_val_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1219_ = l_System_FilePath_pathSeparators;
                v___x_1233_ = lean_unsigned_to_nat(0);
                v___x_1234_ = lean_string_utf8_byte_size(v_p_1218_);
                lean_inc_ref(v_p_1218_);
                v___x_1235_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1235_, 0, v_p_1218_);
                lean_ctor_set(v___x_1235_, 1, v___x_1233_);
                lean_ctor_set(v___x_1235_, 2, v___x_1234_);
                v___x_1236_ = l_String_Slice_Pos_get_x3f(v___x_1235_, v___x_1233_);
                lean_dec_ref_known(v___x_1235_, 3);
                if lean_obj_tag(v___x_1236_) == 0 {
                    v___x_1237_ = 65;
                    v___y_1221_ = v___x_1237_;
                    state = 1;
                    continue;
                } else {
                    v_val_1238_ = lean_ctor_get(v___x_1236_, 0);
                    lean_inc(v_val_1238_);
                    lean_dec_ref_known(v___x_1236_, 1);
                    v___x_1239_ = lean_unbox_uint32(v_val_1238_);
                    lean_dec(v_val_1238_);
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
                    v___x_1223_ = lean_unsigned_to_nat(0);
                    v___x_1224_ = lean_unsigned_to_nat(3);
                    v___x_1225_ = lean_string_utf8_byte_size(v_p_1218_);
                    v___x_1226_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1226_, 0, v_p_1218_);
                    lean_ctor_set(v___x_1226_, 1, v___x_1223_);
                    lean_ctor_set(v___x_1226_, 2, v___x_1225_);
                    v___x_1227_ = l_String_Slice_Pos_nextn(v___x_1226_, v___x_1223_, v___x_1224_);
                    lean_dec_ref_known(v___x_1226_, 3);
                    return v___x_1227_;
                } else {
                    v___x_1228_ = lean_unsigned_to_nat(0);
                    v___x_1229_ = lean_unsigned_to_nat(1);
                    v___x_1230_ = lean_string_utf8_byte_size(v_p_1218_);
                    v___x_1231_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1231_, 0, v_p_1218_);
                    lean_ctor_set(v___x_1231_, 1, v___x_1228_);
                    lean_ctor_set(v___x_1231_, 2, v___x_1230_);
                    v___x_1232_ = l_String_Slice_Pos_nextn(v___x_1231_, v___x_1228_, v___x_1229_);
                    lean_dec_ref_known(v___x_1231_, 3);
                    return v___x_1232_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_System_FilePath_parent(mut v_p_1240_: *mut LeanObject) -> *mut LeanObject {
    let mut v___y_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: u8 = 0;
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: u8 = 0;
    let mut v_afterRootDirectory_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: u8 = 0;
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1267_: u8 = 0;
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1271_: u8 = 0;
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_p_1240_);
                v___x_1251_ =
                    l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(v_p_1240_);
                if lean_obj_tag(v___x_1251_) == 0 {
                    v___x_1273_ = lean_box(0);
                    v___y_1253_ = v___x_1273_;
                    state = 2;
                    continue;
                } else {
                    v_val_1274_ = lean_ctor_get(v___x_1251_, 0);
                    lean_inc(v_val_1274_);
                    v___x_1275_ = lean_unsigned_to_nat(0);
                    v___x_1276_ = lean_string_utf8_extract(v_p_1240_, v___x_1275_, v_val_1274_);
                    lean_dec(v_val_1274_);
                    v___x_1277_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1277_, 0, v___x_1276_);
                    v___y_1253_ = v___x_1277_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                lean_inc(v___y_1242_);
                v___x_1246_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1246_, 0, v___y_1242_);
                v___x_1247_ =
                    l_Option_instDecidableEq___redArg(v___y_1243_, v___y_1245_, v___x_1246_);
                if v___x_1247_ == 0 {
                    lean_dec(v___y_1242_);
                    lean_dec_ref(v_p_1240_);
                    return v___y_1244_;
                } else {
                    lean_dec(v___y_1244_);
                    v___x_1248_ = lean_unsigned_to_nat(0);
                    v___x_1249_ = lean_string_utf8_extract(v_p_1240_, v___x_1248_, v___y_1242_);
                    lean_dec(v___y_1242_);
                    lean_dec_ref(v_p_1240_);
                    v___x_1250_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1250_, 0, v___x_1249_);
                    return v___x_1250_;
                }
            }
            2 => {
                lean_inc_ref(v_p_1240_);
                v___x_1254_ = l_System_FilePath_isAbsolute(v_p_1240_);
                if v___x_1254_ == 0 {
                    lean_dec(v___x_1251_);
                    lean_dec_ref(v_p_1240_);
                    return v___y_1253_;
                } else {
                    lean_inc_ref(v_p_1240_);
                    v_afterRootDirectory_1255_ =
                        l___private_Init_System_FilePath_0__System_FilePath_afterRootDirectory(
                            v_p_1240_,
                        );
                    v___x_1256_ = lean_string_utf8_byte_size(v_p_1240_);
                    v___x_1257_ = lean_nat_dec_eq(v_afterRootDirectory_1255_, v___x_1256_);
                    if v___x_1257_ == 0 {
                        lean_inc_ref(v_p_1240_);
                        v___x_1258_ = lean_alloc_closure(
                            l_String_instDecidableEqPos___boxed as *mut core::ffi::c_void,
                            3,
                            1,
                        );
                        lean_closure_set(v___x_1258_, 0, v_p_1240_);
                        if lean_obj_tag(v___x_1251_) == 0 {
                            v___y_1242_ = v_afterRootDirectory_1255_;
                            v___y_1243_ = v___x_1258_;
                            v___y_1244_ = v___y_1253_;
                            v___y_1245_ = v___x_1251_;
                            state = 1;
                            continue;
                        } else {
                            v_val_1259_ = lean_ctor_get(v___x_1251_, 0);
                            lean_inc(v_val_1259_);
                            lean_dec_ref_known(v___x_1251_, 1);
                            v___x_1260_ = lean_unsigned_to_nat(0);
                            lean_inc_ref(v_p_1240_);
                            v___x_1261_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v___x_1261_, 0, v_p_1240_);
                            lean_ctor_set(v___x_1261_, 1, v___x_1260_);
                            lean_ctor_set(v___x_1261_, 2, v___x_1256_);
                            v___x_1262_ = l_String_Slice_Pos_next_x3f(v___x_1261_, v_val_1259_);
                            lean_dec(v_val_1259_);
                            lean_dec_ref_known(v___x_1261_, 3);
                            if lean_obj_tag(v___x_1262_) == 0 {
                                v___x_1263_ = lean_box(0);
                                v___y_1242_ = v_afterRootDirectory_1255_;
                                v___y_1243_ = v___x_1258_;
                                v___y_1244_ = v___y_1253_;
                                v___y_1245_ = v___x_1263_;
                                state = 1;
                                continue;
                            } else {
                                v_val_1264_ = lean_ctor_get(v___x_1262_, 0);
                                v_isSharedCheck_1271_ = (!lean_is_exclusive(v___x_1262_)) as u8;
                                if v_isSharedCheck_1271_ == 0 {
                                    v___x_1266_ = v___x_1262_;
                                    v_isShared_1267_ = v_isSharedCheck_1271_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_val_1264_);
                                    lean_dec(v___x_1262_);
                                    v___x_1266_ = lean_box(0);
                                    v_isShared_1267_ = v_isSharedCheck_1271_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_afterRootDirectory_1255_);
                        lean_dec(v___y_1253_);
                        lean_dec(v___x_1251_);
                        lean_dec_ref(v_p_1240_);
                        v___x_1272_ = lean_box(0);
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
                    v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_val_1264_);
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
pub unsafe fn l_System_FilePath_fileName(mut v_p_1280_: *mut LeanObject) -> *mut LeanObject {
    let mut v___y_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1283_: u8 = 0;
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: u8 = 0;
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: u8 = 0;
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: u8 = 0;
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_p_1280_);
                v___x_1296_ =
                    l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(v_p_1280_);
                if lean_obj_tag(v___x_1296_) == 0 {
                    v___y_1290_ = v_p_1280_;
                    state = 2;
                    continue;
                } else {
                    v_val_1297_ = lean_ctor_get(v___x_1296_, 0);
                    lean_inc(v_val_1297_);
                    lean_dec_ref_known(v___x_1296_, 1);
                    v___x_1298_ = lean_unsigned_to_nat(0);
                    v___x_1299_ = lean_string_utf8_byte_size(v_p_1280_);
                    lean_inc_ref(v_p_1280_);
                    v___x_1300_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1300_, 0, v_p_1280_);
                    lean_ctor_set(v___x_1300_, 1, v___x_1298_);
                    lean_ctor_set(v___x_1300_, 2, v___x_1299_);
                    v___x_1301_ = l_String_Slice_Pos_next_x21(v___x_1300_, v_val_1297_);
                    lean_dec(v_val_1297_);
                    lean_dec_ref_known(v___x_1300_, 3);
                    v___x_1302_ = lean_string_utf8_extract(v_p_1280_, v___x_1301_, v___x_1299_);
                    lean_dec(v___x_1301_);
                    lean_dec_ref(v_p_1280_);
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
                        v___x_1286_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1286_, 0, v___y_1282_);
                        return v___x_1286_;
                    } else {
                        lean_dec_ref(v___y_1282_);
                        v___x_1287_ = lean_box(0);
                        return v___x_1287_;
                    }
                } else {
                    lean_dec_ref(v___y_1282_);
                    v___x_1288_ = lean_box(0);
                    return v___x_1288_;
                }
            }
            2 => {
                v___x_1291_ = lean_string_utf8_byte_size(v___y_1290_);
                v___x_1292_ = lean_unsigned_to_nat(0);
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
    mut v_s_1303_: *mut LeanObject,
    mut v_a_1304_: *mut LeanObject,
    mut v_b_1305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: u8 = 0;
    let mut v_str_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: u32 = 0;
    let mut v___x_1318_: u32 = 0;
    let mut v___x_1319_: u8 = 0;
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1306_ = lean_unsigned_to_nat(0);
                v___x_1307_ = lean_nat_dec_eq(v_a_1304_, v___x_1306_);
                if v___x_1307_ == 0 {
                    v_str_1308_ = lean_ctor_get(v_s_1303_, 0);
                    v_startInclusive_1309_ = lean_ctor_get(v_s_1303_, 1);
                    v___x_1310_ = lean_nat_add(v_startInclusive_1309_, v_a_1304_);
                    lean_inc(v___x_1310_);
                    lean_inc(v_startInclusive_1309_);
                    lean_inc_ref(v_str_1308_);
                    v___x_1311_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1311_, 0, v_str_1308_);
                    lean_ctor_set(v___x_1311_, 1, v_startInclusive_1309_);
                    lean_ctor_set(v___x_1311_, 2, v___x_1310_);
                    v___x_1312_ = lean_nat_sub(v___x_1310_, v_startInclusive_1309_);
                    lean_dec(v___x_1310_);
                    v___x_1313_ = lean_unsigned_to_nat(1);
                    v___x_1314_ = lean_nat_sub(v___x_1312_, v___x_1313_);
                    lean_dec(v___x_1312_);
                    v___x_1315_ = l_String_Slice_posLE(v___x_1311_, v___x_1314_);
                    lean_dec_ref_known(v___x_1311_, 3);
                    v___x_1316_ = lean_nat_add(v_startInclusive_1309_, v___x_1315_);
                    v___x_1317_ = lean_string_utf8_get_fast(v_str_1308_, v___x_1316_);
                    lean_dec(v___x_1316_);
                    v___x_1318_ = 46;
                    v___x_1319_ = lean_uint32_dec_eq(v___x_1317_, v___x_1318_);
                    if v___x_1319_ == 0 {
                        lean_dec(v___x_1315_);
                        v___x_1320_ = lean_box(0);
                        v___x_1321_ = lean_nat_sub(v_a_1304_, v___x_1313_);
                        lean_dec(v_a_1304_);
                        v___x_1322_ = l_String_Slice_posLE(v_s_1303_, v___x_1321_);
                        v_a_1304_ = v___x_1322_;
                        v_b_1305_ = v___x_1320_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_a_1304_);
                        v___x_1324_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1324_, 0, v___x_1315_);
                        return v___x_1324_;
                    }
                } else {
                    lean_dec(v_a_1304_);
                    lean_inc(v_b_1305_);
                    return v_b_1305_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg___boxed(
    mut v_s_1325_: *mut LeanObject,
    mut v_a_1326_: *mut LeanObject,
    mut v_b_1327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1328_: *mut LeanObject = core::ptr::null_mut();
    v_res_1328_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_1325_, v_a_1326_, v_b_1327_);
    lean_dec(v_b_1327_);
    lean_dec_ref(v_s_1325_);
    return v_res_1328_;
}
pub unsafe fn l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(
    mut v_s_1329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_startInclusive_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    v_startInclusive_1330_ = lean_ctor_get(v_s_1329_, 1);
    v_endExclusive_1331_ = lean_ctor_get(v_s_1329_, 2);
    v_searcher_1332_ = lean_nat_sub(v_endExclusive_1331_, v_startInclusive_1330_);
    v___x_1333_ = lean_box(0);
    v___x_1334_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_1329_, v_searcher_1332_, v___x_1333_);
    return v___x_1334_;
}
pub unsafe fn l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0___boxed(
    mut v_s_1335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1336_: *mut LeanObject = core::ptr::null_mut();
    v_res_1336_ = l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(v_s_1335_);
    lean_dec_ref(v_s_1335_);
    return v_res_1336_;
}
pub unsafe fn l_System_FilePath_fileStem(mut v_p_1337_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1347_: u8 = 0;
    let mut v___x_1348_: u8 = 0;
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1353_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1338_ = l_System_FilePath_fileName(v_p_1337_);
                if lean_obj_tag(v___x_1338_) == 0 {
                    return v___x_1338_;
                } else {
                    v_val_1339_ = lean_ctor_get(v___x_1338_, 0);
                    lean_inc_n(v_val_1339_, 2);
                    v___x_1340_ = lean_unsigned_to_nat(0);
                    v___x_1341_ = lean_string_utf8_byte_size(v_val_1339_);
                    v___x_1342_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1342_, 0, v_val_1339_);
                    lean_ctor_set(v___x_1342_, 1, v___x_1340_);
                    lean_ctor_set(v___x_1342_, 2, v___x_1341_);
                    v___x_1343_ =
                        l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(
                            v___x_1342_,
                        );
                    lean_dec_ref_known(v___x_1342_, 3);
                    if lean_obj_tag(v___x_1343_) == 0 {
                        lean_dec(v_val_1339_);
                        return v___x_1338_;
                    } else {
                        v_val_1344_ = lean_ctor_get(v___x_1343_, 0);
                        v_isSharedCheck_1353_ = (!lean_is_exclusive(v___x_1343_)) as u8;
                        if v_isSharedCheck_1353_ == 0 {
                            v___x_1346_ = v___x_1343_;
                            v_isShared_1347_ = v_isSharedCheck_1353_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_1344_);
                            lean_dec(v___x_1343_);
                            v___x_1346_ = lean_box(0);
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
                    lean_dec_ref_known(v___x_1338_, 1);
                    v___x_1349_ = lean_string_utf8_extract(v_val_1339_, v___x_1340_, v_val_1344_);
                    lean_dec(v_val_1344_);
                    lean_dec(v_val_1339_);
                    if v_isShared_1347_ == 0 {
                        lean_ctor_set(v___x_1346_, 0, v___x_1349_);
                        v___x_1351_ = v___x_1346_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1349_);
                        v___x_1351_ = v_reuseFailAlloc_1352_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1346_);
                    lean_dec(v_val_1344_);
                    lean_dec(v_val_1339_);
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
    mut v_s_1354_: *mut LeanObject,
    mut v_inst_1355_: *mut LeanObject,
    mut v_R_1356_: *mut LeanObject,
    mut v_a_1357_: *mut LeanObject,
    mut v_b_1358_: *mut LeanObject,
    mut v_c_1359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    v___x_1360_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___redArg(v_s_1354_, v_a_1357_, v_b_1358_);
    return v___x_1360_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0___boxed(
    mut v_s_1361_: *mut LeanObject,
    mut v_inst_1362_: *mut LeanObject,
    mut v_R_1363_: *mut LeanObject,
    mut v_a_1364_: *mut LeanObject,
    mut v_b_1365_: *mut LeanObject,
    mut v_c_1366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1367_: *mut LeanObject = core::ptr::null_mut();
    v_res_1367_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0_spec__0(v_s_1361_, v_inst_1362_, v_R_1363_, v_a_1364_, v_b_1365_, v_c_1366_);
    lean_dec(v_b_1365_);
    lean_dec_ref(v_s_1361_);
    return v_res_1367_;
}
pub unsafe fn _init_l_System_FilePath_extension___closed__0() -> *mut LeanObject {
    let mut v___x_1368_: u32 = 0;
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    v___x_1368_ = 46;
    v___x_1369_ = l_Char_utf8Size(v___x_1368_);
    return v___x_1369_;
}
pub unsafe fn l_System_FilePath_extension(mut v_p_1370_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1381_: u8 = 0;
    let mut v___x_1382_: u8 = 0;
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1390_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1371_ = l_System_FilePath_fileName(v_p_1370_);
                if lean_obj_tag(v___x_1371_) == 0 {
                    return v___x_1371_;
                } else {
                    v_val_1372_ = lean_ctor_get(v___x_1371_, 0);
                    lean_inc_n(v_val_1372_, 2);
                    lean_dec_ref_known(v___x_1371_, 1);
                    v___x_1373_ = lean_unsigned_to_nat(0);
                    v___x_1374_ = lean_string_utf8_byte_size(v_val_1372_);
                    v___x_1375_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1375_, 0, v_val_1372_);
                    lean_ctor_set(v___x_1375_, 1, v___x_1373_);
                    lean_ctor_set(v___x_1375_, 2, v___x_1374_);
                    v___x_1376_ =
                        l_String_Slice_revFind_x3f___at___00System_FilePath_fileStem_spec__0(
                            v___x_1375_,
                        );
                    lean_dec_ref_known(v___x_1375_, 3);
                    if lean_obj_tag(v___x_1376_) == 0 {
                        lean_dec(v_val_1372_);
                        v___x_1377_ = lean_box(0);
                        return v___x_1377_;
                    } else {
                        v_val_1378_ = lean_ctor_get(v___x_1376_, 0);
                        v_isSharedCheck_1390_ = (!lean_is_exclusive(v___x_1376_)) as u8;
                        if v_isSharedCheck_1390_ == 0 {
                            v___x_1380_ = v___x_1376_;
                            v_isShared_1381_ = v_isSharedCheck_1390_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_1378_);
                            lean_dec(v___x_1376_);
                            v___x_1380_ = lean_box(0);
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
                    v___x_1383_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_System_FilePath_extension___closed__0),
                        core::ptr::addr_of_mut!(l_System_FilePath_extension___closed__0_once),
                        _init_l_System_FilePath_extension___closed__0,
                    );
                    v___x_1384_ = lean_nat_add(v_val_1378_, v___x_1383_);
                    lean_dec(v_val_1378_);
                    v___x_1385_ = lean_string_utf8_extract(v_val_1372_, v___x_1384_, v___x_1374_);
                    lean_dec(v___x_1384_);
                    lean_dec(v_val_1372_);
                    if v_isShared_1381_ == 0 {
                        lean_ctor_set(v___x_1380_, 0, v___x_1385_);
                        v___x_1387_ = v___x_1380_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
                        v___x_1387_ = v_reuseFailAlloc_1388_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1380_);
                    lean_dec(v_val_1378_);
                    lean_dec(v_val_1372_);
                    v___x_1389_ = lean_box(0);
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
    mut v_p_1391_: *mut LeanObject,
    mut v_fname_1392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    v___x_1393_ = l_System_FilePath_parent(v_p_1391_);
    if lean_obj_tag(v___x_1393_) == 0 {
        return v_fname_1392_;
    } else {
        let mut v_val_1394_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
        v_val_1394_ = lean_ctor_get(v___x_1393_, 0);
        lean_inc(v_val_1394_);
        lean_dec_ref_known(v___x_1393_, 1);
        v___x_1395_ = l_System_FilePath_join(v_val_1394_, v_fname_1392_);
        return v___x_1395_;
    }
}
pub unsafe fn l_System_FilePath_addExtension(
    mut v_p_1396_: *mut LeanObject,
    mut v_ext_1397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_p_1396_);
    v___x_1398_ = l_System_FilePath_fileName(v_p_1396_);
    if lean_obj_tag(v___x_1398_) == 0 {
        return v_p_1396_;
    } else {
        let mut v_val_1399_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1402_: u8 = 0;
        v_val_1399_ = lean_ctor_get(v___x_1398_, 0);
        lean_inc(v_val_1399_);
        lean_dec_ref_known(v___x_1398_, 1);
        v___x_1400_ = lean_string_utf8_byte_size(v_ext_1397_);
        v___x_1401_ = lean_unsigned_to_nat(0);
        v___x_1402_ = lean_nat_dec_eq(v___x_1400_, v___x_1401_);
        if v___x_1402_ == 0 {
            let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
            v___x_1403_ = l_System_FilePath_fileName___closed__1;
            v___x_1404_ = lean_string_append(v_val_1399_, v___x_1403_);
            v___x_1405_ = lean_string_append(v___x_1404_, v_ext_1397_);
            v___x_1406_ = l_System_FilePath_withFileName(v_p_1396_, v___x_1405_);
            return v___x_1406_;
        } else {
            let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
            v___x_1407_ = l_System_FilePath_withFileName(v_p_1396_, v_val_1399_);
            return v___x_1407_;
        }
    }
}
pub unsafe fn l_System_FilePath_addExtension___boxed(
    mut v_p_1408_: *mut LeanObject,
    mut v_ext_1409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1410_: *mut LeanObject = core::ptr::null_mut();
    v_res_1410_ = l_System_FilePath_addExtension(v_p_1408_, v_ext_1409_);
    lean_dec_ref(v_ext_1409_);
    return v_res_1410_;
}
pub unsafe fn l_System_FilePath_withExtension(
    mut v_p_1411_: *mut LeanObject,
    mut v_ext_1412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_p_1411_);
    v___x_1413_ = l_System_FilePath_fileStem(v_p_1411_);
    if lean_obj_tag(v___x_1413_) == 0 {
        return v_p_1411_;
    } else {
        let mut v_val_1414_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1417_: u8 = 0;
        v_val_1414_ = lean_ctor_get(v___x_1413_, 0);
        lean_inc(v_val_1414_);
        lean_dec_ref_known(v___x_1413_, 1);
        v___x_1415_ = lean_string_utf8_byte_size(v_ext_1412_);
        v___x_1416_ = lean_unsigned_to_nat(0);
        v___x_1417_ = lean_nat_dec_eq(v___x_1415_, v___x_1416_);
        if v___x_1417_ == 0 {
            let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
            v___x_1418_ = l_System_FilePath_fileName___closed__1;
            v___x_1419_ = lean_string_append(v_val_1414_, v___x_1418_);
            v___x_1420_ = lean_string_append(v___x_1419_, v_ext_1412_);
            v___x_1421_ = l_System_FilePath_withFileName(v_p_1411_, v___x_1420_);
            return v___x_1421_;
        } else {
            let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
            v___x_1422_ = l_System_FilePath_withFileName(v_p_1411_, v_val_1414_);
            return v___x_1422_;
        }
    }
}
pub unsafe fn l_System_FilePath_withExtension___boxed(
    mut v_p_1423_: *mut LeanObject,
    mut v_ext_1424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1425_: *mut LeanObject = core::ptr::null_mut();
    v_res_1425_ = l_System_FilePath_withExtension(v_p_1423_, v_ext_1424_);
    lean_dec_ref(v_ext_1424_);
    return v_res_1425_;
}
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    v___x_1426_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_System_FilePath_join___closed__0),
        core::ptr::addr_of_mut!(l_System_FilePath_join___closed__0_once),
        _init_l_System_FilePath_join___closed__0,
    );
    v___x_1427_ = lean_string_utf8_byte_size(v___x_1426_);
    return v___x_1427_;
}
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1()
-> u8 {
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: u8 = 0;
    v___x_1428_ = lean_unsigned_to_nat(0);
    v___x_1429_ = lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once), _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0);
    v___x_1430_ = lean_nat_dec_eq(v___x_1429_, v___x_1428_);
    return v___x_1430_;
}
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    v___x_1431_ = lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0_once), _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__0);
    v___x_1432_ = lean_unsigned_to_nat(0);
    v___x_1433_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_System_FilePath_join___closed__0),
        core::ptr::addr_of_mut!(l_System_FilePath_join___closed__0_once),
        _init_l_System_FilePath_join___closed__0,
    );
    v___x_1434_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1434_, 0, v___x_1433_);
    lean_ctor_set(v___x_1434_, 1, v___x_1432_);
    lean_ctor_set(v___x_1434_, 2, v___x_1431_);
    return v___x_1434_;
}
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    v___x_1435_ = lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2_once), _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2);
    v___x_1436_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1435_);
    return v___x_1436_;
}
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    v___x_1437_ = lean_unsigned_to_nat(0);
    v___x_1438_ = lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3_once), _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__3);
    v___x_1439_ = lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2_once), _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__2);
    v___x_1440_ = lean_alloc_ctor(2, 4, (0) as u32);
    lean_ctor_set(v___x_1440_, 0, v___x_1439_);
    lean_ctor_set(v___x_1440_, 1, v___x_1438_);
    lean_ctor_set(v___x_1440_, 2, v___x_1437_);
    lean_ctor_set(v___x_1440_, 3, v___x_1437_);
    return v___x_1440_;
}
pub unsafe fn _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5()
-> *mut LeanObject {
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    v___x_1441_ = lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4_once), _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__4);
    v___x_1442_ = lean_unsigned_to_nat(0);
    v___x_1443_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1443_, 0, v___x_1442_);
    lean_ctor_set(v___x_1443_, 1, v___x_1441_);
    return v___x_1443_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(
    mut v_s_1449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1450_: u8 = 0;
    v___x_1450_ = lean_uint8_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1_once), _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__1);
    if v___x_1450_ == 0 {
        let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
        v___x_1451_ = lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5), core::ptr::addr_of_mut!(l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5_once), _init_l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__5);
        return v___x_1451_;
    } else {
        let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
        v___x_1452_ =
            l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___closed__7;
        return v___x_1452_;
    }
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0___boxed(
    mut v_s_1453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1454_: *mut LeanObject = core::ptr::null_mut();
    v_res_1454_ =
        l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(v_s_1453_);
    lean_dec_ref(v_s_1453_);
    return v_res_1454_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(
    mut v___x_1455_: *mut LeanObject,
    mut v___x_1456_: *mut LeanObject,
    mut v___x_1457_: *mut LeanObject,
    mut v_a_1458_: *mut LeanObject,
    mut v_b_1459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currPos_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1472_: u8 = 0;
    let mut v_it_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startPos_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_slice_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1488_: u8 = 0;
    let mut v_nextIt_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1492_: u8 = 0;
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1498_: u8 = 0;
    let mut v_startInclusive_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: u8 = 0;
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1507_: u8 = 0;
    let mut v_pos_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1511_: u8 = 0;
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1516_: u8 = 0;
    let mut v_needle_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_table_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stackPos_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_needlePos_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1523_: u8 = 0;
    let mut v_str_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_basePos_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: u8 = 0;
    let mut v___x_1531_: u8 = 0;
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stackByte_1533_: u8 = 0;
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_patByte_1535_: u8 = 0;
    let mut v___x_1536_: u8 = 0;
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: u8 = 0;
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNeedlePos_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: u8 = 0;
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextNeedlePos_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: u8 = 0;
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1572_: u8 = 0;
    let mut v_isSharedCheck_1573_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1458_) == 0 {
                    v_currPos_1468_ = lean_ctor_get(v_a_1458_, 0);
                    v_searcher_1469_ = lean_ctor_get(v_a_1458_, 1);
                    v_isSharedCheck_1573_ = (!lean_is_exclusive(v_a_1458_)) as u8;
                    if v_isSharedCheck_1573_ == 0 {
                        v___x_1471_ = v_a_1458_;
                        v_isShared_1472_ = v_isSharedCheck_1573_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_searcher_1469_);
                        lean_inc(v_currPos_1468_);
                        lean_dec(v_a_1458_);
                        v___x_1471_ = lean_box(0);
                        v_isShared_1472_ = v_isSharedCheck_1573_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1457_);
                    lean_dec_ref(v___x_1455_);
                    return v_b_1459_;
                }
            }
            1 => {
                lean_inc_ref(v___x_1455_);
                v___x_1464_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1464_, 0, v___x_1455_);
                lean_ctor_set(v___x_1464_, 1, v_startInclusive_1462_);
                lean_ctor_set(v___x_1464_, 2, v_endExclusive_1463_);
                v___x_1465_ = l_String_Slice_toString(v___x_1464_);
                lean_dec_ref_known(v___x_1464_, 3);
                v___x_1466_ = lean_array_push(v_b_1459_, v___x_1465_);
                v_a_1458_ = v_it_1461_;
                v_b_1459_ = v___x_1466_;
                state = 0;
                continue;
            }
            2 => match lean_obj_tag(v_searcher_1469_) {
                0 => {
                    lean_del_object(v___x_1471_);
                    v_pos_1495_ = lean_ctor_get(v_searcher_1469_, 0);
                    v_isSharedCheck_1507_ = (!lean_is_exclusive(v_searcher_1469_)) as u8;
                    if v_isSharedCheck_1507_ == 0 {
                        v___x_1497_ = v_searcher_1469_;
                        v_isShared_1498_ = v_isSharedCheck_1507_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_pos_1495_);
                        lean_dec(v_searcher_1469_);
                        v___x_1497_ = lean_box(0);
                        v_isShared_1498_ = v_isSharedCheck_1507_;
                        state = 9;
                        continue;
                    }
                }
                1 => {
                    v_pos_1508_ = lean_ctor_get(v_searcher_1469_, 0);
                    v_isSharedCheck_1516_ = (!lean_is_exclusive(v_searcher_1469_)) as u8;
                    if v_isSharedCheck_1516_ == 0 {
                        v___x_1510_ = v_searcher_1469_;
                        v_isShared_1511_ = v_isSharedCheck_1516_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_pos_1508_);
                        lean_dec(v_searcher_1469_);
                        v___x_1510_ = lean_box(0);
                        v_isShared_1511_ = v_isSharedCheck_1516_;
                        state = 11;
                        continue;
                    }
                }
                2 => {
                    v_needle_1517_ = lean_ctor_get(v_searcher_1469_, 0);
                    v_table_1518_ = lean_ctor_get(v_searcher_1469_, 1);
                    v_stackPos_1519_ = lean_ctor_get(v_searcher_1469_, 2);
                    v_needlePos_1520_ = lean_ctor_get(v_searcher_1469_, 3);
                    v_isSharedCheck_1572_ = (!lean_is_exclusive(v_searcher_1469_)) as u8;
                    if v_isSharedCheck_1572_ == 0 {
                        v___x_1522_ = v_searcher_1469_;
                        v_isShared_1523_ = v_isSharedCheck_1572_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_needlePos_1520_);
                        lean_inc(v_stackPos_1519_);
                        lean_inc(v_table_1518_);
                        lean_inc(v_needle_1517_);
                        lean_dec(v_searcher_1469_);
                        v___x_1522_ = lean_box(0);
                        v_isShared_1523_ = v_isSharedCheck_1572_;
                        state = 13;
                        continue;
                    }
                }
                _ => {
                    lean_del_object(v___x_1471_);
                    state = 8;
                    continue;
                }
            },
            3 => {
                if v_isShared_1472_ == 0 {
                    lean_ctor_set(v___x_1471_, 1, v_it_1474_);
                    v___x_1476_ = v___x_1471_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_currPos_1468_);
                    lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_it_1474_);
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
                v_startInclusive_1484_ = lean_ctor_get(v_slice_1483_, 0);
                v_endExclusive_1485_ = lean_ctor_get(v_slice_1483_, 1);
                v_isSharedCheck_1492_ = (!lean_is_exclusive(v_slice_1483_)) as u8;
                if v_isSharedCheck_1492_ == 0 {
                    v___x_1487_ = v_slice_1483_;
                    v_isShared_1488_ = v_isSharedCheck_1492_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_endExclusive_1485_);
                    lean_inc(v_startInclusive_1484_);
                    lean_dec(v_slice_1483_);
                    v___x_1487_ = lean_box(0);
                    v_isShared_1488_ = v_isSharedCheck_1492_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1488_ == 0 {
                    lean_ctor_set(v___x_1487_, 1, v_it_1480_);
                    lean_ctor_set(v___x_1487_, 0, v_endPos_1482_);
                    v_nextIt_1490_ = v___x_1487_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_endPos_1482_);
                    lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_it_1480_);
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
                v___x_1494_ = lean_box(1);
                lean_inc(v___x_1457_);
                v_it_1461_ = v___x_1494_;
                v_startInclusive_1462_ = v_currPos_1468_;
                v_endExclusive_1463_ = v___x_1457_;
                state = 1;
                continue;
            }
            9 => {
                v_startInclusive_1499_ = lean_ctor_get(v___x_1456_, 1);
                v_endExclusive_1500_ = lean_ctor_get(v___x_1456_, 2);
                v___x_1501_ = lean_nat_sub(v_endExclusive_1500_, v_startInclusive_1499_);
                v___x_1502_ = lean_nat_dec_eq(v_pos_1495_, v___x_1501_);
                lean_dec(v___x_1501_);
                if v___x_1502_ == 0 {
                    lean_inc(v_pos_1495_);
                    if v_isShared_1498_ == 0 {
                        lean_ctor_set_tag(v___x_1497_, 1);
                        v___x_1504_ = v___x_1497_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_pos_1495_);
                        v___x_1504_ = v_reuseFailAlloc_1505_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1497_);
                    v___x_1506_ = lean_box(3);
                    lean_inc(v_pos_1495_);
                    v_it_1480_ = v___x_1506_;
                    v_startPos_1481_ = v_pos_1495_;
                    v_endPos_1482_ = v_pos_1495_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                lean_inc(v_pos_1495_);
                v_it_1480_ = v___x_1504_;
                v_startPos_1481_ = v_pos_1495_;
                v_endPos_1482_ = v_pos_1495_;
                state = 5;
                continue;
            }
            11 => {
                v___x_1512_ = lean_string_utf8_next_fast(v___x_1455_, v_pos_1508_);
                lean_dec(v_pos_1508_);
                if v_isShared_1511_ == 0 {
                    lean_ctor_set_tag(v___x_1510_, 0);
                    lean_ctor_set(v___x_1510_, 0, v___x_1512_);
                    v___x_1514_ = v___x_1510_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1512_);
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
                v_str_1524_ = lean_ctor_get(v_needle_1517_, 0);
                v_startInclusive_1525_ = lean_ctor_get(v_needle_1517_, 1);
                v_endExclusive_1526_ = lean_ctor_get(v_needle_1517_, 2);
                v_basePos_1527_ = lean_nat_sub(v_stackPos_1519_, v_needlePos_1520_);
                v___x_1528_ = lean_nat_sub(v_endExclusive_1526_, v_startInclusive_1525_);
                v___x_1529_ = lean_nat_add(v_basePos_1527_, v___x_1528_);
                v___x_1530_ = lean_nat_dec_le(v___x_1529_, v___x_1457_);
                lean_dec(v___x_1529_);
                if v___x_1530_ == 0 {
                    lean_dec(v___x_1528_);
                    lean_del_object(v___x_1522_);
                    lean_dec(v_needlePos_1520_);
                    lean_dec(v_stackPos_1519_);
                    lean_dec_ref(v_table_1518_);
                    lean_dec_ref(v_needle_1517_);
                    v___x_1531_ = lean_nat_dec_lt(v_basePos_1527_, v___x_1457_);
                    lean_dec(v_basePos_1527_);
                    if v___x_1531_ == 0 {
                        lean_del_object(v___x_1471_);
                        state = 8;
                        continue;
                    } else {
                        v___x_1532_ = lean_box(3);
                        v_it_1474_ = v___x_1532_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_basePos_1527_);
                    lean_inc(v_stackPos_1519_);
                    v_stackByte_1533_ = lean_string_get_byte_fast(v___x_1455_, v_stackPos_1519_);
                    v___x_1534_ = lean_nat_add(v_startInclusive_1525_, v_needlePos_1520_);
                    v_patByte_1535_ = lean_string_get_byte_fast(v_str_1524_, v___x_1534_);
                    v___x_1536_ = lean_uint8_dec_eq(v_stackByte_1533_, v_patByte_1535_);
                    if v___x_1536_ == 0 {
                        lean_dec(v___x_1528_);
                        v___x_1537_ = lean_unsigned_to_nat(0);
                        v___x_1538_ = lean_nat_dec_eq(v_needlePos_1520_, v___x_1537_);
                        if v___x_1538_ == 0 {
                            v___x_1539_ = lean_unsigned_to_nat(1);
                            v___x_1540_ = lean_nat_sub(v_needlePos_1520_, v___x_1539_);
                            lean_dec(v_needlePos_1520_);
                            v_newNeedlePos_1541_ =
                                lean_array_fget_borrowed(v_table_1518_, v___x_1540_);
                            lean_dec(v___x_1540_);
                            v___x_1542_ = lean_nat_dec_eq(v_newNeedlePos_1541_, v___x_1537_);
                            if v___x_1542_ == 0 {
                                lean_inc(v_newNeedlePos_1541_);
                                if v_isShared_1523_ == 0 {
                                    lean_ctor_set(v___x_1522_, 3, v_newNeedlePos_1541_);
                                    v___x_1544_ = v___x_1522_;
                                    state = 14;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1545_ = lean_alloc_ctor(2, 4, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_needle_1517_);
                                    lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_table_1518_);
                                    lean_ctor_set(v_reuseFailAlloc_1545_, 2, v_stackPos_1519_);
                                    lean_ctor_set(v_reuseFailAlloc_1545_, 3, v_newNeedlePos_1541_);
                                    v___x_1544_ = v_reuseFailAlloc_1545_;
                                    state = 14;
                                    continue;
                                }
                            } else {
                                v_nextStackPos_1546_ =
                                    l_String_Slice_posGE___redArg(v___x_1456_, v_stackPos_1519_);
                                if v_isShared_1523_ == 0 {
                                    lean_ctor_set(v___x_1522_, 3, v___x_1537_);
                                    lean_ctor_set(v___x_1522_, 2, v_nextStackPos_1546_);
                                    v___x_1548_ = v___x_1522_;
                                    state = 15;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1549_ = lean_alloc_ctor(2, 4, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_needle_1517_);
                                    lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_table_1518_);
                                    lean_ctor_set(v_reuseFailAlloc_1549_, 2, v_nextStackPos_1546_);
                                    lean_ctor_set(v_reuseFailAlloc_1549_, 3, v___x_1537_);
                                    v___x_1548_ = v_reuseFailAlloc_1549_;
                                    state = 15;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_needlePos_1520_);
                            v___x_1550_ = lean_unsigned_to_nat(1);
                            v___x_1551_ = lean_nat_add(v_stackPos_1519_, v___x_1550_);
                            lean_dec(v_stackPos_1519_);
                            v_nextStackPos_1552_ =
                                l_String_Slice_posGE___redArg(v___x_1456_, v___x_1551_);
                            if v_isShared_1523_ == 0 {
                                lean_ctor_set(v___x_1522_, 3, v___x_1537_);
                                lean_ctor_set(v___x_1522_, 2, v_nextStackPos_1552_);
                                v___x_1554_ = v___x_1522_;
                                state = 16;
                                continue;
                            } else {
                                v_reuseFailAlloc_1555_ = lean_alloc_ctor(2, 4, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_needle_1517_);
                                lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_table_1518_);
                                lean_ctor_set(v_reuseFailAlloc_1555_, 2, v_nextStackPos_1552_);
                                lean_ctor_set(v_reuseFailAlloc_1555_, 3, v___x_1537_);
                                v___x_1554_ = v_reuseFailAlloc_1555_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_1471_);
                        v___x_1556_ = lean_unsigned_to_nat(1);
                        v_nextStackPos_1557_ = lean_nat_add(v_stackPos_1519_, v___x_1556_);
                        lean_dec(v_stackPos_1519_);
                        v_nextNeedlePos_1558_ = lean_nat_add(v_needlePos_1520_, v___x_1556_);
                        lean_dec(v_needlePos_1520_);
                        v___x_1559_ = lean_nat_dec_eq(v_nextNeedlePos_1558_, v___x_1528_);
                        lean_dec(v___x_1528_);
                        if v___x_1559_ == 0 {
                            if v_isShared_1523_ == 0 {
                                lean_ctor_set(v___x_1522_, 3, v_nextNeedlePos_1558_);
                                lean_ctor_set(v___x_1522_, 2, v_nextStackPos_1557_);
                                v___x_1561_ = v___x_1522_;
                                state = 17;
                                continue;
                            } else {
                                v_reuseFailAlloc_1564_ = lean_alloc_ctor(2, 4, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_needle_1517_);
                                lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_table_1518_);
                                lean_ctor_set(v_reuseFailAlloc_1564_, 2, v_nextStackPos_1557_);
                                lean_ctor_set(v_reuseFailAlloc_1564_, 3, v_nextNeedlePos_1558_);
                                v___x_1561_ = v_reuseFailAlloc_1564_;
                                state = 17;
                                continue;
                            }
                        } else {
                            v___x_1565_ = lean_nat_sub(v_nextStackPos_1557_, v_nextNeedlePos_1558_);
                            lean_dec(v_nextNeedlePos_1558_);
                            v___x_1566_ = l_String_Slice_pos_x21(v___x_1456_, v___x_1565_);
                            lean_dec(v___x_1565_);
                            v___x_1567_ = l_String_Slice_pos_x21(v___x_1456_, v_nextStackPos_1557_);
                            v___x_1568_ = lean_unsigned_to_nat(0);
                            if v_isShared_1523_ == 0 {
                                lean_ctor_set(v___x_1522_, 3, v___x_1568_);
                                lean_ctor_set(v___x_1522_, 2, v_nextStackPos_1557_);
                                v___x_1570_ = v___x_1522_;
                                state = 18;
                                continue;
                            } else {
                                v_reuseFailAlloc_1571_ = lean_alloc_ctor(2, 4, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_needle_1517_);
                                lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_table_1518_);
                                lean_ctor_set(v_reuseFailAlloc_1571_, 2, v_nextStackPos_1557_);
                                lean_ctor_set(v_reuseFailAlloc_1571_, 3, v___x_1568_);
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
                v___x_1562_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1562_, 0, v_currPos_1468_);
                lean_ctor_set(v___x_1562_, 1, v___x_1561_);
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
    mut v___x_1574_: *mut LeanObject,
    mut v___x_1575_: *mut LeanObject,
    mut v___x_1576_: *mut LeanObject,
    mut v_a_1577_: *mut LeanObject,
    mut v_b_1578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1579_: *mut LeanObject = core::ptr::null_mut();
    v_res_1579_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_1574_, v___x_1575_, v___x_1576_, v_a_1577_, v_b_1578_);
    lean_dec_ref(v___x_1575_);
    return v_res_1579_;
}
pub unsafe fn l_System_FilePath_components(mut v_p_1582_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    v___x_1583_ = l_System_FilePath_normalize(v_p_1582_);
    v___x_1584_ = lean_unsigned_to_nat(0);
    v___x_1585_ = lean_string_utf8_byte_size(v___x_1583_);
    lean_inc_ref(v___x_1583_);
    v___x_1586_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1586_, 0, v___x_1583_);
    lean_ctor_set(v___x_1586_, 1, v___x_1584_);
    lean_ctor_set(v___x_1586_, 2, v___x_1585_);
    v___x_1587_ =
        l_String_Slice_splitToSubslice___at___00System_FilePath_components_spec__0(v___x_1586_);
    v___x_1588_ = l_System_FilePath_components___closed__0;
    v___x_1589_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_1583_, v___x_1586_, v___x_1585_, v___x_1587_, v___x_1588_);
    lean_dec_ref_known(v___x_1586_, 3);
    v___x_1590_ = lean_array_to_list(v___x_1589_);
    return v___x_1590_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(
    mut v___x_1591_: *mut LeanObject,
    mut v___x_1592_: *mut LeanObject,
    mut v___x_1593_: *mut LeanObject,
    mut v_inst_1594_: *mut LeanObject,
    mut v_R_1595_: *mut LeanObject,
    mut v_a_1596_: *mut LeanObject,
    mut v_b_1597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    v___x_1598_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___redArg(v___x_1591_, v___x_1592_, v___x_1593_, v_a_1596_, v_b_1597_);
    return v___x_1598_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1___boxed(
    mut v___x_1599_: *mut LeanObject,
    mut v___x_1600_: *mut LeanObject,
    mut v___x_1601_: *mut LeanObject,
    mut v_inst_1602_: *mut LeanObject,
    mut v_R_1603_: *mut LeanObject,
    mut v_a_1604_: *mut LeanObject,
    mut v_b_1605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1606_: *mut LeanObject = core::ptr::null_mut();
    v_res_1606_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_FilePath_components_spec__1(v___x_1599_, v___x_1600_, v___x_1601_, v_inst_1602_, v_R_1603_, v_a_1604_, v_b_1605_);
    lean_dec_ref(v___x_1600_);
    return v_res_1606_;
}
pub unsafe fn l_System_mkFilePath(mut v_parts_1607_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    v___x_1608_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_System_FilePath_join___closed__0),
        core::ptr::addr_of_mut!(l_System_FilePath_join___closed__0_once),
        _init_l_System_FilePath_join___closed__0,
    );
    v___x_1609_ = l_String_intercalate(v___x_1608_, v_parts_1607_);
    return v___x_1609_;
}
pub unsafe fn l_System_instCoeStringFilePath___lam__0(
    mut v_toString_1610_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_toString_1610_);
    return v_toString_1610_;
}
pub unsafe fn l_System_instCoeStringFilePath___lam__0___boxed(
    mut v_toString_1611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1612_: *mut LeanObject = core::ptr::null_mut();
    v_res_1612_ = l_System_instCoeStringFilePath___lam__0(v_toString_1611_);
    lean_dec_ref(v_toString_1611_);
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
    mut v_s_1620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    v___x_1621_ =
        l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___closed__0;
    return v___x_1621_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0___boxed(
    mut v_s_1622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1623_: *mut LeanObject = core::ptr::null_mut();
    v_res_1623_ =
        l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(v_s_1622_);
    lean_dec_ref(v_s_1622_);
    return v_res_1623_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(
    mut v_s_1624_: *mut LeanObject,
    mut v___x_1625_: *mut LeanObject,
    mut v___x_1626_: *mut LeanObject,
    mut v_a_1627_: *mut LeanObject,
    mut v_b_1628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currPos_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1640_: u8 = 0;
    let mut v_startInclusive_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: u8 = 0;
    let mut v___x_1645_: u32 = 0;
    let mut v___x_1646_: u32 = 0;
    let mut v___x_1647_: u8 = 0;
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_slice_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1663_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1627_) == 0 {
                    v_currPos_1636_ = lean_ctor_get(v_a_1627_, 0);
                    v_searcher_1637_ = lean_ctor_get(v_a_1627_, 1);
                    v_isSharedCheck_1663_ = (!lean_is_exclusive(v_a_1627_)) as u8;
                    if v_isSharedCheck_1663_ == 0 {
                        v___x_1639_ = v_a_1627_;
                        v_isShared_1640_ = v_isSharedCheck_1663_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_searcher_1637_);
                        lean_inc(v_currPos_1636_);
                        lean_dec(v_a_1627_);
                        v___x_1639_ = lean_box(0);
                        v_isShared_1640_ = v_isSharedCheck_1663_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1626_);
                    return v_b_1628_;
                }
            }
            1 => {
                v___x_1633_ = lean_string_utf8_extract(
                    v_s_1624_,
                    v_startInclusive_1631_,
                    v_endExclusive_1632_,
                );
                lean_dec(v_endExclusive_1632_);
                lean_dec(v_startInclusive_1631_);
                v___x_1634_ = lean_array_push(v_b_1628_, v___x_1633_);
                v_a_1627_ = v_it_1630_;
                v_b_1628_ = v___x_1634_;
                state = 0;
                continue;
            }
            2 => {
                v_startInclusive_1641_ = lean_ctor_get(v___x_1625_, 1);
                v_endExclusive_1642_ = lean_ctor_get(v___x_1625_, 2);
                v___x_1643_ = lean_nat_sub(v_endExclusive_1642_, v_startInclusive_1641_);
                v___x_1644_ = lean_nat_dec_eq(v_searcher_1637_, v___x_1643_);
                lean_dec(v___x_1643_);
                if v___x_1644_ == 0 {
                    v___x_1645_ = l_System_SearchPath_separator;
                    v___x_1646_ = lean_string_utf8_get_fast(v_s_1624_, v_searcher_1637_);
                    v___x_1647_ = lean_uint32_dec_eq(v___x_1646_, v___x_1645_);
                    if v___x_1647_ == 0 {
                        v___x_1648_ = lean_string_utf8_next_fast(v_s_1624_, v_searcher_1637_);
                        lean_dec(v_searcher_1637_);
                        if v_isShared_1640_ == 0 {
                            lean_ctor_set(v___x_1639_, 1, v___x_1648_);
                            v___x_1650_ = v___x_1639_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_currPos_1636_);
                            lean_ctor_set(v_reuseFailAlloc_1652_, 1, v___x_1648_);
                            v___x_1650_ = v_reuseFailAlloc_1652_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1653_ = lean_string_utf8_next_fast(v_s_1624_, v_searcher_1637_);
                        v___x_1654_ = lean_nat_sub(v___x_1653_, v_searcher_1637_);
                        v___x_1655_ = lean_nat_add(v_searcher_1637_, v___x_1654_);
                        lean_dec(v___x_1654_);
                        v_slice_1656_ = l_String_Slice_subslice_x21(
                            v___x_1625_,
                            v_currPos_1636_,
                            v_searcher_1637_,
                        );
                        lean_inc(v___x_1655_);
                        if v_isShared_1640_ == 0 {
                            lean_ctor_set(v___x_1639_, 1, v___x_1655_);
                            lean_ctor_set(v___x_1639_, 0, v___x_1655_);
                            v_nextIt_1658_ = v___x_1639_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1655_);
                            lean_ctor_set(v_reuseFailAlloc_1661_, 1, v___x_1655_);
                            v_nextIt_1658_ = v_reuseFailAlloc_1661_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_1639_);
                    lean_dec(v_searcher_1637_);
                    v___x_1662_ = lean_box(1);
                    lean_inc(v___x_1626_);
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
                v_startInclusive_1659_ = lean_ctor_get(v_slice_1656_, 0);
                lean_inc(v_startInclusive_1659_);
                v_endExclusive_1660_ = lean_ctor_get(v_slice_1656_, 1);
                lean_inc(v_endExclusive_1660_);
                lean_dec_ref(v_slice_1656_);
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
    mut v_s_1664_: *mut LeanObject,
    mut v___x_1665_: *mut LeanObject,
    mut v___x_1666_: *mut LeanObject,
    mut v_a_1667_: *mut LeanObject,
    mut v_b_1668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1669_: *mut LeanObject = core::ptr::null_mut();
    v_res_1669_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_1664_, v___x_1665_, v___x_1666_, v_a_1667_, v_b_1668_);
    lean_dec_ref(v___x_1665_);
    lean_dec_ref(v_s_1664_);
    return v_res_1669_;
}
pub unsafe fn l_System_SearchPath_parse(mut v_s_1670_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    v___x_1671_ = lean_unsigned_to_nat(0);
    v___x_1672_ = lean_string_utf8_byte_size(v_s_1670_);
    lean_inc_ref(v_s_1670_);
    v___x_1673_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1673_, 0, v_s_1670_);
    lean_ctor_set(v___x_1673_, 1, v___x_1671_);
    lean_ctor_set(v___x_1673_, 2, v___x_1672_);
    v___x_1674_ =
        l_String_Slice_splitToSubslice___at___00System_SearchPath_parse_spec__0(v___x_1673_);
    v___x_1675_ = l_System_FilePath_components___closed__0;
    v___x_1676_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_1670_, v___x_1673_, v___x_1672_, v___x_1674_, v___x_1675_);
    lean_dec_ref_known(v___x_1673_, 3);
    lean_dec_ref(v_s_1670_);
    v___x_1677_ = lean_array_to_list(v___x_1676_);
    return v___x_1677_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(
    mut v_s_1678_: *mut LeanObject,
    mut v___x_1679_: *mut LeanObject,
    mut v___x_1680_: *mut LeanObject,
    mut v_inst_1681_: *mut LeanObject,
    mut v_R_1682_: *mut LeanObject,
    mut v_a_1683_: *mut LeanObject,
    mut v_b_1684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    v___x_1685_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___redArg(v_s_1678_, v___x_1679_, v___x_1680_, v_a_1683_, v_b_1684_);
    return v___x_1685_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1___boxed(
    mut v_s_1686_: *mut LeanObject,
    mut v___x_1687_: *mut LeanObject,
    mut v___x_1688_: *mut LeanObject,
    mut v_inst_1689_: *mut LeanObject,
    mut v_R_1690_: *mut LeanObject,
    mut v_a_1691_: *mut LeanObject,
    mut v_b_1692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1693_: *mut LeanObject = core::ptr::null_mut();
    v_res_1693_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00System_SearchPath_parse_spec__1(v_s_1686_, v___x_1687_, v___x_1688_, v_inst_1689_, v_R_1690_, v_a_1691_, v_b_1692_);
    lean_dec_ref(v___x_1687_);
    lean_dec_ref(v_s_1686_);
    return v_res_1693_;
}
pub unsafe fn l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(
    mut v_a_1694_: *mut LeanObject,
    mut v_a_1695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1701_: u8 = 0;
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1706_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1694_) == 0 {
                    v___x_1696_ = l_List_reverse___redArg(v_a_1695_);
                    return v___x_1696_;
                } else {
                    v_head_1697_ = lean_ctor_get(v_a_1694_, 0);
                    v_tail_1698_ = lean_ctor_get(v_a_1694_, 1);
                    v_isSharedCheck_1706_ = (!lean_is_exclusive(v_a_1694_)) as u8;
                    if v_isSharedCheck_1706_ == 0 {
                        v___x_1700_ = v_a_1694_;
                        v_isShared_1701_ = v_isSharedCheck_1706_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1698_);
                        lean_inc(v_head_1697_);
                        lean_dec(v_a_1694_);
                        v___x_1700_ = lean_box(0);
                        v_isShared_1701_ = v_isSharedCheck_1706_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1701_ == 0 {
                    lean_ctor_set(v___x_1700_, 1, v_a_1695_);
                    v___x_1703_ = v___x_1700_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_head_1697_);
                    lean_ctor_set(v_reuseFailAlloc_1705_, 1, v_a_1695_);
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
pub unsafe fn _init_l_System_SearchPath_toString___closed__0() -> *mut LeanObject {
    let mut v___x_1707_: u32 = 0;
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    v___x_1707_ = l_System_SearchPath_separator;
    v___x_1708_ = l_System_instInhabitedFilePath_default___closed__0;
    v___x_1709_ = lean_string_push(v___x_1708_, v___x_1707_);
    return v___x_1709_;
}
pub unsafe fn l_System_SearchPath_toString(mut v_path_1710_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    v___x_1711_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_System_SearchPath_toString___closed__0),
        core::ptr::addr_of_mut!(l_System_SearchPath_toString___closed__0_once),
        _init_l_System_SearchPath_toString___closed__0,
    );
    v___x_1712_ = lean_box(0);
    v___x_1713_ =
        l_List_mapTR_loop___at___00System_SearchPath_toString_spec__0(v_path_1710_, v___x_1712_);
    v___x_1714_ = l_String_intercalate(v___x_1711_, v___x_1713_);
    return v___x_1714_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_System_FilePath(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Modify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_System_Platform(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Length(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Take(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Access(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_System_FilePath_pathSeparator = _init_l_System_FilePath_pathSeparator();
    l_System_FilePath_pathSeparators___closed__0___boxed__const__1 =
        _init_l_System_FilePath_pathSeparators___closed__0___boxed__const__1();
    lean_mark_persistent(l_System_FilePath_pathSeparators___closed__0___boxed__const__1);
    l_System_FilePath_pathSeparators___closed__1___boxed__const__1 =
        _init_l_System_FilePath_pathSeparators___closed__1___boxed__const__1();
    lean_mark_persistent(l_System_FilePath_pathSeparators___closed__1___boxed__const__1);
    l_System_FilePath_pathSeparators = _init_l_System_FilePath_pathSeparators();
    lean_mark_persistent(l_System_FilePath_pathSeparators);
    l_System_FilePath_extSeparator = _init_l_System_FilePath_extSeparator();
    l_System_FilePath_exeExtension = _init_l_System_FilePath_exeExtension();
    lean_mark_persistent(l_System_FilePath_exeExtension);
    l_System_FilePath_isAbsolute___closed__0___boxed__const__1 =
        _init_l_System_FilePath_isAbsolute___closed__0___boxed__const__1();
    lean_mark_persistent(l_System_FilePath_isAbsolute___closed__0___boxed__const__1);
    l_System_SearchPath_separator = _init_l_System_SearchPath_separator();
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_System_FilePath(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_System_FilePath(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Modify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_System_Platform(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Length(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_Take(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Access(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_System_FilePath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_System_FilePath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_System_FilePath(builtin);
}
