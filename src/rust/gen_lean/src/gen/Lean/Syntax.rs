// Lean compiler output
// Module: Lean.Syntax
// Imports: Init.Data.Slice Init.Data.Hashable Lean.Data.Format Init.Data.Option.Coe Init.Data.String.Hashable Init.Data.Range.Polymorphic.Iterators Init.Data.ToString.Macro Init.Omega Init.Syntax
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Format::Syntax::l_Lean_Syntax_formatStx;
use crate::r#gen::Init::Data::Hashable::{
    initialize_Init_Data_Hashable, runtime_initialize_Init_Data_Hashable,
};
use crate::r#gen::Init::Data::List::Basic::{
    l_List_drop___redArg, l_List_isEmpty___redArg, l_List_reverse___redArg,
    l_List_zipWith___at___00List_zip_spec__0,
};
use crate::r#gen::Init::Data::List::Impl::{
    l___private_Init_Data_List_Impl_0__List_takeTR_go,
    l___private_Init_Data_List_Impl_0__List_zipWithTR_go,
};
use crate::r#gen::Init::Data::Option::Coe::{
    initialize_Init_Data_Option_Coe, runtime_initialize_Init_Data_Option_Coe,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::Slice::{
    initialize_Init_Data_Slice, runtime_initialize_Init_Data_Slice,
};
use crate::r#gen::Init::Data::String::Hashable::{
    initialize_Init_Data_String_Hashable, l_String_instHashableRaw_hash,
    runtime_initialize_Init_Data_String_Hashable,
};
use crate::r#gen::Init::Data::String::Substring::l_Substring_Raw_beq;
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_getTrailingTailPos_x3f, l_Lean_Syntax_instBEqPreresolved_beq,
    l_Lean_Syntax_isAtom, l_Lean_Syntax_splitNameLit,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_SourceInfo_getPos_x3f, l_Lean_SourceInfo_getTailPos_x3f,
    l_Lean_SourceInfo_getTrailingTailPos_x3f, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_getId, l_Lean_Syntax_getNumArgs, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isIdent, l_Lean_Syntax_isMissing,
    l_Lean_Syntax_isOfKind, l_Lean_mkAtom, l_List_lengthTR___redArg, lean_erase_macro_scopes,
};
use crate::r#gen::Init::Syntax::{
    initialize_Init_Syntax, l_Lean_Syntax_setArg, runtime_initialize_Init_Syntax,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::Format::{
    initialize_Lean_Data_Format, runtime_initialize_Lean_Data_Format,
};
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_components, l_Lean_Name_getNumParts};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::ffi::{
    lean_array_pop, lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::ffi::lean_array_fset;
use crate::ffi::lean_nat_to_int;
use crate::ffi::{
    lean_string_is_valid_pos, lean_string_utf8_extract, lean_string_utf8_get_fast,
    lean_string_utf8_next_fast,
};
use crate::ffi::{
    lean_string_length, lean_substring_tostring,
};
use crate::ffi::lean_string_append;
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_string_dec_eq, lean_string_utf8_byte_size, lean_uint32_dec_eq,
    lean_uint64_mix_hash, lean_usize_dec_eq,
};
use crate::ffi::lean_dbg_trace;
pub static l_Lean_Syntax_instInhabitedRange_default___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
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
static mut l_Lean_Syntax_instInhabitedRange_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instInhabitedRange_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Syntax_instInhabitedRange_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instInhabitedRange_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Syntax_instInhabitedRange: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instInhabitedRange_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instReprRange_repr___redArg___closed__0_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [123, 32, 0],
};
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instReprRange_repr___redArg___closed__1_value:
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
    m_data: [115, 116, 97, 114, 116, 0],
};
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instReprRange_repr___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instReprRange_repr___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instReprRange_repr___redArg___closed__4_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instReprRange_repr___redArg___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instReprRange_repr___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Syntax_instReprRange_repr___redArg___closed__8_value:
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
    m_data: [123, 32, 98, 121, 116, 101, 73, 100, 120, 32, 58, 61, 32, 0],
};
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instReprRange_repr___redArg___closed__9_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instReprRange_repr___redArg___closed__10_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [32, 125, 0],
};
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instReprRange_repr___redArg___closed__11_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instReprRange_repr___redArg___closed__12_value:
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
    m_data: [44, 0],
};
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instReprRange_repr___redArg___closed__13_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instReprRange_repr___redArg___closed__14_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [115, 116, 111, 112, 0],
};
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instReprRange_repr___redArg___closed__15_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__14_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Syntax_instReprRange_repr___redArg___closed__19_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Syntax_instReprRange_repr___redArg___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instReprRange_repr___redArg___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instReprRange___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Syntax_instReprRange_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Syntax_instReprRange___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instReprRange___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Syntax_instReprRange: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instReprRange___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instBEqRange___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Syntax_instBEqRange_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Syntax_instBEqRange___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instBEqRange___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Syntax_instBEqRange: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instBEqRange___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instHashableRange___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Syntax_instHashableRange_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Syntax_instHashableRange___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instHashableRange___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Syntax_instHashableRange: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_instHashableRange___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instBEqSourceInfo__lean___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqSourceInfo__lean_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqSourceInfo__lean___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqSourceInfo__lean___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instBEqSourceInfo__lean: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqSourceInfo__lean___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_isLitKind___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [99, 104, 97, 114, 0],
    };
static mut l_Lean_isLitKind___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isLitKind___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_isLitKind___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_isLitKind___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16760301032635233067 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_isLitKind___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isLitKind___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_isLitKind___closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [110, 97, 109, 101, 0],
    };
static mut l_Lean_isLitKind___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isLitKind___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_isLitKind___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_isLitKind___closed__2_value)
                as *mut crate::leanh::LeanObject,
            5949480926448383572 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_isLitKind___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isLitKind___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_isLitKind___closed__4_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [115, 99, 105, 101, 110, 116, 105, 102, 105, 99, 0],
    };
static mut l_Lean_isLitKind___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isLitKind___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_isLitKind___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_isLitKind___closed__4_value)
                as *mut crate::leanh::LeanObject,
            12926801259741997275 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_isLitKind___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isLitKind___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_isLitKind___closed__6_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [115, 116, 114, 0],
    };
static mut l_Lean_isLitKind___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isLitKind___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_isLitKind___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_isLitKind___closed__6_value)
                as *mut crate::leanh::LeanObject,
            9232979286016572671 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_isLitKind___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isLitKind___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_isLitKind___closed__8_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [110, 117, 109, 0],
    };
static mut l_Lean_isLitKind___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isLitKind___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_isLitKind___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_isLitKind___closed__8_value)
                as *mut crate::leanh::LeanObject,
            6110315075117401315 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_isLitKind___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_isLitKind___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
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
        114, 101, 117, 115, 101, 32, 115, 116, 111, 112, 112, 101, 100, 58, 10, 0,
    ],
};
static mut l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 33, 61, 10, 0],
};
static mut l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_structRangeEqWithTraceReuse___closed__2_value:
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
    m_data: [116, 114, 97, 99, 101, 0],
};
static mut l_Lean_Syntax_structRangeEqWithTraceReuse___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_structRangeEqWithTraceReuse___closed__3_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [69, 108, 97, 98, 0],
};
static mut l_Lean_Syntax_structRangeEqWithTraceReuse___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_structRangeEqWithTraceReuse___closed__4_value:
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
    m_data: [114, 101, 117, 115, 101, 0],
};
static mut l_Lean_Syntax_structRangeEqWithTraceReuse___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__2_value)
            as *mut crate::leanh::LeanObject,
        14231257465488249300 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__3_value)
            as *mut crate::leanh::LeanObject,
        129656885399133742 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__4_value)
            as *mut crate::leanh::LeanObject,
        8944050731725230368 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_getAtomVal___closed__0_value: crate::leanh::LeanStringObject<1> =
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
static mut l_Lean_Syntax_getAtomVal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_getAtomVal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_asNode___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Syntax_asNode___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_asNode___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_asNode___closed__1_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lean_Syntax_asNode___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_asNode___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_asNode___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Syntax_asNode___closed__1_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_asNode___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_asNode___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_asNode___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 1,
        },
        m_objs: [
            (((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Syntax_asNode___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Syntax_asNode___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_asNode___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_asNode___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_rewriteBottomUp___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Syntax_rewriteBottomUp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_rewriteBottomUp___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_rewriteBottomUp___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Syntax_rewriteBottomUp___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_rewriteBottomUp___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_rewriteBottomUp___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Syntax_rewriteBottomUp___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_rewriteBottomUp___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_rewriteBottomUp___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Syntax_rewriteBottomUp___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_rewriteBottomUp___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_rewriteBottomUp___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Syntax_rewriteBottomUp___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_rewriteBottomUp___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_rewriteBottomUp___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Syntax_rewriteBottomUp___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_rewriteBottomUp___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_rewriteBottomUp___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Syntax_rewriteBottomUp___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_rewriteBottomUp___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_rewriteBottomUp___closed__7_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Syntax_rewriteBottomUp___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Syntax_rewriteBottomUp___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_rewriteBottomUp___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_rewriteBottomUp___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_rewriteBottomUp___closed__8_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Syntax_rewriteBottomUp___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Syntax_rewriteBottomUp___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Syntax_rewriteBottomUp___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Syntax_rewriteBottomUp___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Syntax_rewriteBottomUp___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_rewriteBottomUp___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_rewriteBottomUp___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_rewriteBottomUp___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Syntax_rewriteBottomUp___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Syntax_rewriteBottomUp___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_rewriteBottomUp___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_rewriteBottomUp___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Syntax_identComponents___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Syntax_identComponents___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_identComponents___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_identComponents___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Syntax_getAtomVal___closed__0_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_identComponents___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_identComponents___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_identComponents___closed__2_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [76, 101, 97, 110, 46, 83, 121, 110, 116, 97, 120, 0],
    };
static mut l_Lean_Syntax_identComponents___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_identComponents___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_identComponents___closed__3_value: crate::leanh::LeanStringObject<28> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            76, 101, 97, 110, 46, 83, 121, 110, 116, 97, 120, 46, 105, 100, 101, 110, 116, 67, 111,
            109, 112, 111, 110, 101, 110, 116, 115, 0,
        ],
    };
static mut l_Lean_Syntax_identComponents___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_identComponents___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_identComponents___closed__4_value: crate::leanh::LeanStringObject<34> =
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
            117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97,
            115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
        ],
    };
static mut l_Lean_Syntax_identComponents___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_identComponents___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Syntax_identComponents___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Syntax_identComponents___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [99, 104, 111, 105, 99, 101, 0],
};
static mut l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11985596712582660667 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___closed__0_value:
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
    m_data: [32, 0],
};
static mut l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_Traverser_fromSyntax___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Syntax_Traverser_fromSyntax___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_Traverser_fromSyntax___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_MonadTraverser_getCur___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Syntax_MonadTraverser_getCur___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_MonadTraverser_getCur___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_MonadTraverser_goUp___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Syntax_MonadTraverser_goUp___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Syntax_MonadTraverser_goUp___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_MonadTraverser_goUp___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_MonadTraverser_goLeft___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Syntax_MonadTraverser_goLeft___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Syntax_MonadTraverser_goLeft___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_MonadTraverser_goLeft___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_MonadTraverser_goRight___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Syntax_MonadTraverser_goRight___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Syntax_MonadTraverser_goRight___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_MonadTraverser_goRight___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_isQuot___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [113, 117, 111, 116, 0],
    };
static mut l_Lean_Syntax_isQuot___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_isQuot___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_isQuot___closed__1_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [100, 121, 110, 97, 109, 105, 99, 81, 117, 111, 116, 0],
    };
static mut l_Lean_Syntax_isQuot___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_isQuot___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_isQuot___closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Syntax_isQuot___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_isQuot___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_isQuot___closed__3_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Syntax_isQuot___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_isQuot___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_isQuot___closed__4_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_Lean_Syntax_isQuot___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_isQuot___closed__4_value) as *mut crate::leanh::LeanObject;
static l_Lean_Syntax_getQuotContent___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Syntax_isQuot___closed__2_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Syntax_getQuotContent___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Syntax_getQuotContent___closed__0_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Syntax_isQuot___closed__3_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Syntax_getQuotContent___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Syntax_getQuotContent___closed__0_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Syntax_isQuot___closed__4_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Syntax_getQuotContent___closed__0_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Syntax_getQuotContent___closed__0_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Syntax_isQuot___closed__1_value)
                as *mut crate::leanh::LeanObject,
            17470799606987848564 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_getQuotContent___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_getQuotContent___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_isAntiquot___closed__0_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [97, 110, 116, 105, 113, 117, 111, 116, 0],
    };
static mut l_Lean_Syntax_isAntiquot___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_isAntiquot___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_mkAntiquotNode___closed__0_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [36, 0],
    };
static mut l_Lean_Syntax_mkAntiquotNode___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotNode___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Syntax_mkAntiquotNode___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Syntax_mkAntiquotNode___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Syntax_mkAntiquotNode___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Syntax_isAntiquot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7653097574325063121 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_mkAntiquotNode___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotNode___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Syntax_mkAntiquotNode___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Syntax_mkAntiquotNode___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Syntax_mkAntiquotNode___closed__4_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [112, 115, 101, 117, 100, 111, 0],
    };
static mut l_Lean_Syntax_mkAntiquotNode___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotNode___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_mkAntiquotNode___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotNode___closed__4_value)
                as *mut crate::leanh::LeanObject,
            17091268464027434998 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_mkAntiquotNode___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotNode___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_mkAntiquotNode___closed__6_value: crate::leanh::LeanStringObject<13> =
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
        m_data: [97, 110, 116, 105, 113, 117, 111, 116, 78, 97, 109, 101, 0],
    };
static mut l_Lean_Syntax_mkAntiquotNode___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotNode___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_mkAntiquotNode___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotNode___closed__6_value)
                as *mut crate::leanh::LeanObject,
            5763156871072657475 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_mkAntiquotNode___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotNode___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_mkAntiquotNode___closed__8_value: crate::leanh::LeanStringObject<2> =
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
static mut l_Lean_Syntax_mkAntiquotNode___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotNode___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Syntax_mkAntiquotNode___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Syntax_mkAntiquotNode___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Syntax_mkAntiquotNode___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Syntax_mkAntiquotNode___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Syntax_mkAntiquotNode___closed__11_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [104, 111, 108, 101, 0],
    };
static mut l_Lean_Syntax_mkAntiquotNode___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotNode___closed__11_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Syntax_mkAntiquotNode___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Syntax_isQuot___closed__2_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Syntax_mkAntiquotNode___closed__12_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotNode___closed__12_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Syntax_isQuot___closed__3_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Syntax_mkAntiquotNode___closed__12_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotNode___closed__12_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Syntax_isQuot___closed__4_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Syntax_mkAntiquotNode___closed__12_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotNode___closed__12_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotNode___closed__11_value)
                as *mut crate::leanh::LeanObject,
            3984140175429830279 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_mkAntiquotNode___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotNode___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_mkAntiquotNode___closed__13_value: crate::leanh::LeanStringObject<19> =
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
            97, 110, 116, 105, 113, 117, 111, 116, 78, 101, 115, 116, 101, 100, 69, 120, 112, 114,
            0,
        ],
    };
static mut l_Lean_Syntax_mkAntiquotNode___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotNode___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_mkAntiquotNode___closed__14_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotNode___closed__13_value)
                as *mut crate::leanh::LeanObject,
            9054665995413608708 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_mkAntiquotNode___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotNode___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_mkAntiquotNode___closed__15_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [40, 0],
    };
static mut l_Lean_Syntax_mkAntiquotNode___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotNode___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Syntax_mkAntiquotNode___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Syntax_mkAntiquotNode___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Syntax_mkAntiquotNode___closed__17_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [41, 0],
    };
static mut l_Lean_Syntax_mkAntiquotNode___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotNode___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Syntax_mkAntiquotNode___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Syntax_mkAntiquotNode___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Syntax_mkAntiquotNode___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Syntax_mkAntiquotNode___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_antiquotSpliceKind_x3f___closed__0_value: crate::leanh::LeanStringObject<
    15,
> = crate::leanh::LeanStringObject {
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
        97, 110, 116, 105, 113, 117, 111, 116, 95, 115, 99, 111, 112, 101, 0,
    ],
};
static mut l_Lean_Syntax_antiquotSpliceKind_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_antiquotSpliceKind_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_mkAntiquotSpliceNode___closed__0_value: crate::leanh::LeanStringObject<
    16,
> = crate::leanh::LeanStringObject {
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
        97, 110, 116, 105, 113, 117, 111, 116, 95, 115, 112, 108, 105, 99, 101, 0,
    ],
};
static mut l_Lean_Syntax_mkAntiquotSpliceNode___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotSpliceNode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_mkAntiquotSpliceNode___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotSpliceNode___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13960734728685499916 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_mkAntiquotSpliceNode___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotSpliceNode___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_mkAntiquotSpliceNode___closed__2_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [91, 0],
    };
static mut l_Lean_Syntax_mkAntiquotSpliceNode___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotSpliceNode___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Syntax_mkAntiquotSpliceNode___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Syntax_mkAntiquotSpliceNode___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Syntax_mkAntiquotSpliceNode___closed__4_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [93, 0],
    };
static mut l_Lean_Syntax_mkAntiquotSpliceNode___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotSpliceNode___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Syntax_mkAntiquotSpliceNode___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Syntax_mkAntiquotSpliceNode___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Syntax_mkAntiquotSpliceNode___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Syntax_mkAntiquotSpliceNode___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
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
        97, 110, 116, 105, 113, 117, 111, 116, 95, 115, 117, 102, 102, 105, 120, 95, 115, 112, 108,
        105, 99, 101, 0,
    ],
};
static mut l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__0_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15643112305600108244 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_isTokenAntiquot___closed__0_value: crate::leanh::LeanStringObject<15> =
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
            116, 111, 107, 101, 110, 95, 97, 110, 116, 105, 113, 117, 111, 116, 0,
        ],
    };
static mut l_Lean_Syntax_isTokenAntiquot___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_isTokenAntiquot___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_isTokenAntiquot___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Syntax_isTokenAntiquot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9743428852723982113 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Syntax_isTokenAntiquot___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_isTokenAntiquot___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
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
static mut l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Syntax_Stack_matches___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Syntax_Stack_matches___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Syntax_Stack_matches___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Nat_cast___at___00Lean_Syntax_instReprRange_repr_spec__0(
    mut v_a_2737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2738_ = lean_nat_to_int(v_a_2737_);
    return v___x_2738_;
}
pub unsafe fn _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2752_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_2753_ = lean_nat_to_int(v___x_2752_);
    return v___x_2753_;
}
pub unsafe fn _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2766_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_2767_ = lean_nat_to_int(v___x_2766_);
    return v___x_2767_;
}
pub unsafe fn _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2768_ = l_Lean_Syntax_instReprRange_repr___redArg___closed__0;
    v___x_2769_ = lean_string_length(v___x_2768_);
    return v___x_2769_;
}
pub unsafe fn _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2770_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Syntax_instReprRange_repr___redArg___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Syntax_instReprRange_repr___redArg___closed__17_once),
        _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__17,
    );
    v___x_2771_ = lean_nat_to_int(v___x_2770_);
    return v___x_2771_;
}
pub unsafe fn l_Lean_Syntax_instReprRange_repr___redArg(
    mut v_x_2774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2779_: u8 = 0;
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: u8 = 0;
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2816_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_2775_ = crate::leanh::lean_ctor_get(v_x_2774_, 0);
                v_stop_2776_ = crate::leanh::lean_ctor_get(v_x_2774_, 1);
                v_isSharedCheck_2816_ = (!crate::leanh::lean_is_exclusive(v_x_2774_)) as u8;
                if v_isSharedCheck_2816_ == 0 {
                    v___x_2778_ = v_x_2774_;
                    v_isShared_2779_ = v_isSharedCheck_2816_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_2776_);
                    crate::leanh::lean_inc(v_start_2775_);
                    crate::leanh::lean_dec(v_x_2774_);
                    v___x_2778_ = crate::leanh::lean_box(0);
                    v_isShared_2779_ = v_isSharedCheck_2816_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2780_ = l_Lean_Syntax_instReprRange_repr___redArg___closed__5;
                v___x_2781_ = l_Lean_Syntax_instReprRange_repr___redArg___closed__6;
                v___x_2782_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Syntax_instReprRange_repr___redArg___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Lean_Syntax_instReprRange_repr___redArg___closed__7_once
                    ),
                    _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__7,
                );
                v___x_2783_ = l_Lean_Syntax_instReprRange_repr___redArg___closed__9;
                v___x_2784_ = l_Nat_reprFast(v_start_2775_);
                v___x_2785_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2785_, 0, v___x_2784_);
                if v_isShared_2779_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2778_, 5);
                    crate::leanh::lean_ctor_set(v___x_2778_, 1, v___x_2785_);
                    crate::leanh::lean_ctor_set(v___x_2778_, 0, v___x_2783_);
                    v___x_2787_ = v___x_2778_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2815_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 1, v___x_2785_);
                    v___x_2787_ = v_reuseFailAlloc_2815_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2788_ = l_Lean_Syntax_instReprRange_repr___redArg___closed__11;
                v___x_2789_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2789_, 0, v___x_2787_);
                crate::leanh::lean_ctor_set(v___x_2789_, 1, v___x_2788_);
                v___x_2790_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2790_, 0, v___x_2782_);
                crate::leanh::lean_ctor_set(v___x_2790_, 1, v___x_2789_);
                v___x_2791_ = 0;
                v___x_2792_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2792_, 0, v___x_2790_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2792_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2791_,
                );
                v___x_2793_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2793_, 0, v___x_2781_);
                crate::leanh::lean_ctor_set(v___x_2793_, 1, v___x_2792_);
                v___x_2794_ = l_Lean_Syntax_instReprRange_repr___redArg___closed__13;
                v___x_2795_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2795_, 0, v___x_2793_);
                crate::leanh::lean_ctor_set(v___x_2795_, 1, v___x_2794_);
                v___x_2796_ = crate::leanh::lean_box(1);
                v___x_2797_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2797_, 0, v___x_2795_);
                crate::leanh::lean_ctor_set(v___x_2797_, 1, v___x_2796_);
                v___x_2798_ = l_Lean_Syntax_instReprRange_repr___redArg___closed__15;
                v___x_2799_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2799_, 0, v___x_2797_);
                crate::leanh::lean_ctor_set(v___x_2799_, 1, v___x_2798_);
                v___x_2800_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2800_, 0, v___x_2799_);
                crate::leanh::lean_ctor_set(v___x_2800_, 1, v___x_2780_);
                v___x_2801_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Syntax_instReprRange_repr___redArg___closed__16),
                    core::ptr::addr_of_mut!(
                        l_Lean_Syntax_instReprRange_repr___redArg___closed__16_once
                    ),
                    _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__16,
                );
                v___x_2802_ = l_Nat_reprFast(v_stop_2776_);
                v___x_2803_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2803_, 0, v___x_2802_);
                v___x_2804_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2804_, 0, v___x_2783_);
                crate::leanh::lean_ctor_set(v___x_2804_, 1, v___x_2803_);
                v___x_2805_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2805_, 0, v___x_2804_);
                crate::leanh::lean_ctor_set(v___x_2805_, 1, v___x_2788_);
                v___x_2806_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2806_, 0, v___x_2801_);
                crate::leanh::lean_ctor_set(v___x_2806_, 1, v___x_2805_);
                v___x_2807_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2807_, 0, v___x_2806_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2807_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2791_,
                );
                v___x_2808_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2808_, 0, v___x_2800_);
                crate::leanh::lean_ctor_set(v___x_2808_, 1, v___x_2807_);
                v___x_2809_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Syntax_instReprRange_repr___redArg___closed__18),
                    core::ptr::addr_of_mut!(
                        l_Lean_Syntax_instReprRange_repr___redArg___closed__18_once
                    ),
                    _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__18,
                );
                v___x_2810_ = l_Lean_Syntax_instReprRange_repr___redArg___closed__19;
                v___x_2811_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2811_, 0, v___x_2810_);
                crate::leanh::lean_ctor_set(v___x_2811_, 1, v___x_2808_);
                v___x_2812_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2812_, 0, v___x_2811_);
                crate::leanh::lean_ctor_set(v___x_2812_, 1, v___x_2788_);
                v___x_2813_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2813_, 0, v___x_2809_);
                crate::leanh::lean_ctor_set(v___x_2813_, 1, v___x_2812_);
                v___x_2814_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2814_, 0, v___x_2813_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2814_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2791_,
                );
                return v___x_2814_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_instReprRange_repr(
    mut v_x_2817_: *mut crate::leanh::LeanObject,
    mut v_prec_2818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2819_ = l_Lean_Syntax_instReprRange_repr___redArg(v_x_2817_);
    return v___x_2819_;
}
pub unsafe fn l_Lean_Syntax_instReprRange_repr___boxed(
    mut v_x_2820_: *mut crate::leanh::LeanObject,
    mut v_prec_2821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2822_ = l_Lean_Syntax_instReprRange_repr(v_x_2820_, v_prec_2821_);
    crate::leanh::lean_dec(v_prec_2821_);
    return v_res_2822_;
}
pub unsafe fn l_Lean_Syntax_instBEqRange_beq(
    mut v_x_2825_: *mut crate::leanh::LeanObject,
    mut v_x_2826_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_start_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: u8 = 0;
    v_start_2827_ = crate::leanh::lean_ctor_get(v_x_2825_, 0);
    v_stop_2828_ = crate::leanh::lean_ctor_get(v_x_2825_, 1);
    v_start_2829_ = crate::leanh::lean_ctor_get(v_x_2826_, 0);
    v_stop_2830_ = crate::leanh::lean_ctor_get(v_x_2826_, 1);
    v___x_2831_ = lean_nat_dec_eq(v_start_2827_, v_start_2829_);
    if v___x_2831_ == 0 {
        return v___x_2831_;
    } else {
        let mut v___x_2832_: u8 = 0;
        v___x_2832_ = lean_nat_dec_eq(v_stop_2828_, v_stop_2830_);
        return v___x_2832_;
    }
}
pub unsafe fn l_Lean_Syntax_instBEqRange_beq___boxed(
    mut v_x_2833_: *mut crate::leanh::LeanObject,
    mut v_x_2834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2835_: u8 = 0;
    let mut v_r_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2835_ = l_Lean_Syntax_instBEqRange_beq(v_x_2833_, v_x_2834_);
    crate::leanh::lean_dec_ref(v_x_2834_);
    crate::leanh::lean_dec_ref(v_x_2833_);
    v_r_2836_ = crate::leanh::lean_box((v_res_2835_) as usize);
    return v_r_2836_;
}
pub unsafe fn l_Lean_Syntax_instHashableRange_hash(
    mut v_x_2839_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v_start_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: u64 = 0;
    let mut v___x_2843_: u64 = 0;
    let mut v___x_2844_: u64 = 0;
    let mut v___x_2845_: u64 = 0;
    let mut v___x_2846_: u64 = 0;
    v_start_2840_ = crate::leanh::lean_ctor_get(v_x_2839_, 0);
    v_stop_2841_ = crate::leanh::lean_ctor_get(v_x_2839_, 1);
    v___x_2842_ = 0u64;
    v___x_2843_ = l_String_instHashableRaw_hash(v_start_2840_);
    v___x_2844_ = lean_uint64_mix_hash(v___x_2842_, v___x_2843_);
    v___x_2845_ = l_String_instHashableRaw_hash(v_stop_2841_);
    v___x_2846_ = lean_uint64_mix_hash(v___x_2844_, v___x_2845_);
    return v___x_2846_;
}
pub unsafe fn l_Lean_Syntax_instHashableRange_hash___boxed(
    mut v_x_2847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2848_: u64 = 0;
    let mut v_r_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2848_ = l_Lean_Syntax_instHashableRange_hash(v_x_2847_);
    crate::leanh::lean_dec_ref(v_x_2847_);
    v_r_2849_ = crate::leanh::lean_box_uint64(v_res_2848_);
    return v_r_2849_;
}
pub unsafe fn l_Lean_Syntax_Range_contains(
    mut v_r_2852_: *mut crate::leanh::LeanObject,
    mut v_pos_2853_: *mut crate::leanh::LeanObject,
    mut v_includeStop_2854_: u8,
) -> u8 {
    let mut v_start_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: u8 = 0;
    v_start_2855_ = crate::leanh::lean_ctor_get(v_r_2852_, 0);
    v_stop_2856_ = crate::leanh::lean_ctor_get(v_r_2852_, 1);
    v___x_2857_ = lean_nat_dec_le(v_start_2855_, v_pos_2853_);
    if v___x_2857_ == 0 {
        return v___x_2857_;
    } else {
        if v_includeStop_2854_ == 0 {
            let mut v___x_2858_: u8 = 0;
            v___x_2858_ = lean_nat_dec_lt(v_pos_2853_, v_stop_2856_);
            return v___x_2858_;
        } else {
            let mut v___x_2859_: u8 = 0;
            v___x_2859_ = lean_nat_dec_le(v_pos_2853_, v_stop_2856_);
            return v___x_2859_;
        }
    }
}
pub unsafe fn l_Lean_Syntax_Range_contains___boxed(
    mut v_r_2860_: *mut crate::leanh::LeanObject,
    mut v_pos_2861_: *mut crate::leanh::LeanObject,
    mut v_includeStop_2862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_includeStop_boxed_2863_: u8 = 0;
    let mut v_res_2864_: u8 = 0;
    let mut v_r_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_includeStop_boxed_2863_ = (crate::leanh::lean_unbox(v_includeStop_2862_) as u8);
    v_res_2864_ = l_Lean_Syntax_Range_contains(v_r_2860_, v_pos_2861_, v_includeStop_boxed_2863_);
    crate::leanh::lean_dec(v_pos_2861_);
    crate::leanh::lean_dec_ref(v_r_2860_);
    v_r_2865_ = crate::leanh::lean_box((v_res_2864_) as usize);
    return v_r_2865_;
}
pub unsafe fn l_Lean_Syntax_Range_includes(
    mut v_super_2866_: *mut crate::leanh::LeanObject,
    mut v_sub_2867_: *mut crate::leanh::LeanObject,
    mut v_includeSuperStop_2868_: u8,
    mut v_includeSubStop_2869_: u8,
) -> u8 {
    let mut v_start_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2875_: u8 = 0;
    let mut v___x_2876_: u8 = 0;
    let mut v___x_2877_: u8 = 0;
    let mut v___x_2878_: u8 = 0;
    let mut v___x_2879_: u8 = 0;
    let mut v___y_2881_: u8 = 0;
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: u8 = 0;
    let mut v___x_2885_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_2870_ = crate::leanh::lean_ctor_get(v_super_2866_, 0);
                v_stop_2871_ = crate::leanh::lean_ctor_get(v_super_2866_, 1);
                v_start_2872_ = crate::leanh::lean_ctor_get(v_sub_2867_, 0);
                v_stop_2873_ = crate::leanh::lean_ctor_get(v_sub_2867_, 1);
                v___x_2879_ = lean_nat_dec_le(v_start_2870_, v_start_2872_);
                if v___x_2879_ == 0 {
                    return v___x_2879_;
                } else {
                    if v_includeSuperStop_2868_ == 0 {
                        v___y_2881_ = v_includeSuperStop_2868_;
                        state = 2;
                        continue;
                    } else {
                        if v_includeSubStop_2869_ == 0 {
                            v___x_2882_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_2883_ = lean_nat_add(v_stop_2871_, v___x_2882_);
                            v___x_2884_ = lean_nat_dec_le(v_stop_2873_, v___x_2883_);
                            crate::leanh::lean_dec(v___x_2883_);
                            return v___x_2884_;
                        } else {
                            v___x_2885_ = 0;
                            v___y_2881_ = v___x_2885_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_2875_ == 0 {
                    v___x_2876_ = lean_nat_dec_le(v_stop_2873_, v_stop_2871_);
                    return v___x_2876_;
                } else {
                    if v_includeSubStop_2869_ == 0 {
                        v___x_2877_ = lean_nat_dec_le(v_stop_2873_, v_stop_2871_);
                        return v___x_2877_;
                    } else {
                        v___x_2878_ = lean_nat_dec_lt(v_stop_2873_, v_stop_2871_);
                        return v___x_2878_;
                    }
                }
            }
            2 => {
                if v_includeSuperStop_2868_ == 0 {
                    v___y_2875_ = v___x_2879_;
                    state = 1;
                    continue;
                } else {
                    v___y_2875_ = v___y_2881_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_Range_includes___boxed(
    mut v_super_2886_: *mut crate::leanh::LeanObject,
    mut v_sub_2887_: *mut crate::leanh::LeanObject,
    mut v_includeSuperStop_2888_: *mut crate::leanh::LeanObject,
    mut v_includeSubStop_2889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_includeSuperStop_boxed_2890_: u8 = 0;
    let mut v_includeSubStop_boxed_2891_: u8 = 0;
    let mut v_res_2892_: u8 = 0;
    let mut v_r_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_includeSuperStop_boxed_2890_ = (crate::leanh::lean_unbox(v_includeSuperStop_2888_) as u8);
    v_includeSubStop_boxed_2891_ = (crate::leanh::lean_unbox(v_includeSubStop_2889_) as u8);
    v_res_2892_ = l_Lean_Syntax_Range_includes(
        v_super_2886_,
        v_sub_2887_,
        v_includeSuperStop_boxed_2890_,
        v_includeSubStop_boxed_2891_,
    );
    crate::leanh::lean_dec_ref(v_sub_2887_);
    crate::leanh::lean_dec_ref(v_super_2886_);
    v_r_2893_ = crate::leanh::lean_box((v_res_2892_) as usize);
    return v_r_2893_;
}
pub unsafe fn l_String_Range_includes(
    mut v_super_2894_: *mut crate::leanh::LeanObject,
    mut v_sub_2895_: *mut crate::leanh::LeanObject,
    mut v_includeSuperStop_2896_: u8,
    mut v_includeSubStop_2897_: u8,
) -> u8 {
    let mut v___x_2898_: u8 = 0;
    v___x_2898_ = l_Lean_Syntax_Range_includes(
        v_super_2894_,
        v_sub_2895_,
        v_includeSuperStop_2896_,
        v_includeSubStop_2897_,
    );
    return v___x_2898_;
}
pub unsafe fn l_String_Range_includes___boxed(
    mut v_super_2899_: *mut crate::leanh::LeanObject,
    mut v_sub_2900_: *mut crate::leanh::LeanObject,
    mut v_includeSuperStop_2901_: *mut crate::leanh::LeanObject,
    mut v_includeSubStop_2902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_includeSuperStop_boxed_2903_: u8 = 0;
    let mut v_includeSubStop_boxed_2904_: u8 = 0;
    let mut v_res_2905_: u8 = 0;
    let mut v_r_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_includeSuperStop_boxed_2903_ = (crate::leanh::lean_unbox(v_includeSuperStop_2901_) as u8);
    v_includeSubStop_boxed_2904_ = (crate::leanh::lean_unbox(v_includeSubStop_2902_) as u8);
    v_res_2905_ = l_String_Range_includes(
        v_super_2899_,
        v_sub_2900_,
        v_includeSuperStop_boxed_2903_,
        v_includeSubStop_boxed_2904_,
    );
    crate::leanh::lean_dec_ref(v_sub_2900_);
    crate::leanh::lean_dec_ref(v_super_2899_);
    v_r_2906_ = crate::leanh::lean_box((v_res_2905_) as usize);
    return v_r_2906_;
}
pub unsafe fn l_Lean_Syntax_Range_overlaps(
    mut v_first_2907_: *mut crate::leanh::LeanObject,
    mut v_second_2908_: *mut crate::leanh::LeanObject,
    mut v_includeFirstStop_2909_: u8,
    mut v_includeSecondStop_2910_: u8,
) -> u8 {
    let mut v___y_2912_: u8 = 0;
    let mut v_start_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: u8 = 0;
    let mut v_start_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: u8 = 0;
    let mut v_start_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: u8 = 0;
    let mut v_start_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_includeFirstStop_2909_ == 0 {
                    v_start_2919_ = crate::leanh::lean_ctor_get(v_second_2908_, 0);
                    v_stop_2920_ = crate::leanh::lean_ctor_get(v_first_2907_, 1);
                    v___x_2921_ = lean_nat_dec_lt(v_start_2919_, v_stop_2920_);
                    v___y_2912_ = v___x_2921_;
                    state = 1;
                    continue;
                } else {
                    v_start_2922_ = crate::leanh::lean_ctor_get(v_second_2908_, 0);
                    v_stop_2923_ = crate::leanh::lean_ctor_get(v_first_2907_, 1);
                    v___x_2924_ = lean_nat_dec_le(v_start_2922_, v_stop_2923_);
                    v___y_2912_ = v___x_2924_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_2912_ == 0 {
                    return v___y_2912_;
                } else {
                    if v_includeSecondStop_2910_ == 0 {
                        v_start_2913_ = crate::leanh::lean_ctor_get(v_first_2907_, 0);
                        v_stop_2914_ = crate::leanh::lean_ctor_get(v_second_2908_, 1);
                        v___x_2915_ = lean_nat_dec_lt(v_start_2913_, v_stop_2914_);
                        return v___x_2915_;
                    } else {
                        v_start_2916_ = crate::leanh::lean_ctor_get(v_first_2907_, 0);
                        v_stop_2917_ = crate::leanh::lean_ctor_get(v_second_2908_, 1);
                        v___x_2918_ = lean_nat_dec_le(v_start_2916_, v_stop_2917_);
                        return v___x_2918_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_Range_overlaps___boxed(
    mut v_first_2925_: *mut crate::leanh::LeanObject,
    mut v_second_2926_: *mut crate::leanh::LeanObject,
    mut v_includeFirstStop_2927_: *mut crate::leanh::LeanObject,
    mut v_includeSecondStop_2928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_includeFirstStop_boxed_2929_: u8 = 0;
    let mut v_includeSecondStop_boxed_2930_: u8 = 0;
    let mut v_res_2931_: u8 = 0;
    let mut v_r_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_includeFirstStop_boxed_2929_ = (crate::leanh::lean_unbox(v_includeFirstStop_2927_) as u8);
    v_includeSecondStop_boxed_2930_ = (crate::leanh::lean_unbox(v_includeSecondStop_2928_) as u8);
    v_res_2931_ = l_Lean_Syntax_Range_overlaps(
        v_first_2925_,
        v_second_2926_,
        v_includeFirstStop_boxed_2929_,
        v_includeSecondStop_boxed_2930_,
    );
    crate::leanh::lean_dec_ref(v_second_2926_);
    crate::leanh::lean_dec_ref(v_first_2925_);
    v_r_2932_ = crate::leanh::lean_box((v_res_2931_) as usize);
    return v_r_2932_;
}
pub unsafe fn l_String_Range_overlaps(
    mut v_first_2933_: *mut crate::leanh::LeanObject,
    mut v_second_2934_: *mut crate::leanh::LeanObject,
    mut v_includeFirstStop_2935_: u8,
    mut v_includeSecondStop_2936_: u8,
) -> u8 {
    let mut v___x_2937_: u8 = 0;
    v___x_2937_ = l_Lean_Syntax_Range_overlaps(
        v_first_2933_,
        v_second_2934_,
        v_includeFirstStop_2935_,
        v_includeSecondStop_2936_,
    );
    return v___x_2937_;
}
pub unsafe fn l_String_Range_overlaps___boxed(
    mut v_first_2938_: *mut crate::leanh::LeanObject,
    mut v_second_2939_: *mut crate::leanh::LeanObject,
    mut v_includeFirstStop_2940_: *mut crate::leanh::LeanObject,
    mut v_includeSecondStop_2941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_includeFirstStop_boxed_2942_: u8 = 0;
    let mut v_includeSecondStop_boxed_2943_: u8 = 0;
    let mut v_res_2944_: u8 = 0;
    let mut v_r_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_includeFirstStop_boxed_2942_ = (crate::leanh::lean_unbox(v_includeFirstStop_2940_) as u8);
    v_includeSecondStop_boxed_2943_ = (crate::leanh::lean_unbox(v_includeSecondStop_2941_) as u8);
    v_res_2944_ = l_String_Range_overlaps(
        v_first_2938_,
        v_second_2939_,
        v_includeFirstStop_boxed_2942_,
        v_includeSecondStop_boxed_2943_,
    );
    crate::leanh::lean_dec_ref(v_second_2939_);
    crate::leanh::lean_dec_ref(v_first_2938_);
    v_r_2945_ = crate::leanh::lean_box((v_res_2944_) as usize);
    return v_r_2945_;
}
pub unsafe fn l_Lean_Syntax_Range_bsize(
    mut v_r_2946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_start_2947_ = crate::leanh::lean_ctor_get(v_r_2946_, 0);
    v_stop_2948_ = crate::leanh::lean_ctor_get(v_r_2946_, 1);
    v___x_2949_ = lean_nat_sub(v_stop_2948_, v_start_2947_);
    return v___x_2949_;
}
pub unsafe fn l_Lean_Syntax_Range_bsize___boxed(
    mut v_r_2950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2951_ = l_Lean_Syntax_Range_bsize(v_r_2950_);
    crate::leanh::lean_dec_ref(v_r_2950_);
    return v_res_2951_;
}
pub unsafe fn l_String_Range_bsize(
    mut v_r_2952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2953_ = l_Lean_Syntax_Range_bsize(v_r_2952_);
    return v___x_2953_;
}
pub unsafe fn l_String_Range_bsize___boxed(
    mut v_r_2954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2955_ = l_String_Range_bsize(v_r_2954_);
    crate::leanh::lean_dec_ref(v_r_2954_);
    return v_res_2955_;
}
pub unsafe fn l_Lean_SourceInfo_updateTrailing(
    mut v_trailing_2956_: *mut crate::leanh::LeanObject,
    mut v_x_2957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leading_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2963_: u8 = 0;
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2967_: u8 = 0;
    let mut v_unused_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2957_) == 0 {
                    v_leading_2958_ = crate::leanh::lean_ctor_get(v_x_2957_, 0);
                    v_pos_2959_ = crate::leanh::lean_ctor_get(v_x_2957_, 1);
                    v_endPos_2960_ = crate::leanh::lean_ctor_get(v_x_2957_, 3);
                    v_isSharedCheck_2967_ = (!crate::leanh::lean_is_exclusive(v_x_2957_)) as u8;
                    if v_isSharedCheck_2967_ == 0 {
                        v_unused_2968_ = crate::leanh::lean_ctor_get(v_x_2957_, 2);
                        crate::leanh::lean_dec(v_unused_2968_);
                        v___x_2962_ = v_x_2957_;
                        v_isShared_2963_ = v_isSharedCheck_2967_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_endPos_2960_);
                        crate::leanh::lean_inc(v_pos_2959_);
                        crate::leanh::lean_inc(v_leading_2958_);
                        crate::leanh::lean_dec(v_x_2957_);
                        v___x_2962_ = crate::leanh::lean_box(0);
                        v_isShared_2963_ = v_isSharedCheck_2967_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_trailing_2956_);
                    return v_x_2957_;
                }
            }
            1 => {
                if v_isShared_2963_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2962_, 2, v_trailing_2956_);
                    v___x_2965_ = v___x_2962_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2966_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_leading_2958_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 1, v_pos_2959_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 2, v_trailing_2956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 3, v_endPos_2960_);
                    v___x_2965_ = v_reuseFailAlloc_2966_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2965_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SourceInfo_getRange_x3f(
    mut v_canonicalOnly_2969_: u8,
    mut v_info_2970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2979_: u8 = 0;
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2984_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2971_ = l_Lean_SourceInfo_getPos_x3f(v_info_2970_, v_canonicalOnly_2969_);
                if crate::leanh::lean_obj_tag(v___x_2971_) == 0 {
                    v___x_2972_ = crate::leanh::lean_box(0);
                    return v___x_2972_;
                } else {
                    v_val_2973_ = crate::leanh::lean_ctor_get(v___x_2971_, 0);
                    crate::leanh::lean_inc(v_val_2973_);
                    crate::leanh::lean_dec_ref_known(v___x_2971_, 1);
                    v___x_2974_ =
                        l_Lean_SourceInfo_getTailPos_x3f(v_info_2970_, v_canonicalOnly_2969_);
                    if crate::leanh::lean_obj_tag(v___x_2974_) == 0 {
                        crate::leanh::lean_dec(v_val_2973_);
                        v___x_2975_ = crate::leanh::lean_box(0);
                        return v___x_2975_;
                    } else {
                        v_val_2976_ = crate::leanh::lean_ctor_get(v___x_2974_, 0);
                        v_isSharedCheck_2984_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2974_)) as u8;
                        if v_isSharedCheck_2984_ == 0 {
                            v___x_2978_ = v___x_2974_;
                            v_isShared_2979_ = v_isSharedCheck_2984_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2976_);
                            crate::leanh::lean_dec(v___x_2974_);
                            v___x_2978_ = crate::leanh::lean_box(0);
                            v_isShared_2979_ = v_isSharedCheck_2984_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2980_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2980_, 0, v_val_2973_);
                crate::leanh::lean_ctor_set(v___x_2980_, 1, v_val_2976_);
                if v_isShared_2979_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2978_, 0, v___x_2980_);
                    v___x_2982_ = v___x_2978_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2983_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2980_);
                    v___x_2982_ = v_reuseFailAlloc_2983_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2982_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SourceInfo_getRange_x3f___boxed(
    mut v_canonicalOnly_2985_: *mut crate::leanh::LeanObject,
    mut v_info_2986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonicalOnly_boxed_2987_: u8 = 0;
    let mut v_res_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2987_ = (crate::leanh::lean_unbox(v_canonicalOnly_2985_) as u8);
    v_res_2988_ = l_Lean_SourceInfo_getRange_x3f(v_canonicalOnly_boxed_2987_, v_info_2986_);
    crate::leanh::lean_dec(v_info_2986_);
    return v_res_2988_;
}
pub unsafe fn l_Lean_SourceInfo_getRangeWithTrailing_x3f(
    mut v_canonicalOnly_2989_: u8,
    mut v_info_2990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2999_: u8 = 0;
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3004_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2991_ = l_Lean_SourceInfo_getPos_x3f(v_info_2990_, v_canonicalOnly_2989_);
                if crate::leanh::lean_obj_tag(v___x_2991_) == 0 {
                    v___x_2992_ = crate::leanh::lean_box(0);
                    return v___x_2992_;
                } else {
                    v_val_2993_ = crate::leanh::lean_ctor_get(v___x_2991_, 0);
                    crate::leanh::lean_inc(v_val_2993_);
                    crate::leanh::lean_dec_ref_known(v___x_2991_, 1);
                    v___x_2994_ = l_Lean_SourceInfo_getTrailingTailPos_x3f(
                        v_info_2990_,
                        v_canonicalOnly_2989_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2994_) == 0 {
                        crate::leanh::lean_dec(v_val_2993_);
                        v___x_2995_ = crate::leanh::lean_box(0);
                        return v___x_2995_;
                    } else {
                        v_val_2996_ = crate::leanh::lean_ctor_get(v___x_2994_, 0);
                        v_isSharedCheck_3004_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2994_)) as u8;
                        if v_isSharedCheck_3004_ == 0 {
                            v___x_2998_ = v___x_2994_;
                            v_isShared_2999_ = v_isSharedCheck_3004_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2996_);
                            crate::leanh::lean_dec(v___x_2994_);
                            v___x_2998_ = crate::leanh::lean_box(0);
                            v_isShared_2999_ = v_isSharedCheck_3004_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3000_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3000_, 0, v_val_2993_);
                crate::leanh::lean_ctor_set(v___x_3000_, 1, v_val_2996_);
                if v_isShared_2999_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2998_, 0, v___x_3000_);
                    v___x_3002_ = v___x_2998_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3003_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_3000_);
                    v___x_3002_ = v_reuseFailAlloc_3003_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3002_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SourceInfo_getRangeWithTrailing_x3f___boxed(
    mut v_canonicalOnly_3005_: *mut crate::leanh::LeanObject,
    mut v_info_3006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonicalOnly_boxed_3007_: u8 = 0;
    let mut v_res_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_3007_ = (crate::leanh::lean_unbox(v_canonicalOnly_3005_) as u8);
    v_res_3008_ =
        l_Lean_SourceInfo_getRangeWithTrailing_x3f(v_canonicalOnly_boxed_3007_, v_info_3006_);
    crate::leanh::lean_dec(v_info_3006_);
    return v_res_3008_;
}
pub unsafe fn l_Lean_SourceInfo_nonCanonicalSynthetic(
    mut v_x_3009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: u8 = 0;
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3018_: u8 = 0;
    let mut v___x_3019_: u8 = 0;
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3023_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_3009_) {
                0 => {
                    v_pos_3010_ = crate::leanh::lean_ctor_get(v_x_3009_, 1);
                    crate::leanh::lean_inc(v_pos_3010_);
                    v_endPos_3011_ = crate::leanh::lean_ctor_get(v_x_3009_, 3);
                    crate::leanh::lean_inc(v_endPos_3011_);
                    crate::leanh::lean_dec_ref_known(v_x_3009_, 4);
                    v___x_3012_ = 0;
                    v___x_3013_ = crate::leanh::lean_alloc_ctor(1, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3013_, 0, v_pos_3010_);
                    crate::leanh::lean_ctor_set(v___x_3013_, 1, v_endPos_3011_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3013_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_3012_,
                    );
                    return v___x_3013_;
                }
                1 => {
                    v_pos_3014_ = crate::leanh::lean_ctor_get(v_x_3009_, 0);
                    v_endPos_3015_ = crate::leanh::lean_ctor_get(v_x_3009_, 1);
                    v_isSharedCheck_3023_ = (!crate::leanh::lean_is_exclusive(v_x_3009_)) as u8;
                    if v_isSharedCheck_3023_ == 0 {
                        v___x_3017_ = v_x_3009_;
                        v_isShared_3018_ = v_isSharedCheck_3023_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_endPos_3015_);
                        crate::leanh::lean_inc(v_pos_3014_);
                        crate::leanh::lean_dec(v_x_3009_);
                        v___x_3017_ = crate::leanh::lean_box(0);
                        v_isShared_3018_ = v_isSharedCheck_3023_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    return v_x_3009_;
                }
            },
            1 => {
                v___x_3019_ = 0;
                if v_isShared_3018_ == 0 {
                    v___x_3021_ = v___x_3017_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3022_ = crate::leanh::lean_alloc_ctor(1, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_pos_3014_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3022_, 1, v_endPos_3015_);
                    v___x_3021_ = v_reuseFailAlloc_3022_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3021_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_3019_,
                );
                return v___x_3021_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instBEqSourceInfo__lean_beq(
    mut v_x_3024_: *mut crate::leanh::LeanObject,
    mut v_x_3025_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_3024_) {
        0 => {
            if crate::leanh::lean_obj_tag(v_x_3025_) == 0 {
                let mut v_leading_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_pos_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_trailing_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_endPos_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_leading_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_pos_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_trailing_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_endPos_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3034_: u8 = 0;
                v_leading_3026_ = crate::leanh::lean_ctor_get(v_x_3024_, 0);
                crate::leanh::lean_inc_ref(v_leading_3026_);
                v_pos_3027_ = crate::leanh::lean_ctor_get(v_x_3024_, 1);
                crate::leanh::lean_inc(v_pos_3027_);
                v_trailing_3028_ = crate::leanh::lean_ctor_get(v_x_3024_, 2);
                crate::leanh::lean_inc_ref(v_trailing_3028_);
                v_endPos_3029_ = crate::leanh::lean_ctor_get(v_x_3024_, 3);
                crate::leanh::lean_inc(v_endPos_3029_);
                crate::leanh::lean_dec_ref_known(v_x_3024_, 4);
                v_leading_3030_ = crate::leanh::lean_ctor_get(v_x_3025_, 0);
                crate::leanh::lean_inc_ref(v_leading_3030_);
                v_pos_3031_ = crate::leanh::lean_ctor_get(v_x_3025_, 1);
                crate::leanh::lean_inc(v_pos_3031_);
                v_trailing_3032_ = crate::leanh::lean_ctor_get(v_x_3025_, 2);
                crate::leanh::lean_inc_ref(v_trailing_3032_);
                v_endPos_3033_ = crate::leanh::lean_ctor_get(v_x_3025_, 3);
                crate::leanh::lean_inc(v_endPos_3033_);
                crate::leanh::lean_dec_ref_known(v_x_3025_, 4);
                v___x_3034_ = l_Substring_Raw_beq(v_leading_3026_, v_leading_3030_);
                if v___x_3034_ == 0 {
                    crate::leanh::lean_dec(v_endPos_3033_);
                    crate::leanh::lean_dec_ref(v_trailing_3032_);
                    crate::leanh::lean_dec(v_pos_3031_);
                    crate::leanh::lean_dec(v_endPos_3029_);
                    crate::leanh::lean_dec_ref(v_trailing_3028_);
                    crate::leanh::lean_dec(v_pos_3027_);
                    return v___x_3034_;
                } else {
                    let mut v___x_3035_: u8 = 0;
                    v___x_3035_ = lean_nat_dec_eq(v_pos_3027_, v_pos_3031_);
                    crate::leanh::lean_dec(v_pos_3031_);
                    crate::leanh::lean_dec(v_pos_3027_);
                    if v___x_3035_ == 0 {
                        crate::leanh::lean_dec(v_endPos_3033_);
                        crate::leanh::lean_dec_ref(v_trailing_3032_);
                        crate::leanh::lean_dec(v_endPos_3029_);
                        crate::leanh::lean_dec_ref(v_trailing_3028_);
                        return v___x_3035_;
                    } else {
                        let mut v___x_3036_: u8 = 0;
                        v___x_3036_ = l_Substring_Raw_beq(v_trailing_3028_, v_trailing_3032_);
                        if v___x_3036_ == 0 {
                            crate::leanh::lean_dec(v_endPos_3033_);
                            crate::leanh::lean_dec(v_endPos_3029_);
                            return v___x_3036_;
                        } else {
                            let mut v___x_3037_: u8 = 0;
                            v___x_3037_ = lean_nat_dec_eq(v_endPos_3029_, v_endPos_3033_);
                            crate::leanh::lean_dec(v_endPos_3033_);
                            crate::leanh::lean_dec(v_endPos_3029_);
                            return v___x_3037_;
                        }
                    }
                }
            } else {
                let mut v___x_3038_: u8 = 0;
                crate::leanh::lean_dec_ref_known(v_x_3024_, 4);
                crate::leanh::lean_dec(v_x_3025_);
                v___x_3038_ = 0;
                return v___x_3038_;
            }
        }
        1 => {
            if crate::leanh::lean_obj_tag(v_x_3025_) == 1 {
                let mut v_pos_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_endPos_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_canonical_3041_: u8 = 0;
                let mut v_pos_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_endPos_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_canonical_3044_: u8 = 0;
                let mut v___x_3045_: u8 = 0;
                v_pos_3039_ = crate::leanh::lean_ctor_get(v_x_3024_, 0);
                crate::leanh::lean_inc(v_pos_3039_);
                v_endPos_3040_ = crate::leanh::lean_ctor_get(v_x_3024_, 1);
                crate::leanh::lean_inc(v_endPos_3040_);
                v_canonical_3041_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_3024_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                crate::leanh::lean_dec_ref_known(v_x_3024_, 2);
                v_pos_3042_ = crate::leanh::lean_ctor_get(v_x_3025_, 0);
                crate::leanh::lean_inc(v_pos_3042_);
                v_endPos_3043_ = crate::leanh::lean_ctor_get(v_x_3025_, 1);
                crate::leanh::lean_inc(v_endPos_3043_);
                v_canonical_3044_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_3025_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                crate::leanh::lean_dec_ref_known(v_x_3025_, 2);
                v___x_3045_ = lean_nat_dec_eq(v_pos_3039_, v_pos_3042_);
                crate::leanh::lean_dec(v_pos_3042_);
                crate::leanh::lean_dec(v_pos_3039_);
                if v___x_3045_ == 0 {
                    crate::leanh::lean_dec(v_endPos_3043_);
                    crate::leanh::lean_dec(v_endPos_3040_);
                    return v___x_3045_;
                } else {
                    let mut v___x_3046_: u8 = 0;
                    v___x_3046_ = lean_nat_dec_eq(v_endPos_3040_, v_endPos_3043_);
                    crate::leanh::lean_dec(v_endPos_3043_);
                    crate::leanh::lean_dec(v_endPos_3040_);
                    if v___x_3046_ == 0 {
                        return v___x_3046_;
                    } else {
                        if v_canonical_3041_ == 0 {
                            if v_canonical_3044_ == 0 {
                                return v___x_3046_;
                            } else {
                                return v_canonical_3041_;
                            }
                        } else {
                            return v_canonical_3044_;
                        }
                    }
                }
            } else {
                let mut v___x_3047_: u8 = 0;
                crate::leanh::lean_dec_ref_known(v_x_3024_, 2);
                crate::leanh::lean_dec(v_x_3025_);
                v___x_3047_ = 0;
                return v___x_3047_;
            }
        }
        _ => {
            if crate::leanh::lean_obj_tag(v_x_3025_) == 2 {
                let mut v___x_3048_: u8 = 0;
                v___x_3048_ = 1;
                return v___x_3048_;
            } else {
                let mut v___x_3049_: u8 = 0;
                crate::leanh::lean_dec(v_x_3025_);
                v___x_3049_ = 0;
                return v___x_3049_;
            }
        }
    }
}
pub unsafe fn l_Lean_instBEqSourceInfo__lean_beq___boxed(
    mut v_x_3050_: *mut crate::leanh::LeanObject,
    mut v_x_3051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3052_: u8 = 0;
    let mut v_r_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3052_ = l_Lean_instBEqSourceInfo__lean_beq(v_x_3050_, v_x_3051_);
    v_r_3053_ = crate::leanh::lean_box((v_res_3052_) as usize);
    return v_r_3053_;
}
pub unsafe fn l_Lean_unreachIsNodeMissing(
    mut v_00_u03b2_3056_: *mut crate::leanh::LeanObject,
    mut v_a_3057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    core::hint::unreachable_unchecked();
}
pub unsafe fn l_Lean_unreachIsNodeAtom(
    mut v_00_u03b2_3058_: *mut crate::leanh::LeanObject,
    mut v_info_3059_: *mut crate::leanh::LeanObject,
    mut v_val_3060_: *mut crate::leanh::LeanObject,
    mut v_a_3061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    core::hint::unreachable_unchecked();
}
pub unsafe fn l_Lean_unreachIsNodeAtom___boxed(
    mut v_00_u03b2_3062_: *mut crate::leanh::LeanObject,
    mut v_info_3063_: *mut crate::leanh::LeanObject,
    mut v_val_3064_: *mut crate::leanh::LeanObject,
    mut v_a_3065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3066_ = l_Lean_unreachIsNodeAtom(v_00_u03b2_3062_, v_info_3063_, v_val_3064_, v_a_3065_);
    crate::leanh::lean_dec_ref(v_val_3064_);
    crate::leanh::lean_dec(v_info_3063_);
    return v_res_3066_;
}
pub unsafe fn l_Lean_unreachIsNodeIdent(
    mut v_00_u03b2_3067_: *mut crate::leanh::LeanObject,
    mut v_info_3068_: *mut crate::leanh::LeanObject,
    mut v_rawVal_3069_: *mut crate::leanh::LeanObject,
    mut v_val_3070_: *mut crate::leanh::LeanObject,
    mut v_preresolved_3071_: *mut crate::leanh::LeanObject,
    mut v_a_3072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    core::hint::unreachable_unchecked();
}
pub unsafe fn l_Lean_unreachIsNodeIdent___boxed(
    mut v_00_u03b2_3073_: *mut crate::leanh::LeanObject,
    mut v_info_3074_: *mut crate::leanh::LeanObject,
    mut v_rawVal_3075_: *mut crate::leanh::LeanObject,
    mut v_val_3076_: *mut crate::leanh::LeanObject,
    mut v_preresolved_3077_: *mut crate::leanh::LeanObject,
    mut v_a_3078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3079_ = l_Lean_unreachIsNodeIdent(
        v_00_u03b2_3073_,
        v_info_3074_,
        v_rawVal_3075_,
        v_val_3076_,
        v_preresolved_3077_,
        v_a_3078_,
    );
    crate::leanh::lean_dec(v_preresolved_3077_);
    crate::leanh::lean_dec(v_val_3076_);
    crate::leanh::lean_dec_ref(v_rawVal_3075_);
    crate::leanh::lean_dec(v_info_3074_);
    return v_res_3079_;
}
pub unsafe fn l_Lean_isLitKind(mut v_k_3095_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___y_3097_: u8 = 0;
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: u8 = 0;
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: u8 = 0;
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: u8 = 0;
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: u8 = 0;
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3104_ = l_Lean_isLitKind___closed__7;
                v___x_3105_ = lean_name_eq(v_k_3095_, v___x_3104_);
                if v___x_3105_ == 0 {
                    v___x_3106_ = l_Lean_isLitKind___closed__9;
                    v___x_3107_ = lean_name_eq(v_k_3095_, v___x_3106_);
                    v___y_3097_ = v___x_3107_;
                    state = 1;
                    continue;
                } else {
                    v___y_3097_ = v___x_3105_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_3097_ == 0 {
                    v___x_3098_ = l_Lean_isLitKind___closed__1;
                    v___x_3099_ = lean_name_eq(v_k_3095_, v___x_3098_);
                    if v___x_3099_ == 0 {
                        v___x_3100_ = l_Lean_isLitKind___closed__3;
                        v___x_3101_ = lean_name_eq(v_k_3095_, v___x_3100_);
                        if v___x_3101_ == 0 {
                            v___x_3102_ = l_Lean_isLitKind___closed__5;
                            v___x_3103_ = lean_name_eq(v_k_3095_, v___x_3102_);
                            return v___x_3103_;
                        } else {
                            return v___x_3101_;
                        }
                    } else {
                        return v___x_3099_;
                    }
                } else {
                    return v___y_3097_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isLitKind___boxed(
    mut v_k_3108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3109_: u8 = 0;
    let mut v_r_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3109_ = l_Lean_isLitKind(v_k_3108_);
    crate::leanh::lean_dec(v_k_3108_);
    v_r_3110_ = crate::leanh::lean_box((v_res_3109_) as usize);
    return v_r_3110_;
}
pub unsafe fn l_Lean_SyntaxNode_getKind(
    mut v_n_3111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_3112_ = crate::leanh::lean_ctor_get(v_n_3111_, 1);
    crate::leanh::lean_inc(v_kind_3112_);
    return v_kind_3112_;
}
pub unsafe fn l_Lean_SyntaxNode_getKind___boxed(
    mut v_n_3113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3114_ = l_Lean_SyntaxNode_getKind(v_n_3113_);
    crate::leanh::lean_dec(v_n_3113_);
    return v_res_3114_;
}
pub unsafe fn l_Lean_SyntaxNode_withArgs___redArg(
    mut v_n_3115_: *mut crate::leanh::LeanObject,
    mut v_fn_3116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_args_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_args_3117_ = crate::leanh::lean_ctor_get(v_n_3115_, 2);
    crate::leanh::lean_inc_ref(v_args_3117_);
    crate::leanh::lean_dec(v_n_3115_);
    v___x_3118_ = crate::leanh::lean_apply_1(v_fn_3116_, v_args_3117_);
    return v___x_3118_;
}
pub unsafe fn l_Lean_SyntaxNode_withArgs(
    mut v_00_u03b2_3119_: *mut crate::leanh::LeanObject,
    mut v_n_3120_: *mut crate::leanh::LeanObject,
    mut v_fn_3121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_args_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_args_3122_ = crate::leanh::lean_ctor_get(v_n_3120_, 2);
    crate::leanh::lean_inc_ref(v_args_3122_);
    crate::leanh::lean_dec(v_n_3120_);
    v___x_3123_ = crate::leanh::lean_apply_1(v_fn_3121_, v_args_3122_);
    return v___x_3123_;
}
pub unsafe fn l_Lean_SyntaxNode_getNumArgs(
    mut v_n_3124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_args_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_args_3125_ = crate::leanh::lean_ctor_get(v_n_3124_, 2);
    v___x_3126_ = lean_array_get_size(v_args_3125_);
    return v___x_3126_;
}
pub unsafe fn l_Lean_SyntaxNode_getNumArgs___boxed(
    mut v_n_3127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3128_ = l_Lean_SyntaxNode_getNumArgs(v_n_3127_);
    crate::leanh::lean_dec(v_n_3127_);
    return v_res_3128_;
}
pub unsafe fn l_Lean_SyntaxNode_getArg(
    mut v_n_3129_: *mut crate::leanh::LeanObject,
    mut v_i_3130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_args_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_args_3131_ = crate::leanh::lean_ctor_get(v_n_3129_, 2);
    v___x_3132_ = crate::leanh::lean_box(0);
    v___x_3133_ = lean_array_get_borrowed(v___x_3132_, v_args_3131_, v_i_3130_);
    crate::leanh::lean_inc(v___x_3133_);
    return v___x_3133_;
}
pub unsafe fn l_Lean_SyntaxNode_getArg___boxed(
    mut v_n_3134_: *mut crate::leanh::LeanObject,
    mut v_i_3135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3136_ = l_Lean_SyntaxNode_getArg(v_n_3134_, v_i_3135_);
    crate::leanh::lean_dec(v_i_3135_);
    crate::leanh::lean_dec(v_n_3134_);
    return v_res_3136_;
}
pub unsafe fn l_Lean_SyntaxNode_getArgs(
    mut v_n_3137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_args_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_args_3138_ = crate::leanh::lean_ctor_get(v_n_3137_, 2);
    crate::leanh::lean_inc_ref(v_args_3138_);
    return v_args_3138_;
}
pub unsafe fn l_Lean_SyntaxNode_getArgs___boxed(
    mut v_n_3139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3140_ = l_Lean_SyntaxNode_getArgs(v_n_3139_);
    crate::leanh::lean_dec(v_n_3139_);
    return v_res_3140_;
}
pub unsafe fn l_Lean_SyntaxNode_modifyArgs(
    mut v_n_3141_: *mut crate::leanh::LeanObject,
    mut v_fn_3142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_info_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3148_: u8 = 0;
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3153_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_info_3143_ = crate::leanh::lean_ctor_get(v_n_3141_, 0);
                v_kind_3144_ = crate::leanh::lean_ctor_get(v_n_3141_, 1);
                v_args_3145_ = crate::leanh::lean_ctor_get(v_n_3141_, 2);
                v_isSharedCheck_3153_ = (!crate::leanh::lean_is_exclusive(v_n_3141_)) as u8;
                if v_isSharedCheck_3153_ == 0 {
                    v___x_3147_ = v_n_3141_;
                    v_isShared_3148_ = v_isSharedCheck_3153_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_args_3145_);
                    crate::leanh::lean_inc(v_kind_3144_);
                    crate::leanh::lean_inc(v_info_3143_);
                    crate::leanh::lean_dec(v_n_3141_);
                    v___x_3147_ = crate::leanh::lean_box(0);
                    v_isShared_3148_ = v_isSharedCheck_3153_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3149_ = crate::leanh::lean_apply_1(v_fn_3142_, v_args_3145_);
                if v_isShared_3148_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3147_, 2, v___x_3149_);
                    v___x_3151_ = v___x_3147_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3152_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_info_3143_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3152_, 1, v_kind_3144_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3152_, 2, v___x_3149_);
                    v___x_3151_ = v_reuseFailAlloc_3152_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3151_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(
    mut v_x_3154_: *mut crate::leanh::LeanObject,
    mut v_x_3155_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3154_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_3155_) == 0 {
            let mut v___x_3156_: u8 = 0;
            v___x_3156_ = 1;
            return v___x_3156_;
        } else {
            let mut v___x_3157_: u8 = 0;
            v___x_3157_ = 0;
            return v___x_3157_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_3155_) == 0 {
            let mut v___x_3158_: u8 = 0;
            v___x_3158_ = 0;
            return v___x_3158_;
        } else {
            let mut v_val_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3161_: u8 = 0;
            v_val_3159_ = crate::leanh::lean_ctor_get(v_x_3154_, 0);
            v_val_3160_ = crate::leanh::lean_ctor_get(v_x_3155_, 0);
            v___x_3161_ = l_Lean_Syntax_instBEqRange_beq(v_val_3159_, v_val_3160_);
            return v___x_3161_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1___boxed(
    mut v_x_3162_: *mut crate::leanh::LeanObject,
    mut v_x_3163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3164_: u8 = 0;
    let mut v_r_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3164_ =
        l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(v_x_3162_, v_x_3163_);
    crate::leanh::lean_dec(v_x_3163_);
    crate::leanh::lean_dec(v_x_3162_);
    v_r_3165_ = crate::leanh::lean_box((v_res_3164_) as usize);
    return v_r_3165_;
}
pub unsafe fn l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(
    mut v_x_3166_: *mut crate::leanh::LeanObject,
    mut v_x_3167_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3168_: u8 = 0;
    let mut v___x_3169_: u8 = 0;
    let mut v___x_3170_: u8 = 0;
    let mut v_head_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3166_) == 0 {
                    if crate::leanh::lean_obj_tag(v_x_3167_) == 0 {
                        v___x_3168_ = 1;
                        return v___x_3168_;
                    } else {
                        v___x_3169_ = 0;
                        return v___x_3169_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_x_3167_) == 0 {
                        v___x_3170_ = 0;
                        return v___x_3170_;
                    } else {
                        v_head_3171_ = crate::leanh::lean_ctor_get(v_x_3166_, 0);
                        v_tail_3172_ = crate::leanh::lean_ctor_get(v_x_3166_, 1);
                        v_head_3173_ = crate::leanh::lean_ctor_get(v_x_3167_, 0);
                        v_tail_3174_ = crate::leanh::lean_ctor_get(v_x_3167_, 1);
                        v___x_3175_ =
                            l_Lean_Syntax_instBEqPreresolved_beq(v_head_3171_, v_head_3173_);
                        if v___x_3175_ == 0 {
                            return v___x_3175_;
                        } else {
                            v_x_3166_ = v_tail_3172_;
                            v_x_3167_ = v_tail_3174_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2___boxed(
    mut v_x_3177_: *mut crate::leanh::LeanObject,
    mut v_x_3178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3179_: u8 = 0;
    let mut v_r_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3179_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(v_x_3177_, v_x_3178_);
    crate::leanh::lean_dec(v_x_3178_);
    crate::leanh::lean_dec(v_x_3177_);
    v_r_3180_ = crate::leanh::lean_box((v_res_3179_) as usize);
    return v_r_3180_;
}
pub unsafe fn l_Lean_Syntax_structRangeEq(
    mut v_x_3181_: *mut crate::leanh::LeanObject,
    mut v_x_3182_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3183_: u8 = 0;
    let mut v___x_3184_: u8 = 0;
    let mut v_info_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3192_: u8 = 0;
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: u8 = 0;
    let mut v___x_3196_: u8 = 0;
    let mut v___x_3197_: u8 = 0;
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: u8 = 0;
    let mut v___x_3201_: u8 = 0;
    let mut v___x_3202_: u8 = 0;
    let mut v_info_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: u8 = 0;
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: u8 = 0;
    let mut v___x_3211_: u8 = 0;
    let mut v___x_3212_: u8 = 0;
    let mut v_info_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rawVal_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preresolved_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rawVal_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preresolved_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3222_: u8 = 0;
    let mut v___x_3223_: u8 = 0;
    let mut v___x_3224_: u8 = 0;
    let mut v___x_3225_: u8 = 0;
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: u8 = 0;
    let mut v___x_3229_: u8 = 0;
    let mut v___x_3230_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_3181_) {
                0 => {
                    if crate::leanh::lean_obj_tag(v_x_3182_) == 0 {
                        v___x_3183_ = 1;
                        return v___x_3183_;
                    } else {
                        crate::leanh::lean_dec(v_x_3182_);
                        v___x_3184_ = 0;
                        return v___x_3184_;
                    }
                }
                1 => {
                    if crate::leanh::lean_obj_tag(v_x_3182_) == 1 {
                        v_info_3185_ = crate::leanh::lean_ctor_get(v_x_3181_, 0);
                        crate::leanh::lean_inc(v_info_3185_);
                        v_kind_3186_ = crate::leanh::lean_ctor_get(v_x_3181_, 1);
                        crate::leanh::lean_inc(v_kind_3186_);
                        v_args_3187_ = crate::leanh::lean_ctor_get(v_x_3181_, 2);
                        crate::leanh::lean_inc_ref(v_args_3187_);
                        crate::leanh::lean_dec_ref_known(v_x_3181_, 3);
                        v_info_3188_ = crate::leanh::lean_ctor_get(v_x_3182_, 0);
                        crate::leanh::lean_inc(v_info_3188_);
                        v_kind_3189_ = crate::leanh::lean_ctor_get(v_x_3182_, 1);
                        crate::leanh::lean_inc(v_kind_3189_);
                        v_args_3190_ = crate::leanh::lean_ctor_get(v_x_3182_, 2);
                        crate::leanh::lean_inc_ref(v_args_3190_);
                        crate::leanh::lean_dec_ref_known(v_x_3182_, 3);
                        v___x_3197_ = 0;
                        v___x_3198_ = l_Lean_SourceInfo_getRange_x3f(v___x_3197_, v_info_3185_);
                        crate::leanh::lean_dec(v_info_3185_);
                        v___x_3199_ = l_Lean_SourceInfo_getRange_x3f(v___x_3197_, v_info_3188_);
                        crate::leanh::lean_dec(v_info_3188_);
                        v___x_3200_ =
                            l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(
                                v___x_3198_,
                                v___x_3199_,
                            );
                        crate::leanh::lean_dec(v___x_3199_);
                        crate::leanh::lean_dec(v___x_3198_);
                        if v___x_3200_ == 0 {
                            crate::leanh::lean_dec(v_kind_3189_);
                            crate::leanh::lean_dec(v_kind_3186_);
                            v___y_3192_ = v___x_3200_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3201_ = lean_name_eq(v_kind_3186_, v_kind_3189_);
                            crate::leanh::lean_dec(v_kind_3189_);
                            crate::leanh::lean_dec(v_kind_3186_);
                            v___y_3192_ = v___x_3201_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_3181_, 3);
                        crate::leanh::lean_dec(v_x_3182_);
                        v___x_3202_ = 0;
                        return v___x_3202_;
                    }
                }
                2 => {
                    if crate::leanh::lean_obj_tag(v_x_3182_) == 2 {
                        v_info_3203_ = crate::leanh::lean_ctor_get(v_x_3181_, 0);
                        crate::leanh::lean_inc(v_info_3203_);
                        v_val_3204_ = crate::leanh::lean_ctor_get(v_x_3181_, 1);
                        crate::leanh::lean_inc_ref(v_val_3204_);
                        crate::leanh::lean_dec_ref_known(v_x_3181_, 2);
                        v_info_3205_ = crate::leanh::lean_ctor_get(v_x_3182_, 0);
                        crate::leanh::lean_inc(v_info_3205_);
                        v_val_3206_ = crate::leanh::lean_ctor_get(v_x_3182_, 1);
                        crate::leanh::lean_inc_ref(v_val_3206_);
                        crate::leanh::lean_dec_ref_known(v_x_3182_, 2);
                        v___x_3207_ = 0;
                        v___x_3208_ = l_Lean_SourceInfo_getRange_x3f(v___x_3207_, v_info_3203_);
                        crate::leanh::lean_dec(v_info_3203_);
                        v___x_3209_ = l_Lean_SourceInfo_getRange_x3f(v___x_3207_, v_info_3205_);
                        crate::leanh::lean_dec(v_info_3205_);
                        v___x_3210_ =
                            l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(
                                v___x_3208_,
                                v___x_3209_,
                            );
                        crate::leanh::lean_dec(v___x_3209_);
                        crate::leanh::lean_dec(v___x_3208_);
                        if v___x_3210_ == 0 {
                            crate::leanh::lean_dec_ref(v_val_3206_);
                            crate::leanh::lean_dec_ref(v_val_3204_);
                            return v___x_3210_;
                        } else {
                            v___x_3211_ = lean_string_dec_eq(v_val_3204_, v_val_3206_);
                            crate::leanh::lean_dec_ref(v_val_3206_);
                            crate::leanh::lean_dec_ref(v_val_3204_);
                            return v___x_3211_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_3181_, 2);
                        crate::leanh::lean_dec(v_x_3182_);
                        v___x_3212_ = 0;
                        return v___x_3212_;
                    }
                }
                _ => {
                    if crate::leanh::lean_obj_tag(v_x_3182_) == 3 {
                        v_info_3213_ = crate::leanh::lean_ctor_get(v_x_3181_, 0);
                        crate::leanh::lean_inc(v_info_3213_);
                        v_rawVal_3214_ = crate::leanh::lean_ctor_get(v_x_3181_, 1);
                        crate::leanh::lean_inc_ref(v_rawVal_3214_);
                        v_val_3215_ = crate::leanh::lean_ctor_get(v_x_3181_, 2);
                        crate::leanh::lean_inc(v_val_3215_);
                        v_preresolved_3216_ = crate::leanh::lean_ctor_get(v_x_3181_, 3);
                        crate::leanh::lean_inc(v_preresolved_3216_);
                        crate::leanh::lean_dec_ref_known(v_x_3181_, 4);
                        v_info_3217_ = crate::leanh::lean_ctor_get(v_x_3182_, 0);
                        crate::leanh::lean_inc(v_info_3217_);
                        v_rawVal_3218_ = crate::leanh::lean_ctor_get(v_x_3182_, 1);
                        crate::leanh::lean_inc_ref(v_rawVal_3218_);
                        v_val_3219_ = crate::leanh::lean_ctor_get(v_x_3182_, 2);
                        crate::leanh::lean_inc(v_val_3219_);
                        v_preresolved_3220_ = crate::leanh::lean_ctor_get(v_x_3182_, 3);
                        crate::leanh::lean_inc(v_preresolved_3220_);
                        crate::leanh::lean_dec_ref_known(v_x_3182_, 4);
                        v___x_3225_ = 0;
                        v___x_3226_ = l_Lean_SourceInfo_getRange_x3f(v___x_3225_, v_info_3213_);
                        crate::leanh::lean_dec(v_info_3213_);
                        v___x_3227_ = l_Lean_SourceInfo_getRange_x3f(v___x_3225_, v_info_3217_);
                        crate::leanh::lean_dec(v_info_3217_);
                        v___x_3228_ =
                            l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(
                                v___x_3226_,
                                v___x_3227_,
                            );
                        crate::leanh::lean_dec(v___x_3227_);
                        crate::leanh::lean_dec(v___x_3226_);
                        if v___x_3228_ == 0 {
                            crate::leanh::lean_dec_ref(v_rawVal_3218_);
                            crate::leanh::lean_dec_ref(v_rawVal_3214_);
                            v___y_3222_ = v___x_3228_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3229_ = l_Substring_Raw_beq(v_rawVal_3214_, v_rawVal_3218_);
                            v___y_3222_ = v___x_3229_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_3181_, 4);
                        crate::leanh::lean_dec(v_x_3182_);
                        v___x_3230_ = 0;
                        return v___x_3230_;
                    }
                }
            },
            1 => {
                if v___y_3192_ == 0 {
                    crate::leanh::lean_dec_ref(v_args_3190_);
                    crate::leanh::lean_dec_ref(v_args_3187_);
                    return v___y_3192_;
                } else {
                    v___x_3193_ = lean_array_get_size(v_args_3187_);
                    v___x_3194_ = lean_array_get_size(v_args_3190_);
                    v___x_3195_ = lean_nat_dec_eq(v___x_3193_, v___x_3194_);
                    if v___x_3195_ == 0 {
                        crate::leanh::lean_dec_ref(v_args_3190_);
                        crate::leanh::lean_dec_ref(v_args_3187_);
                        return v___x_3195_;
                    } else {
                        v___x_3196_ =
                            l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(
                                v_args_3187_,
                                v_args_3190_,
                                v___x_3193_,
                            );
                        crate::leanh::lean_dec_ref(v_args_3190_);
                        crate::leanh::lean_dec_ref(v_args_3187_);
                        return v___x_3196_;
                    }
                }
            }
            2 => {
                if v___y_3222_ == 0 {
                    crate::leanh::lean_dec(v_preresolved_3220_);
                    crate::leanh::lean_dec(v_val_3219_);
                    crate::leanh::lean_dec(v_preresolved_3216_);
                    crate::leanh::lean_dec(v_val_3215_);
                    return v___y_3222_;
                } else {
                    v___x_3223_ = lean_name_eq(v_val_3215_, v_val_3219_);
                    crate::leanh::lean_dec(v_val_3219_);
                    crate::leanh::lean_dec(v_val_3215_);
                    if v___x_3223_ == 0 {
                        crate::leanh::lean_dec(v_preresolved_3220_);
                        crate::leanh::lean_dec(v_preresolved_3216_);
                        return v___x_3223_;
                    } else {
                        v___x_3224_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(
                            v_preresolved_3216_,
                            v_preresolved_3220_,
                        );
                        crate::leanh::lean_dec(v_preresolved_3220_);
                        crate::leanh::lean_dec(v_preresolved_3216_);
                        return v___x_3224_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(
    mut v_xs_3231_: *mut crate::leanh::LeanObject,
    mut v_ys_3232_: *mut crate::leanh::LeanObject,
    mut v_x_3233_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3235_: u8 = 0;
    let mut v_one_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3234_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_3235_ = lean_nat_dec_eq(v_x_3233_, v_zero_3234_);
                if v_isZero_3235_ == 1 {
                    crate::leanh::lean_dec(v_x_3233_);
                    return v_isZero_3235_;
                } else {
                    v_one_3236_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_3237_ = lean_nat_sub(v_x_3233_, v_one_3236_);
                    crate::leanh::lean_dec(v_x_3233_);
                    v___x_3238_ = lean_array_fget_borrowed(v_xs_3231_, v_n_3237_);
                    v___x_3239_ = lean_array_fget_borrowed(v_ys_3232_, v_n_3237_);
                    crate::leanh::lean_inc(v___x_3239_);
                    crate::leanh::lean_inc(v___x_3238_);
                    v___x_3240_ = l_Lean_Syntax_structRangeEq(v___x_3238_, v___x_3239_);
                    if v___x_3240_ == 0 {
                        crate::leanh::lean_dec(v_n_3237_);
                        return v___x_3240_;
                    } else {
                        v_x_3233_ = v_n_3237_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg___boxed(
    mut v_xs_3242_: *mut crate::leanh::LeanObject,
    mut v_ys_3243_: *mut crate::leanh::LeanObject,
    mut v_x_3244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3245_: u8 = 0;
    let mut v_r_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3245_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(
        v_xs_3242_, v_ys_3243_, v_x_3244_,
    );
    crate::leanh::lean_dec_ref(v_ys_3243_);
    crate::leanh::lean_dec_ref(v_xs_3242_);
    v_r_3246_ = crate::leanh::lean_box((v_res_3245_) as usize);
    return v_r_3246_;
}
pub unsafe fn l_Lean_Syntax_structRangeEq___boxed(
    mut v_x_3247_: *mut crate::leanh::LeanObject,
    mut v_x_3248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3249_: u8 = 0;
    let mut v_r_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3249_ = l_Lean_Syntax_structRangeEq(v_x_3247_, v_x_3248_);
    v_r_3250_ = crate::leanh::lean_box((v_res_3249_) as usize);
    return v_r_3250_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0(
    mut v_xs_3251_: *mut crate::leanh::LeanObject,
    mut v_ys_3252_: *mut crate::leanh::LeanObject,
    mut v_hsz_3253_: *mut crate::leanh::LeanObject,
    mut v_x_3254_: *mut crate::leanh::LeanObject,
    mut v_x_3255_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3256_: u8 = 0;
    v___x_3256_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(
        v_xs_3251_, v_ys_3252_, v_x_3254_,
    );
    return v___x_3256_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___boxed(
    mut v_xs_3257_: *mut crate::leanh::LeanObject,
    mut v_ys_3258_: *mut crate::leanh::LeanObject,
    mut v_hsz_3259_: *mut crate::leanh::LeanObject,
    mut v_x_3260_: *mut crate::leanh::LeanObject,
    mut v_x_3261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3262_: u8 = 0;
    let mut v_r_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3262_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0(
        v_xs_3257_,
        v_ys_3258_,
        v_hsz_3259_,
        v_x_3260_,
        v_x_3261_,
    );
    crate::leanh::lean_dec_ref(v_ys_3258_);
    crate::leanh::lean_dec_ref(v_xs_3257_);
    v_r_3263_ = crate::leanh::lean_box((v_res_3262_) as usize);
    return v_r_3263_;
}
pub unsafe fn l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0(
    mut v___x_3264_: u8,
    mut v_x_3265_: *mut crate::leanh::LeanObject,
) -> u8 {
    return v___x_3264_;
}
pub unsafe fn l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed(
    mut v___x_3266_: *mut crate::leanh::LeanObject,
    mut v_x_3267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_207__boxed_3268_: u8 = 0;
    let mut v_res_3269_: u8 = 0;
    let mut v_r_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_207__boxed_3268_ = (crate::leanh::lean_unbox(v___x_3266_) as u8);
    v_res_3269_ =
        l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0(v___x_207__boxed_3268_, v_x_3267_);
    v_r_3270_ = crate::leanh::lean_box((v_res_3269_) as usize);
    return v_r_3270_;
}
pub unsafe fn l_Lean_Syntax_structRangeEqWithTraceReuse(
    mut v_opts_3280_: *mut crate::leanh::LeanObject,
    mut v_stx1_3281_: *mut crate::leanh::LeanObject,
    mut v_stx2_3282_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3283_: u8 = 0;
    let mut v___x_3284_: u8 = 0;
    let mut v_map_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3289_: u8 = 0;
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: u8 = 0;
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_stx2_3282_);
                crate::leanh::lean_inc(v_stx1_3281_);
                v___x_3283_ = l_Lean_Syntax_structRangeEq(v_stx1_3281_, v_stx2_3282_);
                v___x_3284_ = 1;
                if v___x_3283_ == 0 {
                    v_map_3285_ = crate::leanh::lean_ctor_get(v_opts_3280_, 0);
                    v___x_3286_ = crate::leanh::lean_box((v___x_3283_) as usize);
                    v___f_3287_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_3287_, 0, v___x_3286_);
                    v___x_3304_ = l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5;
                    v___x_3305_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3285_, v___x_3304_);
                    if crate::leanh::lean_obj_tag(v___x_3305_) == 0 {
                        v___y_3289_ = v___x_3283_;
                        state = 1;
                        continue;
                    } else {
                        v_val_3306_ = crate::leanh::lean_ctor_get(v___x_3305_, 0);
                        crate::leanh::lean_inc(v_val_3306_);
                        crate::leanh::lean_dec_ref_known(v___x_3305_, 1);
                        if crate::leanh::lean_obj_tag(v_val_3306_) == 1 {
                            v_v_3307_ = crate::leanh::lean_ctor_get_uint8(v_val_3306_, 0 as u32);
                            crate::leanh::lean_dec_ref_known(v_val_3306_, 0);
                            v___y_3289_ = v_v_3307_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_val_3306_);
                            v___y_3289_ = v___x_3283_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_stx2_3282_);
                    crate::leanh::lean_dec(v_stx1_3281_);
                    return v___x_3284_;
                }
            }
            1 => {
                if v___y_3289_ == 0 {
                    crate::leanh::lean_dec_ref(v___f_3287_);
                    crate::leanh::lean_dec(v_stx2_3282_);
                    crate::leanh::lean_dec(v_stx1_3281_);
                    return v___x_3283_;
                } else {
                    v___x_3290_ = l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0;
                    v___x_3291_ = crate::leanh::lean_box(0);
                    v___x_3292_ = l_Lean_Syntax_formatStx(v_stx1_3281_, v___x_3291_, v___x_3284_);
                    v___x_3293_ = l_Std_Format_defWidth;
                    v___x_3294_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3295_ =
                        l_Std_Format_pretty(v___x_3292_, v___x_3293_, v___x_3294_, v___x_3294_);
                    v___x_3296_ = lean_string_append(v___x_3290_, v___x_3295_);
                    crate::leanh::lean_dec_ref(v___x_3295_);
                    v___x_3297_ = l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1;
                    v___x_3298_ = lean_string_append(v___x_3296_, v___x_3297_);
                    v___x_3299_ = l_Lean_Syntax_formatStx(v_stx2_3282_, v___x_3291_, v___x_3284_);
                    v___x_3300_ =
                        l_Std_Format_pretty(v___x_3299_, v___x_3293_, v___x_3294_, v___x_3294_);
                    v___x_3301_ = lean_string_append(v___x_3298_, v___x_3300_);
                    crate::leanh::lean_dec_ref(v___x_3300_);
                    v___x_3302_ = lean_dbg_trace(v___x_3301_, v___f_3287_);
                    v___x_3303_ = (crate::leanh::lean_unbox(v___x_3302_) as u8);
                    crate::leanh::lean_dec(v___x_3302_);
                    return v___x_3303_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_structRangeEqWithTraceReuse___boxed(
    mut v_opts_3308_: *mut crate::leanh::LeanObject,
    mut v_stx1_3309_: *mut crate::leanh::LeanObject,
    mut v_stx2_3310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3311_: u8 = 0;
    let mut v_r_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3311_ =
        l_Lean_Syntax_structRangeEqWithTraceReuse(v_opts_3308_, v_stx1_3309_, v_stx2_3310_);
    crate::leanh::lean_dec_ref(v_opts_3308_);
    v_r_3312_ = crate::leanh::lean_box((v_res_3311_) as usize);
    return v_r_3312_;
}
pub unsafe fn l_Lean_Syntax_eqWithInfo(
    mut v_x_3313_: *mut crate::leanh::LeanObject,
    mut v_x_3314_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3315_: u8 = 0;
    let mut v___x_3316_: u8 = 0;
    let mut v_info_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3324_: u8 = 0;
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: u8 = 0;
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3329_: u8 = 0;
    let mut v___x_3330_: u8 = 0;
    let mut v___x_3331_: u8 = 0;
    let mut v_info_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: u8 = 0;
    let mut v___x_3337_: u8 = 0;
    let mut v___x_3338_: u8 = 0;
    let mut v_info_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rawVal_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preresolved_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rawVal_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preresolved_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3348_: u8 = 0;
    let mut v___x_3349_: u8 = 0;
    let mut v___x_3350_: u8 = 0;
    let mut v___x_3351_: u8 = 0;
    let mut v___x_3352_: u8 = 0;
    let mut v___x_3353_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_3313_) {
                0 => {
                    if crate::leanh::lean_obj_tag(v_x_3314_) == 0 {
                        v___x_3315_ = 1;
                        return v___x_3315_;
                    } else {
                        crate::leanh::lean_dec(v_x_3314_);
                        v___x_3316_ = 0;
                        return v___x_3316_;
                    }
                }
                1 => {
                    if crate::leanh::lean_obj_tag(v_x_3314_) == 1 {
                        v_info_3317_ = crate::leanh::lean_ctor_get(v_x_3313_, 0);
                        crate::leanh::lean_inc(v_info_3317_);
                        v_kind_3318_ = crate::leanh::lean_ctor_get(v_x_3313_, 1);
                        crate::leanh::lean_inc(v_kind_3318_);
                        v_args_3319_ = crate::leanh::lean_ctor_get(v_x_3313_, 2);
                        crate::leanh::lean_inc_ref(v_args_3319_);
                        crate::leanh::lean_dec_ref_known(v_x_3313_, 3);
                        v_info_3320_ = crate::leanh::lean_ctor_get(v_x_3314_, 0);
                        crate::leanh::lean_inc(v_info_3320_);
                        v_kind_3321_ = crate::leanh::lean_ctor_get(v_x_3314_, 1);
                        crate::leanh::lean_inc(v_kind_3321_);
                        v_args_3322_ = crate::leanh::lean_ctor_get(v_x_3314_, 2);
                        crate::leanh::lean_inc_ref(v_args_3322_);
                        crate::leanh::lean_dec_ref_known(v_x_3314_, 3);
                        v___x_3329_ =
                            l_Lean_instBEqSourceInfo__lean_beq(v_info_3317_, v_info_3320_);
                        if v___x_3329_ == 0 {
                            crate::leanh::lean_dec(v_kind_3321_);
                            crate::leanh::lean_dec(v_kind_3318_);
                            v___y_3324_ = v___x_3329_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3330_ = lean_name_eq(v_kind_3318_, v_kind_3321_);
                            crate::leanh::lean_dec(v_kind_3321_);
                            crate::leanh::lean_dec(v_kind_3318_);
                            v___y_3324_ = v___x_3330_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_3313_, 3);
                        crate::leanh::lean_dec(v_x_3314_);
                        v___x_3331_ = 0;
                        return v___x_3331_;
                    }
                }
                2 => {
                    if crate::leanh::lean_obj_tag(v_x_3314_) == 2 {
                        v_info_3332_ = crate::leanh::lean_ctor_get(v_x_3313_, 0);
                        crate::leanh::lean_inc(v_info_3332_);
                        v_val_3333_ = crate::leanh::lean_ctor_get(v_x_3313_, 1);
                        crate::leanh::lean_inc_ref(v_val_3333_);
                        crate::leanh::lean_dec_ref_known(v_x_3313_, 2);
                        v_info_3334_ = crate::leanh::lean_ctor_get(v_x_3314_, 0);
                        crate::leanh::lean_inc(v_info_3334_);
                        v_val_3335_ = crate::leanh::lean_ctor_get(v_x_3314_, 1);
                        crate::leanh::lean_inc_ref(v_val_3335_);
                        crate::leanh::lean_dec_ref_known(v_x_3314_, 2);
                        v___x_3336_ =
                            l_Lean_instBEqSourceInfo__lean_beq(v_info_3332_, v_info_3334_);
                        if v___x_3336_ == 0 {
                            crate::leanh::lean_dec_ref(v_val_3335_);
                            crate::leanh::lean_dec_ref(v_val_3333_);
                            return v___x_3336_;
                        } else {
                            v___x_3337_ = lean_string_dec_eq(v_val_3333_, v_val_3335_);
                            crate::leanh::lean_dec_ref(v_val_3335_);
                            crate::leanh::lean_dec_ref(v_val_3333_);
                            return v___x_3337_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_3313_, 2);
                        crate::leanh::lean_dec(v_x_3314_);
                        v___x_3338_ = 0;
                        return v___x_3338_;
                    }
                }
                _ => {
                    if crate::leanh::lean_obj_tag(v_x_3314_) == 3 {
                        v_info_3339_ = crate::leanh::lean_ctor_get(v_x_3313_, 0);
                        crate::leanh::lean_inc(v_info_3339_);
                        v_rawVal_3340_ = crate::leanh::lean_ctor_get(v_x_3313_, 1);
                        crate::leanh::lean_inc_ref(v_rawVal_3340_);
                        v_val_3341_ = crate::leanh::lean_ctor_get(v_x_3313_, 2);
                        crate::leanh::lean_inc(v_val_3341_);
                        v_preresolved_3342_ = crate::leanh::lean_ctor_get(v_x_3313_, 3);
                        crate::leanh::lean_inc(v_preresolved_3342_);
                        crate::leanh::lean_dec_ref_known(v_x_3313_, 4);
                        v_info_3343_ = crate::leanh::lean_ctor_get(v_x_3314_, 0);
                        crate::leanh::lean_inc(v_info_3343_);
                        v_rawVal_3344_ = crate::leanh::lean_ctor_get(v_x_3314_, 1);
                        crate::leanh::lean_inc_ref(v_rawVal_3344_);
                        v_val_3345_ = crate::leanh::lean_ctor_get(v_x_3314_, 2);
                        crate::leanh::lean_inc(v_val_3345_);
                        v_preresolved_3346_ = crate::leanh::lean_ctor_get(v_x_3314_, 3);
                        crate::leanh::lean_inc(v_preresolved_3346_);
                        crate::leanh::lean_dec_ref_known(v_x_3314_, 4);
                        v___x_3351_ =
                            l_Lean_instBEqSourceInfo__lean_beq(v_info_3339_, v_info_3343_);
                        if v___x_3351_ == 0 {
                            crate::leanh::lean_dec_ref(v_rawVal_3344_);
                            crate::leanh::lean_dec_ref(v_rawVal_3340_);
                            v___y_3348_ = v___x_3351_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3352_ = l_Substring_Raw_beq(v_rawVal_3340_, v_rawVal_3344_);
                            v___y_3348_ = v___x_3352_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_3313_, 4);
                        crate::leanh::lean_dec(v_x_3314_);
                        v___x_3353_ = 0;
                        return v___x_3353_;
                    }
                }
            },
            1 => {
                if v___y_3324_ == 0 {
                    crate::leanh::lean_dec_ref(v_args_3322_);
                    crate::leanh::lean_dec_ref(v_args_3319_);
                    return v___y_3324_;
                } else {
                    v___x_3325_ = lean_array_get_size(v_args_3319_);
                    v___x_3326_ = lean_array_get_size(v_args_3322_);
                    v___x_3327_ = lean_nat_dec_eq(v___x_3325_, v___x_3326_);
                    if v___x_3327_ == 0 {
                        crate::leanh::lean_dec_ref(v_args_3322_);
                        crate::leanh::lean_dec_ref(v_args_3319_);
                        return v___x_3327_;
                    } else {
                        v___x_3328_ =
                            l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(
                                v_args_3319_,
                                v_args_3322_,
                                v___x_3325_,
                            );
                        crate::leanh::lean_dec_ref(v_args_3322_);
                        crate::leanh::lean_dec_ref(v_args_3319_);
                        return v___x_3328_;
                    }
                }
            }
            2 => {
                if v___y_3348_ == 0 {
                    crate::leanh::lean_dec(v_preresolved_3346_);
                    crate::leanh::lean_dec(v_val_3345_);
                    crate::leanh::lean_dec(v_preresolved_3342_);
                    crate::leanh::lean_dec(v_val_3341_);
                    return v___y_3348_;
                } else {
                    v___x_3349_ = lean_name_eq(v_val_3341_, v_val_3345_);
                    crate::leanh::lean_dec(v_val_3345_);
                    crate::leanh::lean_dec(v_val_3341_);
                    if v___x_3349_ == 0 {
                        crate::leanh::lean_dec(v_preresolved_3346_);
                        crate::leanh::lean_dec(v_preresolved_3342_);
                        return v___x_3349_;
                    } else {
                        v___x_3350_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(
                            v_preresolved_3342_,
                            v_preresolved_3346_,
                        );
                        crate::leanh::lean_dec(v_preresolved_3346_);
                        crate::leanh::lean_dec(v_preresolved_3342_);
                        return v___x_3350_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(
    mut v_xs_3354_: *mut crate::leanh::LeanObject,
    mut v_ys_3355_: *mut crate::leanh::LeanObject,
    mut v_x_3356_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3358_: u8 = 0;
    let mut v_one_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3357_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_3358_ = lean_nat_dec_eq(v_x_3356_, v_zero_3357_);
                if v_isZero_3358_ == 1 {
                    crate::leanh::lean_dec(v_x_3356_);
                    return v_isZero_3358_;
                } else {
                    v_one_3359_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_3360_ = lean_nat_sub(v_x_3356_, v_one_3359_);
                    crate::leanh::lean_dec(v_x_3356_);
                    v___x_3361_ = lean_array_fget_borrowed(v_xs_3354_, v_n_3360_);
                    v___x_3362_ = lean_array_fget_borrowed(v_ys_3355_, v_n_3360_);
                    crate::leanh::lean_inc(v___x_3362_);
                    crate::leanh::lean_inc(v___x_3361_);
                    v___x_3363_ = l_Lean_Syntax_eqWithInfo(v___x_3361_, v___x_3362_);
                    if v___x_3363_ == 0 {
                        crate::leanh::lean_dec(v_n_3360_);
                        return v___x_3363_;
                    } else {
                        v_x_3356_ = v_n_3360_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg___boxed(
    mut v_xs_3365_: *mut crate::leanh::LeanObject,
    mut v_ys_3366_: *mut crate::leanh::LeanObject,
    mut v_x_3367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3368_: u8 = 0;
    let mut v_r_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3368_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(
        v_xs_3365_, v_ys_3366_, v_x_3367_,
    );
    crate::leanh::lean_dec_ref(v_ys_3366_);
    crate::leanh::lean_dec_ref(v_xs_3365_);
    v_r_3369_ = crate::leanh::lean_box((v_res_3368_) as usize);
    return v_r_3369_;
}
pub unsafe fn l_Lean_Syntax_eqWithInfo___boxed(
    mut v_x_3370_: *mut crate::leanh::LeanObject,
    mut v_x_3371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3372_: u8 = 0;
    let mut v_r_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3372_ = l_Lean_Syntax_eqWithInfo(v_x_3370_, v_x_3371_);
    v_r_3373_ = crate::leanh::lean_box((v_res_3372_) as usize);
    return v_r_3373_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0(
    mut v_xs_3374_: *mut crate::leanh::LeanObject,
    mut v_ys_3375_: *mut crate::leanh::LeanObject,
    mut v_hsz_3376_: *mut crate::leanh::LeanObject,
    mut v_x_3377_: *mut crate::leanh::LeanObject,
    mut v_x_3378_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3379_: u8 = 0;
    v___x_3379_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(
        v_xs_3374_, v_ys_3375_, v_x_3377_,
    );
    return v___x_3379_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___boxed(
    mut v_xs_3380_: *mut crate::leanh::LeanObject,
    mut v_ys_3381_: *mut crate::leanh::LeanObject,
    mut v_hsz_3382_: *mut crate::leanh::LeanObject,
    mut v_x_3383_: *mut crate::leanh::LeanObject,
    mut v_x_3384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3385_: u8 = 0;
    let mut v_r_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3385_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0(
        v_xs_3380_,
        v_ys_3381_,
        v_hsz_3382_,
        v_x_3383_,
        v_x_3384_,
    );
    crate::leanh::lean_dec_ref(v_ys_3381_);
    crate::leanh::lean_dec_ref(v_xs_3380_);
    v_r_3386_ = crate::leanh::lean_box((v_res_3385_) as usize);
    return v_r_3386_;
}
pub unsafe fn l_Lean_Syntax_eqWithInfoAndTraceReuse(
    mut v_opts_3387_: *mut crate::leanh::LeanObject,
    mut v_stx1_3388_: *mut crate::leanh::LeanObject,
    mut v_stx2_3389_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3390_: u8 = 0;
    let mut v___x_3391_: u8 = 0;
    let mut v_map_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3396_: u8 = 0;
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: u8 = 0;
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3414_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_stx2_3389_);
                crate::leanh::lean_inc(v_stx1_3388_);
                v___x_3390_ = l_Lean_Syntax_eqWithInfo(v_stx1_3388_, v_stx2_3389_);
                v___x_3391_ = 1;
                if v___x_3390_ == 0 {
                    v_map_3392_ = crate::leanh::lean_ctor_get(v_opts_3387_, 0);
                    v___x_3393_ = crate::leanh::lean_box((v___x_3390_) as usize);
                    v___f_3394_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_3394_, 0, v___x_3393_);
                    v___x_3411_ = l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5;
                    v___x_3412_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3392_, v___x_3411_);
                    if crate::leanh::lean_obj_tag(v___x_3412_) == 0 {
                        v___y_3396_ = v___x_3390_;
                        state = 1;
                        continue;
                    } else {
                        v_val_3413_ = crate::leanh::lean_ctor_get(v___x_3412_, 0);
                        crate::leanh::lean_inc(v_val_3413_);
                        crate::leanh::lean_dec_ref_known(v___x_3412_, 1);
                        if crate::leanh::lean_obj_tag(v_val_3413_) == 1 {
                            v_v_3414_ = crate::leanh::lean_ctor_get_uint8(v_val_3413_, 0 as u32);
                            crate::leanh::lean_dec_ref_known(v_val_3413_, 0);
                            v___y_3396_ = v_v_3414_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_val_3413_);
                            v___y_3396_ = v___x_3390_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_stx2_3389_);
                    crate::leanh::lean_dec(v_stx1_3388_);
                    return v___x_3391_;
                }
            }
            1 => {
                if v___y_3396_ == 0 {
                    crate::leanh::lean_dec_ref(v___f_3394_);
                    crate::leanh::lean_dec(v_stx2_3389_);
                    crate::leanh::lean_dec(v_stx1_3388_);
                    return v___x_3390_;
                } else {
                    v___x_3397_ = l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0;
                    v___x_3398_ = crate::leanh::lean_box(0);
                    v___x_3399_ = l_Lean_Syntax_formatStx(v_stx1_3388_, v___x_3398_, v___x_3391_);
                    v___x_3400_ = l_Std_Format_defWidth;
                    v___x_3401_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3402_ =
                        l_Std_Format_pretty(v___x_3399_, v___x_3400_, v___x_3401_, v___x_3401_);
                    v___x_3403_ = lean_string_append(v___x_3397_, v___x_3402_);
                    crate::leanh::lean_dec_ref(v___x_3402_);
                    v___x_3404_ = l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1;
                    v___x_3405_ = lean_string_append(v___x_3403_, v___x_3404_);
                    v___x_3406_ = l_Lean_Syntax_formatStx(v_stx2_3389_, v___x_3398_, v___x_3391_);
                    v___x_3407_ =
                        l_Std_Format_pretty(v___x_3406_, v___x_3400_, v___x_3401_, v___x_3401_);
                    v___x_3408_ = lean_string_append(v___x_3405_, v___x_3407_);
                    crate::leanh::lean_dec_ref(v___x_3407_);
                    v___x_3409_ = lean_dbg_trace(v___x_3408_, v___f_3394_);
                    v___x_3410_ = (crate::leanh::lean_unbox(v___x_3409_) as u8);
                    crate::leanh::lean_dec(v___x_3409_);
                    return v___x_3410_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_eqWithInfoAndTraceReuse___boxed(
    mut v_opts_3415_: *mut crate::leanh::LeanObject,
    mut v_stx1_3416_: *mut crate::leanh::LeanObject,
    mut v_stx2_3417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3418_: u8 = 0;
    let mut v_r_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3418_ = l_Lean_Syntax_eqWithInfoAndTraceReuse(v_opts_3415_, v_stx1_3416_, v_stx2_3417_);
    crate::leanh::lean_dec_ref(v_opts_3415_);
    v_r_3419_ = crate::leanh::lean_box((v_res_3418_) as usize);
    return v_r_3419_;
}
pub unsafe fn l_Lean_Syntax_getAtomVal(
    mut v_x_3421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3421_) == 2 {
        let mut v_val_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3422_ = crate::leanh::lean_ctor_get(v_x_3421_, 1);
        crate::leanh::lean_inc_ref(v_val_3422_);
        return v_val_3422_;
    } else {
        let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3423_ = l_Lean_Syntax_getAtomVal___closed__0;
        return v___x_3423_;
    }
}
pub unsafe fn l_Lean_Syntax_getAtomVal___boxed(
    mut v_x_3424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3425_ = l_Lean_Syntax_getAtomVal(v_x_3424_);
    crate::leanh::lean_dec(v_x_3424_);
    return v_res_3425_;
}
pub unsafe fn l_Lean_Syntax_setAtomVal(
    mut v_x_3426_: *mut crate::leanh::LeanObject,
    mut v_x_3427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_info_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3431_: u8 = 0;
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3435_: u8 = 0;
    let mut v_unused_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3426_) == 2 {
                    v_info_3428_ = crate::leanh::lean_ctor_get(v_x_3426_, 0);
                    v_isSharedCheck_3435_ = (!crate::leanh::lean_is_exclusive(v_x_3426_)) as u8;
                    if v_isSharedCheck_3435_ == 0 {
                        v_unused_3436_ = crate::leanh::lean_ctor_get(v_x_3426_, 1);
                        crate::leanh::lean_dec(v_unused_3436_);
                        v___x_3430_ = v_x_3426_;
                        v_isShared_3431_ = v_isSharedCheck_3435_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_info_3428_);
                        crate::leanh::lean_dec(v_x_3426_);
                        v___x_3430_ = crate::leanh::lean_box(0);
                        v_isShared_3431_ = v_isSharedCheck_3435_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_3427_);
                    return v_x_3426_;
                }
            }
            1 => {
                if v_isShared_3431_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3430_, 1, v_x_3427_);
                    v___x_3433_ = v___x_3430_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3434_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_info_3428_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3434_, 1, v_x_3427_);
                    v___x_3433_ = v_reuseFailAlloc_3434_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3433_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_ifNode___redArg(
    mut v_stx_3437_: *mut crate::leanh::LeanObject,
    mut v_hyes_3438_: *mut crate::leanh::LeanObject,
    mut v_hno_3439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_stx_3437_) == 1 {
        let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_hno_3439_);
        v___x_3440_ = crate::leanh::lean_apply_1(v_hyes_3438_, v_stx_3437_);
        return v___x_3440_;
    } else {
        let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_hyes_3438_);
        crate::leanh::lean_dec(v_stx_3437_);
        v___x_3441_ = crate::leanh::lean_box(0);
        v___x_3442_ = crate::leanh::lean_apply_1(v_hno_3439_, v___x_3441_);
        return v___x_3442_;
    }
}
pub unsafe fn l_Lean_Syntax_ifNode(
    mut v_00_u03b2_3443_: *mut crate::leanh::LeanObject,
    mut v_stx_3444_: *mut crate::leanh::LeanObject,
    mut v_hyes_3445_: *mut crate::leanh::LeanObject,
    mut v_hno_3446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_stx_3444_) == 1 {
        let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_hno_3446_);
        v___x_3447_ = crate::leanh::lean_apply_1(v_hyes_3445_, v_stx_3444_);
        return v___x_3447_;
    } else {
        let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_hyes_3445_);
        crate::leanh::lean_dec(v_stx_3444_);
        v___x_3448_ = crate::leanh::lean_box(0);
        v___x_3449_ = crate::leanh::lean_apply_1(v_hno_3446_, v___x_3448_);
        return v___x_3449_;
    }
}
pub unsafe fn l_Lean_Syntax_ifNodeKind___redArg(
    mut v_stx_3450_: *mut crate::leanh::LeanObject,
    mut v_kind_3451_: *mut crate::leanh::LeanObject,
    mut v_hyes_3452_: *mut crate::leanh::LeanObject,
    mut v_hno_3453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_stx_3450_) == 1 {
        let mut v_kind_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3455_: u8 = 0;
        v_kind_3454_ = crate::leanh::lean_ctor_get(v_stx_3450_, 1);
        v___x_3455_ = lean_name_eq(v_kind_3454_, v_kind_3451_);
        if v___x_3455_ == 0 {
            let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v_stx_3450_, 3);
            crate::leanh::lean_dec(v_hyes_3452_);
            v___x_3456_ = crate::leanh::lean_box(0);
            v___x_3457_ = crate::leanh::lean_apply_1(v_hno_3453_, v___x_3456_);
            return v___x_3457_;
        } else {
            let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_hno_3453_);
            v___x_3458_ = crate::leanh::lean_apply_1(v_hyes_3452_, v_stx_3450_);
            return v___x_3458_;
        }
    } else {
        let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_hyes_3452_);
        crate::leanh::lean_dec(v_stx_3450_);
        v___x_3459_ = crate::leanh::lean_box(0);
        v___x_3460_ = crate::leanh::lean_apply_1(v_hno_3453_, v___x_3459_);
        return v___x_3460_;
    }
}
pub unsafe fn l_Lean_Syntax_ifNodeKind___redArg___boxed(
    mut v_stx_3461_: *mut crate::leanh::LeanObject,
    mut v_kind_3462_: *mut crate::leanh::LeanObject,
    mut v_hyes_3463_: *mut crate::leanh::LeanObject,
    mut v_hno_3464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3465_ =
        l_Lean_Syntax_ifNodeKind___redArg(v_stx_3461_, v_kind_3462_, v_hyes_3463_, v_hno_3464_);
    crate::leanh::lean_dec(v_kind_3462_);
    return v_res_3465_;
}
pub unsafe fn l_Lean_Syntax_ifNodeKind(
    mut v_00_u03b2_3466_: *mut crate::leanh::LeanObject,
    mut v_stx_3467_: *mut crate::leanh::LeanObject,
    mut v_kind_3468_: *mut crate::leanh::LeanObject,
    mut v_hyes_3469_: *mut crate::leanh::LeanObject,
    mut v_hno_3470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_stx_3467_) == 1 {
        let mut v_kind_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3472_: u8 = 0;
        v_kind_3471_ = crate::leanh::lean_ctor_get(v_stx_3467_, 1);
        v___x_3472_ = lean_name_eq(v_kind_3471_, v_kind_3468_);
        if v___x_3472_ == 0 {
            let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v_stx_3467_, 3);
            crate::leanh::lean_dec(v_hyes_3469_);
            v___x_3473_ = crate::leanh::lean_box(0);
            v___x_3474_ = crate::leanh::lean_apply_1(v_hno_3470_, v___x_3473_);
            return v___x_3474_;
        } else {
            let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_hno_3470_);
            v___x_3475_ = crate::leanh::lean_apply_1(v_hyes_3469_, v_stx_3467_);
            return v___x_3475_;
        }
    } else {
        let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_hyes_3469_);
        crate::leanh::lean_dec(v_stx_3467_);
        v___x_3476_ = crate::leanh::lean_box(0);
        v___x_3477_ = crate::leanh::lean_apply_1(v_hno_3470_, v___x_3476_);
        return v___x_3477_;
    }
}
pub unsafe fn l_Lean_Syntax_ifNodeKind___boxed(
    mut v_00_u03b2_3478_: *mut crate::leanh::LeanObject,
    mut v_stx_3479_: *mut crate::leanh::LeanObject,
    mut v_kind_3480_: *mut crate::leanh::LeanObject,
    mut v_hyes_3481_: *mut crate::leanh::LeanObject,
    mut v_hno_3482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3483_ = l_Lean_Syntax_ifNodeKind(
        v_00_u03b2_3478_,
        v_stx_3479_,
        v_kind_3480_,
        v_hyes_3481_,
        v_hno_3482_,
    );
    crate::leanh::lean_dec(v_kind_3480_);
    return v_res_3483_;
}
pub unsafe fn l_Lean_Syntax_asNode(
    mut v_x_3493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3493_) == 1 {
        crate::leanh::lean_inc_ref(v_x_3493_);
        return v_x_3493_;
    } else {
        let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3494_ = l_Lean_Syntax_asNode___closed__3;
        return v___x_3494_;
    }
}
pub unsafe fn l_Lean_Syntax_asNode___boxed(
    mut v_x_3495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3496_ = l_Lean_Syntax_asNode(v_x_3495_);
    crate::leanh::lean_dec(v_x_3495_);
    return v_res_3496_;
}
pub unsafe fn l_Lean_Syntax_getIdAt(
    mut v_stx_3497_: *mut crate::leanh::LeanObject,
    mut v_i_3498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3499_ = l_Lean_Syntax_getArg(v_stx_3497_, v_i_3498_);
    v___x_3500_ = l_Lean_Syntax_getId(v___x_3499_);
    crate::leanh::lean_dec(v___x_3499_);
    return v___x_3500_;
}
pub unsafe fn l_Lean_Syntax_getIdAt___boxed(
    mut v_stx_3501_: *mut crate::leanh::LeanObject,
    mut v_i_3502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3503_ = l_Lean_Syntax_getIdAt(v_stx_3501_, v_i_3502_);
    crate::leanh::lean_dec(v_i_3502_);
    crate::leanh::lean_dec(v_stx_3501_);
    return v_res_3503_;
}
pub unsafe fn l_Lean_Syntax_hasIdent(
    mut v_id_3504_: *mut crate::leanh::LeanObject,
    mut v_x_3505_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_3505_) {
        3 => {
            let mut v_val_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3507_: u8 = 0;
            v_val_3506_ = crate::leanh::lean_ctor_get(v_x_3505_, 2);
            v___x_3507_ = lean_name_eq(v_id_3504_, v_val_3506_);
            return v___x_3507_;
        }
        1 => {
            let mut v_args_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3511_: u8 = 0;
            v_args_3508_ = crate::leanh::lean_ctor_get(v_x_3505_, 2);
            v___x_3509_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_3510_ = lean_array_get_size(v_args_3508_);
            v___x_3511_ = lean_nat_dec_lt(v___x_3509_, v___x_3510_);
            if v___x_3511_ == 0 {
                return v___x_3511_;
            } else {
                if v___x_3511_ == 0 {
                    return v___x_3511_;
                } else {
                    let mut v___x_3512_: usize = 0;
                    let mut v___x_3513_: usize = 0;
                    let mut v___x_3514_: u8 = 0;
                    v___x_3512_ = 0usize;
                    v___x_3513_ = lean_usize_of_nat(v___x_3510_);
                    v___x_3514_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(v_id_3504_, v_args_3508_, v___x_3512_, v___x_3513_);
                    return v___x_3514_;
                }
            }
        }
        _ => {
            let mut v___x_3515_: u8 = 0;
            v___x_3515_ = 0;
            return v___x_3515_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(
    mut v_id_3516_: *mut crate::leanh::LeanObject,
    mut v_as_3517_: *mut crate::leanh::LeanObject,
    mut v_i_3518_: usize,
    mut v_stop_3519_: usize,
) -> u8 {
    let mut v___x_3520_: u8 = 0;
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: u8 = 0;
    let mut v___x_3523_: usize = 0;
    let mut v___x_3524_: usize = 0;
    let mut v___x_3526_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3520_ = lean_usize_dec_eq(v_i_3518_, v_stop_3519_);
                if v___x_3520_ == 0 {
                    v___x_3521_ = lean_array_uget_borrowed(v_as_3517_, v_i_3518_);
                    v___x_3522_ = l_Lean_Syntax_hasIdent(v_id_3516_, v___x_3521_);
                    if v___x_3522_ == 0 {
                        v___x_3523_ = 1usize;
                        v___x_3524_ = lean_usize_add(v_i_3518_, v___x_3523_);
                        v_i_3518_ = v___x_3524_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3522_;
                    }
                } else {
                    v___x_3526_ = 0;
                    return v___x_3526_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0___boxed(
    mut v_id_3527_: *mut crate::leanh::LeanObject,
    mut v_as_3528_: *mut crate::leanh::LeanObject,
    mut v_i_3529_: *mut crate::leanh::LeanObject,
    mut v_stop_3530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3531_: usize = 0;
    let mut v_stop_boxed_3532_: usize = 0;
    let mut v_res_3533_: u8 = 0;
    let mut v_r_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3531_ = crate::leanh::lean_unbox_usize(v_i_3529_);
    crate::leanh::lean_dec(v_i_3529_);
    v_stop_boxed_3532_ = crate::leanh::lean_unbox_usize(v_stop_3530_);
    crate::leanh::lean_dec(v_stop_3530_);
    v_res_3533_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(v_id_3527_, v_as_3528_, v_i_boxed_3531_, v_stop_boxed_3532_);
    crate::leanh::lean_dec_ref(v_as_3528_);
    crate::leanh::lean_dec(v_id_3527_);
    v_r_3534_ = crate::leanh::lean_box((v_res_3533_) as usize);
    return v_r_3534_;
}
pub unsafe fn l_Lean_Syntax_hasIdent___boxed(
    mut v_id_3535_: *mut crate::leanh::LeanObject,
    mut v_x_3536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3537_: u8 = 0;
    let mut v_r_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3537_ = l_Lean_Syntax_hasIdent(v_id_3535_, v_x_3536_);
    crate::leanh::lean_dec(v_x_3536_);
    crate::leanh::lean_dec(v_id_3535_);
    v_r_3538_ = crate::leanh::lean_box((v_res_3537_) as usize);
    return v_r_3538_;
}
pub unsafe fn l_Lean_Syntax_modifyArgs(
    mut v_stx_3539_: *mut crate::leanh::LeanObject,
    mut v_fn_3540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_info_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3546_: u8 = 0;
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3551_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_stx_3539_) == 1 {
                    v_info_3541_ = crate::leanh::lean_ctor_get(v_stx_3539_, 0);
                    v_kind_3542_ = crate::leanh::lean_ctor_get(v_stx_3539_, 1);
                    v_args_3543_ = crate::leanh::lean_ctor_get(v_stx_3539_, 2);
                    v_isSharedCheck_3551_ = (!crate::leanh::lean_is_exclusive(v_stx_3539_)) as u8;
                    if v_isSharedCheck_3551_ == 0 {
                        v___x_3545_ = v_stx_3539_;
                        v_isShared_3546_ = v_isSharedCheck_3551_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_args_3543_);
                        crate::leanh::lean_inc(v_kind_3542_);
                        crate::leanh::lean_inc(v_info_3541_);
                        crate::leanh::lean_dec(v_stx_3539_);
                        v___x_3545_ = crate::leanh::lean_box(0);
                        v_isShared_3546_ = v_isSharedCheck_3551_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_fn_3540_);
                    return v_stx_3539_;
                }
            }
            1 => {
                v___x_3547_ = crate::leanh::lean_apply_1(v_fn_3540_, v_args_3543_);
                if v_isShared_3546_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3545_, 2, v___x_3547_);
                    v___x_3549_ = v___x_3545_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3550_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_info_3541_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3550_, 1, v_kind_3542_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3550_, 2, v___x_3547_);
                    v___x_3549_ = v_reuseFailAlloc_3550_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3549_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_modifyArg(
    mut v_stx_3552_: *mut crate::leanh::LeanObject,
    mut v_i_3553_: *mut crate::leanh::LeanObject,
    mut v_fn_3554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_info_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: u8 = 0;
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3562_: u8 = 0;
    let mut v_v_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3571_: u8 = 0;
    let mut v_unused_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_stx_3552_) == 1 {
                    v_info_3555_ = crate::leanh::lean_ctor_get(v_stx_3552_, 0);
                    v_kind_3556_ = crate::leanh::lean_ctor_get(v_stx_3552_, 1);
                    v_args_3557_ = crate::leanh::lean_ctor_get(v_stx_3552_, 2);
                    v___x_3558_ = lean_array_get_size(v_args_3557_);
                    v___x_3559_ = lean_nat_dec_lt(v_i_3553_, v___x_3558_);
                    if v___x_3559_ == 0 {
                        crate::leanh::lean_dec_ref(v_fn_3554_);
                        return v_stx_3552_;
                    } else {
                        crate::leanh::lean_inc_ref(v_args_3557_);
                        crate::leanh::lean_inc(v_kind_3556_);
                        crate::leanh::lean_inc(v_info_3555_);
                        v_isSharedCheck_3571_ =
                            (!crate::leanh::lean_is_exclusive(v_stx_3552_)) as u8;
                        if v_isSharedCheck_3571_ == 0 {
                            v_unused_3572_ = crate::leanh::lean_ctor_get(v_stx_3552_, 2);
                            crate::leanh::lean_dec(v_unused_3572_);
                            v_unused_3573_ = crate::leanh::lean_ctor_get(v_stx_3552_, 1);
                            crate::leanh::lean_dec(v_unused_3573_);
                            v_unused_3574_ = crate::leanh::lean_ctor_get(v_stx_3552_, 0);
                            crate::leanh::lean_dec(v_unused_3574_);
                            v___x_3561_ = v_stx_3552_;
                            v_isShared_3562_ = v_isSharedCheck_3571_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_stx_3552_);
                            v___x_3561_ = crate::leanh::lean_box(0);
                            v_isShared_3562_ = v_isSharedCheck_3571_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_fn_3554_);
                    return v_stx_3552_;
                }
            }
            1 => {
                v_v_3563_ = lean_array_fget(v_args_3557_, v_i_3553_);
                v___x_3564_ = crate::leanh::lean_box(0);
                v_xs_x27_3565_ = lean_array_fset(v_args_3557_, v_i_3553_, v___x_3564_);
                v___x_3566_ = crate::leanh::lean_apply_1(v_fn_3554_, v_v_3563_);
                v___x_3567_ = lean_array_fset(v_xs_x27_3565_, v_i_3553_, v___x_3566_);
                if v_isShared_3562_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3561_, 2, v___x_3567_);
                    v___x_3569_ = v___x_3561_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3570_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_info_3555_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3570_, 1, v_kind_3556_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3570_, 2, v___x_3567_);
                    v___x_3569_ = v_reuseFailAlloc_3570_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3569_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_modifyArg___boxed(
    mut v_stx_3575_: *mut crate::leanh::LeanObject,
    mut v_i_3576_: *mut crate::leanh::LeanObject,
    mut v_fn_3577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3578_ = l_Lean_Syntax_modifyArg(v_stx_3575_, v_i_3576_, v_fn_3577_);
    crate::leanh::lean_dec(v_i_3576_);
    return v_res_3578_;
}
pub unsafe fn l_Lean_Syntax_replaceM___redArg___lam__0(
    mut v_info_3579_: *mut crate::leanh::LeanObject,
    mut v_kind_3580_: *mut crate::leanh::LeanObject,
    mut v_toPure_3581_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3583_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3583_, 0, v_info_3579_);
    crate::leanh::lean_ctor_set(v___x_3583_, 1, v_kind_3580_);
    crate::leanh::lean_ctor_set(v___x_3583_, 2, v_____do__lift_3582_);
    v___x_3584_ =
        crate::leanh::lean_apply_2(v_toPure_3581_, crate::leanh::lean_box(0), v___x_3583_);
    return v___x_3584_;
}
pub unsafe fn l_Lean_Syntax_replaceM___redArg___lam__2(
    mut v_toPure_3585_: *mut crate::leanh::LeanObject,
    mut v_x_3586_: *mut crate::leanh::LeanObject,
    mut v_o_3587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_o_3587_) == 0 {
        let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3588_ =
            crate::leanh::lean_apply_2(v_toPure_3585_, crate::leanh::lean_box(0), v_x_3586_);
        return v___x_3588_;
    } else {
        let mut v_val_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_3586_);
        v_val_3589_ = crate::leanh::lean_ctor_get(v_o_3587_, 0);
        crate::leanh::lean_inc(v_val_3589_);
        crate::leanh::lean_dec_ref_known(v_o_3587_, 1);
        v___x_3590_ =
            crate::leanh::lean_apply_2(v_toPure_3585_, crate::leanh::lean_box(0), v_val_3589_);
        return v___x_3590_;
    }
}
pub unsafe fn l_Lean_Syntax_replaceM___redArg(
    mut v_inst_3591_: *mut crate::leanh::LeanObject,
    mut v_fn_3592_: *mut crate::leanh::LeanObject,
    mut v_x_3593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3593_) == 1 {
        let mut v_toApplicative_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_info_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_kind_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_args_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_3594_ = crate::leanh::lean_ctor_get(v_inst_3591_, 0);
        v_toBind_3595_ = crate::leanh::lean_ctor_get(v_inst_3591_, 1);
        crate::leanh::lean_inc_n(v_toBind_3595_, 2);
        v_toPure_3596_ = crate::leanh::lean_ctor_get(v_toApplicative_3594_, 1);
        crate::leanh::lean_inc_n(v_toPure_3596_, 2);
        v_info_3597_ = crate::leanh::lean_ctor_get(v_x_3593_, 0);
        v_kind_3598_ = crate::leanh::lean_ctor_get(v_x_3593_, 1);
        v_args_3599_ = crate::leanh::lean_ctor_get(v_x_3593_, 2);
        crate::leanh::lean_inc(v_kind_3598_);
        crate::leanh::lean_inc(v_info_3597_);
        v___f_3600_ = crate::leanh::lean_alloc_closure(
            l_Lean_Syntax_replaceM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_3600_, 0, v_info_3597_);
        crate::leanh::lean_closure_set(v___f_3600_, 1, v_kind_3598_);
        crate::leanh::lean_closure_set(v___f_3600_, 2, v_toPure_3596_);
        crate::leanh::lean_inc_ref(v_args_3599_);
        crate::leanh::lean_inc(v_fn_3592_);
        v___f_3601_ = crate::leanh::lean_alloc_closure(
            l_Lean_Syntax_replaceM___redArg___lam__1 as *mut core::ffi::c_void,
            7,
            6,
        );
        crate::leanh::lean_closure_set(v___f_3601_, 0, v_inst_3591_);
        crate::leanh::lean_closure_set(v___f_3601_, 1, v_fn_3592_);
        crate::leanh::lean_closure_set(v___f_3601_, 2, v_args_3599_);
        crate::leanh::lean_closure_set(v___f_3601_, 3, v_toBind_3595_);
        crate::leanh::lean_closure_set(v___f_3601_, 4, v___f_3600_);
        crate::leanh::lean_closure_set(v___f_3601_, 5, v_toPure_3596_);
        v___x_3602_ = crate::leanh::lean_apply_1(v_fn_3592_, v_x_3593_);
        v___x_3603_ = crate::leanh::lean_apply_4(
            v_toBind_3595_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_3602_,
            v___f_3601_,
        );
        return v___x_3603_;
    } else {
        let mut v_toApplicative_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_3604_ = crate::leanh::lean_ctor_get(v_inst_3591_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_3604_);
        v_toBind_3605_ = crate::leanh::lean_ctor_get(v_inst_3591_, 1);
        crate::leanh::lean_inc(v_toBind_3605_);
        crate::leanh::lean_dec_ref(v_inst_3591_);
        v_toPure_3606_ = crate::leanh::lean_ctor_get(v_toApplicative_3604_, 1);
        crate::leanh::lean_inc(v_toPure_3606_);
        crate::leanh::lean_dec_ref(v_toApplicative_3604_);
        crate::leanh::lean_inc(v_x_3593_);
        v___f_3607_ = crate::leanh::lean_alloc_closure(
            l_Lean_Syntax_replaceM___redArg___lam__2 as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_3607_, 0, v_toPure_3606_);
        crate::leanh::lean_closure_set(v___f_3607_, 1, v_x_3593_);
        v___x_3608_ = crate::leanh::lean_apply_1(v_fn_3592_, v_x_3593_);
        v___x_3609_ = crate::leanh::lean_apply_4(
            v_toBind_3605_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_3608_,
            v___f_3607_,
        );
        return v___x_3609_;
    }
}
pub unsafe fn l_Lean_Syntax_replaceM___redArg___lam__1(
    mut v_inst_3610_: *mut crate::leanh::LeanObject,
    mut v_fn_3611_: *mut crate::leanh::LeanObject,
    mut v_args_3612_: *mut crate::leanh::LeanObject,
    mut v_toBind_3613_: *mut crate::leanh::LeanObject,
    mut v___f_3614_: *mut crate::leanh::LeanObject,
    mut v_toPure_3615_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_3616_) == 0 {
        let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3618_: usize = 0;
        let mut v___x_3619_: usize = 0;
        let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_3615_);
        crate::leanh::lean_inc_ref(v_inst_3610_);
        v___x_3617_ = crate::leanh::lean_alloc_closure(
            l_Lean_Syntax_replaceM___redArg as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___x_3617_, 0, v_inst_3610_);
        crate::leanh::lean_closure_set(v___x_3617_, 1, v_fn_3611_);
        v_sz_3618_ = lean_array_size(v_args_3612_);
        v___x_3619_ = 0usize;
        v___x_3620_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_inst_3610_,
            v___x_3617_,
            v_sz_3618_,
            v___x_3619_,
            v_args_3612_,
        );
        v___x_3621_ = crate::leanh::lean_apply_4(
            v_toBind_3613_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_3620_,
            v___f_3614_,
        );
        return v___x_3621_;
    } else {
        let mut v_val_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_3614_);
        crate::leanh::lean_dec(v_toBind_3613_);
        crate::leanh::lean_dec_ref(v_args_3612_);
        crate::leanh::lean_dec(v_fn_3611_);
        crate::leanh::lean_dec_ref(v_inst_3610_);
        v_val_3622_ = crate::leanh::lean_ctor_get(v_____do__lift_3616_, 0);
        crate::leanh::lean_inc(v_val_3622_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_3616_, 1);
        v___x_3623_ =
            crate::leanh::lean_apply_2(v_toPure_3615_, crate::leanh::lean_box(0), v_val_3622_);
        return v___x_3623_;
    }
}
pub unsafe fn l_Lean_Syntax_replaceM(
    mut v_m_3624_: *mut crate::leanh::LeanObject,
    mut v_inst_3625_: *mut crate::leanh::LeanObject,
    mut v_fn_3626_: *mut crate::leanh::LeanObject,
    mut v_x_3627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3628_ = l_Lean_Syntax_replaceM___redArg(v_inst_3625_, v_fn_3626_, v_x_3627_);
    return v___x_3628_;
}
pub unsafe fn l_Lean_Syntax_rewriteBottomUpM___redArg___lam__0(
    mut v_info_3629_: *mut crate::leanh::LeanObject,
    mut v_kind_3630_: *mut crate::leanh::LeanObject,
    mut v_fn_3631_: *mut crate::leanh::LeanObject,
    mut v_args_3632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3633_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3633_, 0, v_info_3629_);
    crate::leanh::lean_ctor_set(v___x_3633_, 1, v_kind_3630_);
    crate::leanh::lean_ctor_set(v___x_3633_, 2, v_args_3632_);
    v___x_3634_ = crate::leanh::lean_apply_1(v_fn_3631_, v___x_3633_);
    return v___x_3634_;
}
pub unsafe fn l_Lean_Syntax_rewriteBottomUpM___redArg(
    mut v_inst_3635_: *mut crate::leanh::LeanObject,
    mut v_fn_3636_: *mut crate::leanh::LeanObject,
    mut v_x_3637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3637_) == 1 {
        let mut v_toBind_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_info_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_kind_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_args_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3644_: usize = 0;
        let mut v___x_3645_: usize = 0;
        let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_3638_ = crate::leanh::lean_ctor_get(v_inst_3635_, 1);
        crate::leanh::lean_inc(v_toBind_3638_);
        v_info_3639_ = crate::leanh::lean_ctor_get(v_x_3637_, 0);
        crate::leanh::lean_inc(v_info_3639_);
        v_kind_3640_ = crate::leanh::lean_ctor_get(v_x_3637_, 1);
        crate::leanh::lean_inc(v_kind_3640_);
        v_args_3641_ = crate::leanh::lean_ctor_get(v_x_3637_, 2);
        crate::leanh::lean_inc_ref(v_args_3641_);
        crate::leanh::lean_dec_ref_known(v_x_3637_, 3);
        crate::leanh::lean_inc(v_fn_3636_);
        v___f_3642_ = crate::leanh::lean_alloc_closure(
            l_Lean_Syntax_rewriteBottomUpM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_3642_, 0, v_info_3639_);
        crate::leanh::lean_closure_set(v___f_3642_, 1, v_kind_3640_);
        crate::leanh::lean_closure_set(v___f_3642_, 2, v_fn_3636_);
        crate::leanh::lean_inc_ref(v_inst_3635_);
        v___x_3643_ = crate::leanh::lean_alloc_closure(
            l_Lean_Syntax_rewriteBottomUpM___redArg as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___x_3643_, 0, v_inst_3635_);
        crate::leanh::lean_closure_set(v___x_3643_, 1, v_fn_3636_);
        v_sz_3644_ = lean_array_size(v_args_3641_);
        v___x_3645_ = 0usize;
        v___x_3646_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_inst_3635_,
            v___x_3643_,
            v_sz_3644_,
            v___x_3645_,
            v_args_3641_,
        );
        v___x_3647_ = crate::leanh::lean_apply_4(
            v_toBind_3638_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_3646_,
            v___f_3642_,
        );
        return v___x_3647_;
    } else {
        let mut v___x_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_3635_);
        v___x_3648_ = crate::leanh::lean_apply_1(v_fn_3636_, v_x_3637_);
        return v___x_3648_;
    }
}
pub unsafe fn l_Lean_Syntax_rewriteBottomUpM(
    mut v_m_3649_: *mut crate::leanh::LeanObject,
    mut v_inst_3650_: *mut crate::leanh::LeanObject,
    mut v_fn_3651_: *mut crate::leanh::LeanObject,
    mut v_x_3652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3653_ = l_Lean_Syntax_rewriteBottomUpM___redArg(v_inst_3650_, v_fn_3651_, v_x_3652_);
    return v___x_3653_;
}
pub unsafe fn l_Lean_Syntax_rewriteBottomUp___lam__0(
    mut v_fn_3654_: *mut crate::leanh::LeanObject,
    mut v_x_3655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3656_ = crate::leanh::lean_apply_1(v_fn_3654_, v_x_3655_);
    return v___x_3656_;
}
pub unsafe fn l_Lean_Syntax_rewriteBottomUp(
    mut v_fn_3676_: *mut crate::leanh::LeanObject,
    mut v_stx_3677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3678_ = crate::leanh::lean_alloc_closure(
        l_Lean_Syntax_rewriteBottomUp___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3678_, 0, v_fn_3676_);
    v___x_3679_ = l_Lean_Syntax_rewriteBottomUp___closed__9;
    v___x_3680_ = l_Lean_Syntax_rewriteBottomUpM___redArg(v___x_3679_, v___f_3678_, v_stx_3677_);
    return v___x_3680_;
}
pub unsafe fn l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(
    mut v_x_3681_: *mut crate::leanh::LeanObject,
    mut v_x_3682_: *mut crate::leanh::LeanObject,
    mut v_x_3683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leading_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trailing_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3690_: u8 = 0;
    let mut v_str_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3695_: u8 = 0;
    let mut v_str_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3700_: u8 = 0;
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3710_: u8 = 0;
    let mut v_unused_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3712_: u8 = 0;
    let mut v_unused_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3714_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3681_) == 0 {
                    v_leading_3684_ = crate::leanh::lean_ctor_get(v_x_3681_, 0);
                    v_trailing_3685_ = crate::leanh::lean_ctor_get(v_x_3681_, 2);
                    v_pos_3686_ = crate::leanh::lean_ctor_get(v_x_3681_, 1);
                    v_endPos_3687_ = crate::leanh::lean_ctor_get(v_x_3681_, 3);
                    v_isSharedCheck_3714_ = (!crate::leanh::lean_is_exclusive(v_x_3681_)) as u8;
                    if v_isSharedCheck_3714_ == 0 {
                        v___x_3689_ = v_x_3681_;
                        v_isShared_3690_ = v_isSharedCheck_3714_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_endPos_3687_);
                        crate::leanh::lean_inc(v_trailing_3685_);
                        crate::leanh::lean_inc(v_pos_3686_);
                        crate::leanh::lean_inc(v_leading_3684_);
                        crate::leanh::lean_dec(v_x_3681_);
                        v___x_3689_ = crate::leanh::lean_box(0);
                        v_isShared_3690_ = v_isSharedCheck_3714_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_3683_);
                    crate::leanh::lean_dec(v_x_3682_);
                    return v_x_3681_;
                }
            }
            1 => {
                v_str_3691_ = crate::leanh::lean_ctor_get(v_leading_3684_, 0);
                v_stopPos_3692_ = crate::leanh::lean_ctor_get(v_leading_3684_, 2);
                v_isSharedCheck_3712_ = (!crate::leanh::lean_is_exclusive(v_leading_3684_)) as u8;
                if v_isSharedCheck_3712_ == 0 {
                    v_unused_3713_ = crate::leanh::lean_ctor_get(v_leading_3684_, 1);
                    crate::leanh::lean_dec(v_unused_3713_);
                    v___x_3694_ = v_leading_3684_;
                    v_isShared_3695_ = v_isSharedCheck_3712_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_3692_);
                    crate::leanh::lean_inc(v_str_3691_);
                    crate::leanh::lean_dec(v_leading_3684_);
                    v___x_3694_ = crate::leanh::lean_box(0);
                    v_isShared_3695_ = v_isSharedCheck_3712_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_str_3696_ = crate::leanh::lean_ctor_get(v_trailing_3685_, 0);
                v_startPos_3697_ = crate::leanh::lean_ctor_get(v_trailing_3685_, 1);
                v_isSharedCheck_3710_ = (!crate::leanh::lean_is_exclusive(v_trailing_3685_)) as u8;
                if v_isSharedCheck_3710_ == 0 {
                    v_unused_3711_ = crate::leanh::lean_ctor_get(v_trailing_3685_, 2);
                    crate::leanh::lean_dec(v_unused_3711_);
                    v___x_3699_ = v_trailing_3685_;
                    v_isShared_3700_ = v_isSharedCheck_3710_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_startPos_3697_);
                    crate::leanh::lean_inc(v_str_3696_);
                    crate::leanh::lean_dec(v_trailing_3685_);
                    v___x_3699_ = crate::leanh::lean_box(0);
                    v_isShared_3700_ = v_isSharedCheck_3710_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3700_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3699_, 2, v_stopPos_3692_);
                    crate::leanh::lean_ctor_set(v___x_3699_, 1, v_x_3682_);
                    crate::leanh::lean_ctor_set(v___x_3699_, 0, v_str_3691_);
                    v___x_3702_ = v___x_3699_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3709_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_str_3691_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3709_, 1, v_x_3682_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3709_, 2, v_stopPos_3692_);
                    v___x_3702_ = v_reuseFailAlloc_3709_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3695_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3694_, 2, v_x_3683_);
                    crate::leanh::lean_ctor_set(v___x_3694_, 1, v_startPos_3697_);
                    crate::leanh::lean_ctor_set(v___x_3694_, 0, v_str_3696_);
                    v___x_3704_ = v___x_3694_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3708_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_str_3696_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3708_, 1, v_startPos_3697_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3708_, 2, v_x_3683_);
                    v___x_3704_ = v_reuseFailAlloc_3708_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3690_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3689_, 2, v___x_3704_);
                    crate::leanh::lean_ctor_set(v___x_3689_, 0, v___x_3702_);
                    v___x_3706_ = v___x_3689_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3707_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3702_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3707_, 1, v_pos_3686_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3707_, 2, v___x_3704_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3707_, 3, v_endPos_3687_);
                    v___x_3706_ = v_reuseFailAlloc_3707_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3706_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(
    mut v___x_3715_: *mut crate::leanh::LeanObject,
    mut v___x_3716_: *mut crate::leanh::LeanObject,
    mut v___x_3717_: *mut crate::leanh::LeanObject,
    mut v_a_3718_: *mut crate::leanh::LeanObject,
    mut v_b_3719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: u8 = 0;
    let mut v___x_3724_: u32 = 0;
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: u32 = 0;
    let mut v___x_3727_: u8 = 0;
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_3720_ = crate::leanh::lean_ctor_get(v___x_3715_, 1);
                v_endExclusive_3721_ = crate::leanh::lean_ctor_get(v___x_3715_, 2);
                v___x_3722_ = lean_nat_sub(v_endExclusive_3721_, v_startInclusive_3720_);
                v___x_3723_ = lean_nat_dec_eq(v_a_3718_, v___x_3722_);
                crate::leanh::lean_dec(v___x_3722_);
                if v___x_3723_ == 0 {
                    v___x_3724_ = 10;
                    v___x_3725_ = lean_nat_add(v___x_3716_, v_a_3718_);
                    v___x_3726_ = lean_string_utf8_get_fast(v___x_3717_, v___x_3725_);
                    v___x_3727_ = lean_uint32_dec_eq(v___x_3726_, v___x_3724_);
                    if v___x_3727_ == 0 {
                        crate::leanh::lean_dec(v_a_3718_);
                        v___x_3728_ = crate::leanh::lean_box(0);
                        v___x_3729_ = lean_string_utf8_next_fast(v___x_3717_, v___x_3725_);
                        crate::leanh::lean_dec(v___x_3725_);
                        v___x_3730_ = lean_nat_sub(v___x_3729_, v___x_3716_);
                        v_a_3718_ = v___x_3730_;
                        v_b_3719_ = v___x_3728_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3725_);
                        v___x_3732_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3732_, 0, v_a_3718_);
                        return v___x_3732_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3718_);
                    crate::leanh::lean_inc(v_b_3719_);
                    return v_b_3719_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg___boxed(
    mut v___x_3733_: *mut crate::leanh::LeanObject,
    mut v___x_3734_: *mut crate::leanh::LeanObject,
    mut v___x_3735_: *mut crate::leanh::LeanObject,
    mut v_a_3736_: *mut crate::leanh::LeanObject,
    mut v_b_3737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3738_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v___x_3733_, v___x_3734_, v___x_3735_, v_a_3736_, v_b_3737_);
    crate::leanh::lean_dec(v_b_3737_);
    crate::leanh::lean_dec_ref(v___x_3735_);
    crate::leanh::lean_dec(v___x_3734_);
    crate::leanh::lean_dec_ref(v___x_3733_);
    return v_res_3738_;
}
pub unsafe fn l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(
    mut v_trail_3739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3745_: u8 = 0;
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: u8 = 0;
    let mut v___x_3750_: u8 = 0;
    let mut v___x_3751_: u8 = 0;
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3762_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_3740_ = crate::leanh::lean_ctor_get(v_trail_3739_, 0);
                v_startPos_3741_ = crate::leanh::lean_ctor_get(v_trail_3739_, 1);
                v_stopPos_3742_ = crate::leanh::lean_ctor_get(v_trail_3739_, 2);
                v_isSharedCheck_3762_ = (!crate::leanh::lean_is_exclusive(v_trail_3739_)) as u8;
                if v_isSharedCheck_3762_ == 0 {
                    v___x_3744_ = v_trail_3739_;
                    v_isShared_3745_ = v_isSharedCheck_3762_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_3742_);
                    crate::leanh::lean_inc(v_startPos_3741_);
                    crate::leanh::lean_inc(v_str_3740_);
                    crate::leanh::lean_dec(v_trail_3739_);
                    v___x_3744_ = crate::leanh::lean_box(0);
                    v_isShared_3745_ = v_isSharedCheck_3762_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3749_ = lean_string_is_valid_pos(v_str_3740_, v_startPos_3741_);
                if v___x_3749_ == 0 {
                    crate::leanh::lean_del_object(v___x_3744_);
                    crate::leanh::lean_dec_ref(v_str_3740_);
                    state = 2;
                    continue;
                } else {
                    v___x_3750_ = lean_string_is_valid_pos(v_str_3740_, v_stopPos_3742_);
                    if v___x_3750_ == 0 {
                        crate::leanh::lean_del_object(v___x_3744_);
                        crate::leanh::lean_dec_ref(v_str_3740_);
                        state = 2;
                        continue;
                    } else {
                        v___x_3751_ = lean_nat_dec_le(v_startPos_3741_, v_stopPos_3742_);
                        if v___x_3751_ == 0 {
                            crate::leanh::lean_del_object(v___x_3744_);
                            crate::leanh::lean_dec_ref(v_str_3740_);
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_stopPos_3742_);
                            crate::leanh::lean_inc(v_startPos_3741_);
                            crate::leanh::lean_inc_ref(v_str_3740_);
                            if v_isShared_3745_ == 0 {
                                v___x_3753_ = v___x_3744_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3761_ =
                                    crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_str_3740_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3761_,
                                    1,
                                    v_startPos_3741_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3761_,
                                    2,
                                    v_stopPos_3742_,
                                );
                                v___x_3753_ = v_reuseFailAlloc_3761_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_3747_ = lean_nat_sub(v_stopPos_3742_, v_startPos_3741_);
                crate::leanh::lean_dec(v_stopPos_3742_);
                v___x_3748_ = lean_nat_add(v_startPos_3741_, v___x_3747_);
                crate::leanh::lean_dec(v___x_3747_);
                crate::leanh::lean_dec(v_startPos_3741_);
                return v___x_3748_;
            }
            3 => {
                v_searcher_3754_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3755_ = crate::leanh::lean_box(0);
                v___x_3756_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v___x_3753_, v_startPos_3741_, v_str_3740_, v_searcher_3754_, v___x_3755_);
                crate::leanh::lean_dec_ref(v_str_3740_);
                crate::leanh::lean_dec_ref(v___x_3753_);
                if crate::leanh::lean_obj_tag(v___x_3756_) == 0 {
                    v___x_3757_ = lean_nat_sub(v_stopPos_3742_, v_startPos_3741_);
                    crate::leanh::lean_dec(v_stopPos_3742_);
                    v___x_3758_ = lean_nat_add(v_startPos_3741_, v___x_3757_);
                    crate::leanh::lean_dec(v___x_3757_);
                    crate::leanh::lean_dec(v_startPos_3741_);
                    return v___x_3758_;
                } else {
                    crate::leanh::lean_dec(v_stopPos_3742_);
                    v_val_3759_ = crate::leanh::lean_ctor_get(v___x_3756_, 0);
                    crate::leanh::lean_inc(v_val_3759_);
                    crate::leanh::lean_dec_ref_known(v___x_3756_, 1);
                    v___x_3760_ = lean_nat_add(v_startPos_3741_, v_val_3759_);
                    crate::leanh::lean_dec(v_val_3759_);
                    crate::leanh::lean_dec(v_startPos_3741_);
                    return v___x_3760_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(
    mut v___x_3763_: *mut crate::leanh::LeanObject,
    mut v___x_3764_: *mut crate::leanh::LeanObject,
    mut v___x_3765_: *mut crate::leanh::LeanObject,
    mut v_inst_3766_: *mut crate::leanh::LeanObject,
    mut v_R_3767_: *mut crate::leanh::LeanObject,
    mut v_a_3768_: *mut crate::leanh::LeanObject,
    mut v_b_3769_: *mut crate::leanh::LeanObject,
    mut v_c_3770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3771_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v___x_3763_, v___x_3764_, v___x_3765_, v_a_3768_, v_b_3769_);
    return v___x_3771_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___boxed(
    mut v___x_3772_: *mut crate::leanh::LeanObject,
    mut v___x_3773_: *mut crate::leanh::LeanObject,
    mut v___x_3774_: *mut crate::leanh::LeanObject,
    mut v_inst_3775_: *mut crate::leanh::LeanObject,
    mut v_R_3776_: *mut crate::leanh::LeanObject,
    mut v_a_3777_: *mut crate::leanh::LeanObject,
    mut v_b_3778_: *mut crate::leanh::LeanObject,
    mut v_c_3779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3780_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(v___x_3772_, v___x_3773_, v___x_3774_, v_inst_3775_, v_R_3776_, v_a_3777_, v_b_3778_, v_c_3779_);
    crate::leanh::lean_dec(v_b_3778_);
    crate::leanh::lean_dec_ref(v___x_3774_);
    crate::leanh::lean_dec(v___x_3773_);
    crate::leanh::lean_dec_ref(v___x_3772_);
    return v_res_3780_;
}
pub unsafe fn l___private_Lean_Syntax_0__Lean_Syntax_updateLeadingAux(
    mut v_x_3781_: *mut crate::leanh::LeanObject,
    mut v_a_3782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3791_: u8 = 0;
    let mut v_trailing_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trailStop_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3800_: u8 = 0;
    let mut v_unused_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rawVal_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preresolved_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3808_: u8 = 0;
    let mut v_trailing_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trailStop_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3817_: u8 = 0;
    let mut v_unused_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_3781_) {
                2 => {
                    v_info_3787_ = crate::leanh::lean_ctor_get(v_x_3781_, 0);
                    crate::leanh::lean_inc(v_info_3787_);
                    if crate::leanh::lean_obj_tag(v_info_3787_) == 0 {
                        v_val_3788_ = crate::leanh::lean_ctor_get(v_x_3781_, 1);
                        v_isSharedCheck_3800_ = (!crate::leanh::lean_is_exclusive(v_x_3781_)) as u8;
                        if v_isSharedCheck_3800_ == 0 {
                            v_unused_3801_ = crate::leanh::lean_ctor_get(v_x_3781_, 0);
                            crate::leanh::lean_dec(v_unused_3801_);
                            v___x_3790_ = v_x_3781_;
                            v_isShared_3791_ = v_isSharedCheck_3800_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3788_);
                            crate::leanh::lean_dec(v_x_3781_);
                            v___x_3790_ = crate::leanh::lean_box(0);
                            v_isShared_3791_ = v_isSharedCheck_3800_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_info_3787_);
                        crate::leanh::lean_dec_ref_known(v_x_3781_, 2);
                        v___y_3784_ = v_a_3782_;
                        state = 1;
                        continue;
                    }
                }
                3 => {
                    v_info_3802_ = crate::leanh::lean_ctor_get(v_x_3781_, 0);
                    crate::leanh::lean_inc(v_info_3802_);
                    if crate::leanh::lean_obj_tag(v_info_3802_) == 0 {
                        v_rawVal_3803_ = crate::leanh::lean_ctor_get(v_x_3781_, 1);
                        v_val_3804_ = crate::leanh::lean_ctor_get(v_x_3781_, 2);
                        v_preresolved_3805_ = crate::leanh::lean_ctor_get(v_x_3781_, 3);
                        v_isSharedCheck_3817_ = (!crate::leanh::lean_is_exclusive(v_x_3781_)) as u8;
                        if v_isSharedCheck_3817_ == 0 {
                            v_unused_3818_ = crate::leanh::lean_ctor_get(v_x_3781_, 0);
                            crate::leanh::lean_dec(v_unused_3818_);
                            v___x_3807_ = v_x_3781_;
                            v_isShared_3808_ = v_isSharedCheck_3817_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_preresolved_3805_);
                            crate::leanh::lean_inc(v_val_3804_);
                            crate::leanh::lean_inc(v_rawVal_3803_);
                            crate::leanh::lean_dec(v_x_3781_);
                            v___x_3807_ = crate::leanh::lean_box(0);
                            v_isShared_3808_ = v_isSharedCheck_3817_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_3781_, 4);
                        crate::leanh::lean_dec(v_info_3802_);
                        v___y_3784_ = v_a_3782_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_x_3781_);
                    v___y_3784_ = v_a_3782_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_3785_ = crate::leanh::lean_box(0);
                v___x_3786_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3786_, 0, v___x_3785_);
                crate::leanh::lean_ctor_set(v___x_3786_, 1, v___y_3784_);
                return v___x_3786_;
            }
            2 => {
                v_trailing_3792_ = crate::leanh::lean_ctor_get(v_info_3787_, 2);
                crate::leanh::lean_inc_ref(v_trailing_3792_);
                v_trailStop_3793_ =
                    l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_3792_);
                crate::leanh::lean_inc(v_trailStop_3793_);
                v___x_3794_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(
                    v_info_3787_,
                    v_a_3782_,
                    v_trailStop_3793_,
                );
                if v_isShared_3791_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3790_, 0, v___x_3794_);
                    v___x_3796_ = v___x_3790_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3799_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3794_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3799_, 1, v_val_3788_);
                    v___x_3796_ = v_reuseFailAlloc_3799_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3797_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3797_, 0, v___x_3796_);
                v___x_3798_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3798_, 0, v___x_3797_);
                crate::leanh::lean_ctor_set(v___x_3798_, 1, v_trailStop_3793_);
                return v___x_3798_;
            }
            4 => {
                v_trailing_3809_ = crate::leanh::lean_ctor_get(v_info_3802_, 2);
                crate::leanh::lean_inc_ref(v_trailing_3809_);
                v_trailStop_3810_ =
                    l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_3809_);
                crate::leanh::lean_inc(v_trailStop_3810_);
                v___x_3811_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(
                    v_info_3802_,
                    v_a_3782_,
                    v_trailStop_3810_,
                );
                if v_isShared_3808_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3807_, 0, v___x_3811_);
                    v___x_3813_ = v___x_3807_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3816_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3811_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3816_, 1, v_rawVal_3803_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3816_, 2, v_val_3804_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3816_, 3, v_preresolved_3805_);
                    v___x_3813_ = v_reuseFailAlloc_3816_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3814_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3814_, 0, v___x_3813_);
                v___x_3815_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3815_, 0, v___x_3814_);
                crate::leanh::lean_ctor_set(v___x_3815_, 1, v_trailStop_3810_);
                return v___x_3815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(
    mut v___y_3819_: *mut crate::leanh::LeanObject,
    mut v___y_3820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3828_: u8 = 0;
    let mut v_trailing_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trailStop_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3837_: u8 = 0;
    let mut v_unused_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rawVal_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preresolved_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3845_: u8 = 0;
    let mut v_trailing_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trailStop_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3854_: u8 = 0;
    let mut v_unused_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v___y_3819_) {
                2 => {
                    v_info_3824_ = crate::leanh::lean_ctor_get(v___y_3819_, 0);
                    crate::leanh::lean_inc(v_info_3824_);
                    if crate::leanh::lean_obj_tag(v_info_3824_) == 0 {
                        v_val_3825_ = crate::leanh::lean_ctor_get(v___y_3819_, 1);
                        v_isSharedCheck_3837_ =
                            (!crate::leanh::lean_is_exclusive(v___y_3819_)) as u8;
                        if v_isSharedCheck_3837_ == 0 {
                            v_unused_3838_ = crate::leanh::lean_ctor_get(v___y_3819_, 0);
                            crate::leanh::lean_dec(v_unused_3838_);
                            v___x_3827_ = v___y_3819_;
                            v_isShared_3828_ = v_isSharedCheck_3837_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3825_);
                            crate::leanh::lean_dec(v___y_3819_);
                            v___x_3827_ = crate::leanh::lean_box(0);
                            v_isShared_3828_ = v_isSharedCheck_3837_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_info_3824_);
                        crate::leanh::lean_dec_ref_known(v___y_3819_, 2);
                        state = 1;
                        continue;
                    }
                }
                3 => {
                    v_info_3839_ = crate::leanh::lean_ctor_get(v___y_3819_, 0);
                    crate::leanh::lean_inc(v_info_3839_);
                    if crate::leanh::lean_obj_tag(v_info_3839_) == 0 {
                        v_rawVal_3840_ = crate::leanh::lean_ctor_get(v___y_3819_, 1);
                        v_val_3841_ = crate::leanh::lean_ctor_get(v___y_3819_, 2);
                        v_preresolved_3842_ = crate::leanh::lean_ctor_get(v___y_3819_, 3);
                        v_isSharedCheck_3854_ =
                            (!crate::leanh::lean_is_exclusive(v___y_3819_)) as u8;
                        if v_isSharedCheck_3854_ == 0 {
                            v_unused_3855_ = crate::leanh::lean_ctor_get(v___y_3819_, 0);
                            crate::leanh::lean_dec(v_unused_3855_);
                            v___x_3844_ = v___y_3819_;
                            v_isShared_3845_ = v_isSharedCheck_3854_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_preresolved_3842_);
                            crate::leanh::lean_inc(v_val_3841_);
                            crate::leanh::lean_inc(v_rawVal_3840_);
                            crate::leanh::lean_dec(v___y_3819_);
                            v___x_3844_ = crate::leanh::lean_box(0);
                            v_isShared_3845_ = v_isSharedCheck_3854_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_3819_, 4);
                        crate::leanh::lean_dec(v_info_3839_);
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v___y_3819_);
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_3822_ = crate::leanh::lean_box(0);
                v___x_3823_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3823_, 0, v___x_3822_);
                crate::leanh::lean_ctor_set(v___x_3823_, 1, v___y_3820_);
                return v___x_3823_;
            }
            2 => {
                v_trailing_3829_ = crate::leanh::lean_ctor_get(v_info_3824_, 2);
                crate::leanh::lean_inc_ref(v_trailing_3829_);
                v_trailStop_3830_ =
                    l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_3829_);
                crate::leanh::lean_inc(v_trailStop_3830_);
                v___x_3831_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(
                    v_info_3824_,
                    v___y_3820_,
                    v_trailStop_3830_,
                );
                if v_isShared_3828_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3827_, 0, v___x_3831_);
                    v___x_3833_ = v___x_3827_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3836_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3831_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3836_, 1, v_val_3825_);
                    v___x_3833_ = v_reuseFailAlloc_3836_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3834_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3834_, 0, v___x_3833_);
                v___x_3835_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3835_, 0, v___x_3834_);
                crate::leanh::lean_ctor_set(v___x_3835_, 1, v_trailStop_3830_);
                return v___x_3835_;
            }
            4 => {
                v_trailing_3846_ = crate::leanh::lean_ctor_get(v_info_3839_, 2);
                crate::leanh::lean_inc_ref(v_trailing_3846_);
                v_trailStop_3847_ =
                    l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_3846_);
                crate::leanh::lean_inc(v_trailStop_3847_);
                v___x_3848_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(
                    v_info_3839_,
                    v___y_3820_,
                    v_trailStop_3847_,
                );
                if v_isShared_3845_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3844_, 0, v___x_3848_);
                    v___x_3850_ = v___x_3844_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3853_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3853_, 0, v___x_3848_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3853_, 1, v_rawVal_3840_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3853_, 2, v_val_3841_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3853_, 3, v_preresolved_3842_);
                    v___x_3850_ = v_reuseFailAlloc_3853_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3851_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3851_, 0, v___x_3850_);
                v___x_3852_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3852_, 0, v___x_3851_);
                crate::leanh::lean_ctor_set(v___x_3852_, 1, v_trailStop_3847_);
                return v___x_3852_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(
    mut v_x_3856_: *mut crate::leanh::LeanObject,
    mut v___y_3857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_info_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3864_: usize = 0;
    let mut v___x_3865_: usize = 0;
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3871_: u8 = 0;
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3876_: u8 = 0;
    let mut v_snd_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3880_: u8 = 0;
    let mut v_val_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3885_: u8 = 0;
    let mut v_unused_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3892_: u8 = 0;
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3896_: u8 = 0;
    let mut v_unused_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3901_: u8 = 0;
    let mut v_val_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3906_: u8 = 0;
    let mut v_unused_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3856_) == 1 {
                    v_info_3858_ = crate::leanh::lean_ctor_get(v_x_3856_, 0);
                    crate::leanh::lean_inc(v_info_3858_);
                    v_kind_3859_ = crate::leanh::lean_ctor_get(v_x_3856_, 1);
                    crate::leanh::lean_inc(v_kind_3859_);
                    v_args_3860_ = crate::leanh::lean_ctor_get(v_x_3856_, 2);
                    crate::leanh::lean_inc_ref(v_args_3860_);
                    v___x_3861_ =
                        l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(
                            v_x_3856_,
                            v___y_3857_,
                        );
                    v_fst_3862_ = crate::leanh::lean_ctor_get(v___x_3861_, 0);
                    crate::leanh::lean_inc(v_fst_3862_);
                    if crate::leanh::lean_obj_tag(v_fst_3862_) == 0 {
                        v_snd_3863_ = crate::leanh::lean_ctor_get(v___x_3861_, 1);
                        crate::leanh::lean_inc(v_snd_3863_);
                        crate::leanh::lean_dec_ref(v___x_3861_);
                        v_sz_3864_ = lean_array_size(v_args_3860_);
                        v___x_3865_ = 0usize;
                        v___x_3866_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(v_sz_3864_, v___x_3865_, v_args_3860_, v_snd_3863_);
                        v_fst_3867_ = crate::leanh::lean_ctor_get(v___x_3866_, 0);
                        v_snd_3868_ = crate::leanh::lean_ctor_get(v___x_3866_, 1);
                        v_isSharedCheck_3876_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3866_)) as u8;
                        if v_isSharedCheck_3876_ == 0 {
                            v___x_3870_ = v___x_3866_;
                            v_isShared_3871_ = v_isSharedCheck_3876_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_3868_);
                            crate::leanh::lean_inc(v_fst_3867_);
                            crate::leanh::lean_dec(v___x_3866_);
                            v___x_3870_ = crate::leanh::lean_box(0);
                            v_isShared_3871_ = v_isSharedCheck_3876_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_args_3860_);
                        crate::leanh::lean_dec(v_kind_3859_);
                        crate::leanh::lean_dec(v_info_3858_);
                        v_snd_3877_ = crate::leanh::lean_ctor_get(v___x_3861_, 1);
                        v_isSharedCheck_3885_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3861_)) as u8;
                        if v_isSharedCheck_3885_ == 0 {
                            v_unused_3886_ = crate::leanh::lean_ctor_get(v___x_3861_, 0);
                            crate::leanh::lean_dec(v_unused_3886_);
                            v___x_3879_ = v___x_3861_;
                            v_isShared_3880_ = v_isSharedCheck_3885_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_3877_);
                            crate::leanh::lean_dec(v___x_3861_);
                            v___x_3879_ = crate::leanh::lean_box(0);
                            v_isShared_3880_ = v_isSharedCheck_3885_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_x_3856_);
                    v___x_3887_ =
                        l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(
                            v_x_3856_,
                            v___y_3857_,
                        );
                    v_fst_3888_ = crate::leanh::lean_ctor_get(v___x_3887_, 0);
                    crate::leanh::lean_inc(v_fst_3888_);
                    if crate::leanh::lean_obj_tag(v_fst_3888_) == 0 {
                        v_snd_3889_ = crate::leanh::lean_ctor_get(v___x_3887_, 1);
                        v_isSharedCheck_3896_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3887_)) as u8;
                        if v_isSharedCheck_3896_ == 0 {
                            v_unused_3897_ = crate::leanh::lean_ctor_get(v___x_3887_, 0);
                            crate::leanh::lean_dec(v_unused_3897_);
                            v___x_3891_ = v___x_3887_;
                            v_isShared_3892_ = v_isSharedCheck_3896_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_3889_);
                            crate::leanh::lean_dec(v___x_3887_);
                            v___x_3891_ = crate::leanh::lean_box(0);
                            v_isShared_3892_ = v_isSharedCheck_3896_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_x_3856_);
                        v_snd_3898_ = crate::leanh::lean_ctor_get(v___x_3887_, 1);
                        v_isSharedCheck_3906_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3887_)) as u8;
                        if v_isSharedCheck_3906_ == 0 {
                            v_unused_3907_ = crate::leanh::lean_ctor_get(v___x_3887_, 0);
                            crate::leanh::lean_dec(v_unused_3907_);
                            v___x_3900_ = v___x_3887_;
                            v_isShared_3901_ = v_isSharedCheck_3906_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_3898_);
                            crate::leanh::lean_dec(v___x_3887_);
                            v___x_3900_ = crate::leanh::lean_box(0);
                            v_isShared_3901_ = v_isSharedCheck_3906_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3872_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3872_, 0, v_info_3858_);
                crate::leanh::lean_ctor_set(v___x_3872_, 1, v_kind_3859_);
                crate::leanh::lean_ctor_set(v___x_3872_, 2, v_fst_3867_);
                if v_isShared_3871_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3870_, 0, v___x_3872_);
                    v___x_3874_ = v___x_3870_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3875_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3875_, 0, v___x_3872_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3875_, 1, v_snd_3868_);
                    v___x_3874_ = v_reuseFailAlloc_3875_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3874_;
            }
            3 => {
                v_val_3881_ = crate::leanh::lean_ctor_get(v_fst_3862_, 0);
                crate::leanh::lean_inc(v_val_3881_);
                crate::leanh::lean_dec_ref_known(v_fst_3862_, 1);
                if v_isShared_3880_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3879_, 0, v_val_3881_);
                    v___x_3883_ = v___x_3879_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3884_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_val_3881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3884_, 1, v_snd_3877_);
                    v___x_3883_ = v_reuseFailAlloc_3884_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3883_;
            }
            5 => {
                if v_isShared_3892_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3891_, 0, v_x_3856_);
                    v___x_3894_ = v___x_3891_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3895_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_x_3856_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3895_, 1, v_snd_3889_);
                    v___x_3894_ = v_reuseFailAlloc_3895_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3894_;
            }
            7 => {
                v_val_3902_ = crate::leanh::lean_ctor_get(v_fst_3888_, 0);
                crate::leanh::lean_inc(v_val_3902_);
                crate::leanh::lean_dec_ref_known(v_fst_3888_, 1);
                if v_isShared_3901_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3900_, 0, v_val_3902_);
                    v___x_3904_ = v___x_3900_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3905_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_val_3902_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3905_, 1, v_snd_3898_);
                    v___x_3904_ = v_reuseFailAlloc_3905_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3904_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(
    mut v_sz_3908_: usize,
    mut v_i_3909_: usize,
    mut v_bs_3910_: *mut crate::leanh::LeanObject,
    mut v___y_3911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3912_: u8 = 0;
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: usize = 0;
    let mut v___x_3921_: usize = 0;
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3912_ = lean_usize_dec_lt(v_i_3909_, v_sz_3908_);
                if v___x_3912_ == 0 {
                    v___x_3913_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3913_, 0, v_bs_3910_);
                    crate::leanh::lean_ctor_set(v___x_3913_, 1, v___y_3911_);
                    return v___x_3913_;
                } else {
                    v_v_3914_ = lean_array_uget_borrowed(v_bs_3910_, v_i_3909_);
                    crate::leanh::lean_inc(v_v_3914_);
                    v___x_3915_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(
                        v_v_3914_,
                        v___y_3911_,
                    );
                    v_fst_3916_ = crate::leanh::lean_ctor_get(v___x_3915_, 0);
                    crate::leanh::lean_inc(v_fst_3916_);
                    v_snd_3917_ = crate::leanh::lean_ctor_get(v___x_3915_, 1);
                    crate::leanh::lean_inc(v_snd_3917_);
                    crate::leanh::lean_dec_ref(v___x_3915_);
                    v___x_3918_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3919_ = lean_array_uset(v_bs_3910_, v_i_3909_, v___x_3918_);
                    v___x_3920_ = 1usize;
                    v___x_3921_ = lean_usize_add(v_i_3909_, v___x_3920_);
                    v___x_3922_ = lean_array_uset(v_bs_x27_3919_, v_i_3909_, v_fst_3916_);
                    v_i_3909_ = v___x_3921_;
                    v_bs_3910_ = v___x_3922_;
                    v___y_3911_ = v_snd_3917_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0___boxed(
    mut v_sz_3924_: *mut crate::leanh::LeanObject,
    mut v_i_3925_: *mut crate::leanh::LeanObject,
    mut v_bs_3926_: *mut crate::leanh::LeanObject,
    mut v___y_3927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3928_: usize = 0;
    let mut v_i_boxed_3929_: usize = 0;
    let mut v_res_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3928_ = crate::leanh::lean_unbox_usize(v_sz_3924_);
    crate::leanh::lean_dec(v_sz_3924_);
    v_i_boxed_3929_ = crate::leanh::lean_unbox_usize(v_i_3925_);
    crate::leanh::lean_dec(v_i_3925_);
    v_res_3930_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(v_sz_boxed_3928_, v_i_boxed_3929_, v_bs_3926_, v___y_3927_);
    return v_res_3930_;
}
pub unsafe fn l_Lean_Syntax_updateLeading(
    mut v_stx_3931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3932_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3933_ =
        l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(v_stx_3931_, v___x_3932_);
    v_fst_3934_ = crate::leanh::lean_ctor_get(v___x_3933_, 0);
    crate::leanh::lean_inc(v_fst_3934_);
    crate::leanh::lean_dec_ref(v___x_3933_);
    return v_fst_3934_;
}
pub unsafe fn l_Lean_Syntax_updateTrailing(
    mut v_trailing_3935_: *mut crate::leanh::LeanObject,
    mut v_x_3936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_info_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3941_: u8 = 0;
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3946_: u8 = 0;
    let mut v_info_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rawVal_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preresolved_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3953_: u8 = 0;
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3958_: u8 = 0;
    let mut v_info_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: u8 = 0;
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3967_: u8 = 0;
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_last_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3976_: u8 = 0;
    let mut v_unused_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_3936_) {
                2 => {
                    v_info_3937_ = crate::leanh::lean_ctor_get(v_x_3936_, 0);
                    v_val_3938_ = crate::leanh::lean_ctor_get(v_x_3936_, 1);
                    v_isSharedCheck_3946_ = (!crate::leanh::lean_is_exclusive(v_x_3936_)) as u8;
                    if v_isSharedCheck_3946_ == 0 {
                        v___x_3940_ = v_x_3936_;
                        v_isShared_3941_ = v_isSharedCheck_3946_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3938_);
                        crate::leanh::lean_inc(v_info_3937_);
                        crate::leanh::lean_dec(v_x_3936_);
                        v___x_3940_ = crate::leanh::lean_box(0);
                        v_isShared_3941_ = v_isSharedCheck_3946_;
                        state = 1;
                        continue;
                    }
                }
                3 => {
                    v_info_3947_ = crate::leanh::lean_ctor_get(v_x_3936_, 0);
                    v_rawVal_3948_ = crate::leanh::lean_ctor_get(v_x_3936_, 1);
                    v_val_3949_ = crate::leanh::lean_ctor_get(v_x_3936_, 2);
                    v_preresolved_3950_ = crate::leanh::lean_ctor_get(v_x_3936_, 3);
                    v_isSharedCheck_3958_ = (!crate::leanh::lean_is_exclusive(v_x_3936_)) as u8;
                    if v_isSharedCheck_3958_ == 0 {
                        v___x_3952_ = v_x_3936_;
                        v_isShared_3953_ = v_isSharedCheck_3958_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_preresolved_3950_);
                        crate::leanh::lean_inc(v_val_3949_);
                        crate::leanh::lean_inc(v_rawVal_3948_);
                        crate::leanh::lean_inc(v_info_3947_);
                        crate::leanh::lean_dec(v_x_3936_);
                        v___x_3952_ = crate::leanh::lean_box(0);
                        v_isShared_3953_ = v_isSharedCheck_3958_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    v_info_3959_ = crate::leanh::lean_ctor_get(v_x_3936_, 0);
                    v_kind_3960_ = crate::leanh::lean_ctor_get(v_x_3936_, 1);
                    v_args_3961_ = crate::leanh::lean_ctor_get(v_x_3936_, 2);
                    v___x_3962_ = lean_array_get_size(v_args_3961_);
                    v___x_3963_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3964_ = lean_nat_dec_eq(v___x_3962_, v___x_3963_);
                    if v___x_3964_ == 0 {
                        crate::leanh::lean_inc_ref(v_args_3961_);
                        crate::leanh::lean_inc(v_kind_3960_);
                        crate::leanh::lean_inc(v_info_3959_);
                        v_isSharedCheck_3976_ = (!crate::leanh::lean_is_exclusive(v_x_3936_)) as u8;
                        if v_isSharedCheck_3976_ == 0 {
                            v_unused_3977_ = crate::leanh::lean_ctor_get(v_x_3936_, 2);
                            crate::leanh::lean_dec(v_unused_3977_);
                            v_unused_3978_ = crate::leanh::lean_ctor_get(v_x_3936_, 1);
                            crate::leanh::lean_dec(v_unused_3978_);
                            v_unused_3979_ = crate::leanh::lean_ctor_get(v_x_3936_, 0);
                            crate::leanh::lean_dec(v_unused_3979_);
                            v___x_3966_ = v_x_3936_;
                            v_isShared_3967_ = v_isSharedCheck_3976_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_3936_);
                            v___x_3966_ = crate::leanh::lean_box(0);
                            v_isShared_3967_ = v_isSharedCheck_3976_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_trailing_3935_);
                        return v_x_3936_;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_trailing_3935_);
                    return v_x_3936_;
                }
            },
            1 => {
                v___x_3942_ = l_Lean_SourceInfo_updateTrailing(v_trailing_3935_, v_info_3937_);
                if v_isShared_3941_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3940_, 0, v___x_3942_);
                    v___x_3944_ = v___x_3940_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3945_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3945_, 0, v___x_3942_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3945_, 1, v_val_3938_);
                    v___x_3944_ = v_reuseFailAlloc_3945_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3944_;
            }
            3 => {
                v___x_3954_ = l_Lean_SourceInfo_updateTrailing(v_trailing_3935_, v_info_3947_);
                if v_isShared_3953_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3952_, 0, v___x_3954_);
                    v___x_3956_ = v___x_3952_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3957_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3957_, 0, v___x_3954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3957_, 1, v_rawVal_3948_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3957_, 2, v_val_3949_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3957_, 3, v_preresolved_3950_);
                    v___x_3956_ = v_reuseFailAlloc_3957_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3956_;
            }
            5 => {
                v___x_3968_ = crate::leanh::lean_unsigned_to_nat(1);
                v_i_3969_ = lean_nat_sub(v___x_3962_, v___x_3968_);
                v___x_3970_ = lean_array_fget_borrowed(v_args_3961_, v_i_3969_);
                crate::leanh::lean_inc(v___x_3970_);
                v_last_3971_ = l_Lean_Syntax_updateTrailing(v_trailing_3935_, v___x_3970_);
                v_args_3972_ = lean_array_fset(v_args_3961_, v_i_3969_, v_last_3971_);
                crate::leanh::lean_dec(v_i_3969_);
                if v_isShared_3967_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3966_, 2, v_args_3972_);
                    v___x_3974_ = v___x_3966_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3975_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_info_3959_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3975_, 1, v_kind_3960_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3975_, 2, v_args_3972_);
                    v___x_3974_ = v_reuseFailAlloc_3975_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3974_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps_spec__0(
    mut v_x_3980_: *mut crate::leanh::LeanObject,
    mut v_x_3981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3981_) == 0 {
                    return v_x_3980_;
                } else {
                    v_head_3982_ = crate::leanh::lean_ctor_get(v_x_3981_, 0);
                    crate::leanh::lean_inc(v_head_3982_);
                    v_tail_3983_ = crate::leanh::lean_ctor_get(v_x_3981_, 1);
                    crate::leanh::lean_inc(v_tail_3983_);
                    crate::leanh::lean_dec_ref_known(v_x_3981_, 2);
                    v___x_3984_ = l_Lean_Name_append(v_x_3980_, v_head_3982_);
                    v_x_3980_ = v___x_3984_;
                    v_x_3981_ = v_tail_3983_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(
    mut v_n_3988_: *mut crate::leanh::LeanObject,
    mut v_nFields_x3f_3989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_nFields_x3f_3989_) == 1 {
        let mut v_val_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_nameComps_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_nPrefix_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_namePrefix_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3990_ = crate::leanh::lean_ctor_get(v_nFields_x3f_3989_, 0);
        v_nameComps_3991_ = l_Lean_Name_components(v_n_3988_);
        v___x_3992_ = l_List_lengthTR___redArg(v_nameComps_3991_);
        v_nPrefix_3993_ = lean_nat_sub(v___x_3992_, v_val_3990_);
        crate::leanh::lean_dec(v___x_3992_);
        v___x_3994_ = crate::leanh::lean_box(0);
        v___x_3995_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___closed__0;
        crate::leanh::lean_inc(v_nPrefix_3993_);
        crate::leanh::lean_inc(v_nameComps_3991_);
        v___x_3996_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
            crate::leanh::lean_box(0),
            v_nameComps_3991_,
            v_nameComps_3991_,
            v_nPrefix_3993_,
            v___x_3995_,
        );
        v_namePrefix_3997_ = l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps_spec__0(v___x_3994_, v___x_3996_);
        v___x_3998_ = l_List_drop___redArg(v_nPrefix_3993_, v_nameComps_3991_);
        crate::leanh::lean_dec(v_nameComps_3991_);
        v___x_3999_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3999_, 0, v_namePrefix_3997_);
        crate::leanh::lean_ctor_set(v___x_3999_, 1, v___x_3998_);
        return v___x_3999_;
    } else {
        let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4000_ = l_Lean_Name_components(v_n_3988_);
        return v___x_4000_;
    }
}
pub unsafe fn l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___boxed(
    mut v_n_4001_: *mut crate::leanh::LeanObject,
    mut v_nFields_x3f_4002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4003_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(
        v_n_4001_,
        v_nFields_x3f_4002_,
    );
    crate::leanh::lean_dec(v_nFields_x3f_4002_);
    return v_res_4003_;
}
pub unsafe fn l_panic___at___00Lean_Syntax_identComponents_spec__3(
    mut v_msg_4004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4005_ = crate::leanh::lean_box(0);
    v___x_4006_ = lean_panic_fn_borrowed(v___x_4005_, v_msg_4004_);
    return v___x_4006_;
}
pub unsafe fn _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4007_ = l_Lean_Syntax_getAtomVal___closed__0;
    v___x_4008_ = lean_string_utf8_byte_size(v___x_4007_);
    return v___x_4008_;
}
pub unsafe fn _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4009_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__0_once
        ),
        _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__0,
    );
    v___x_4010_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4011_ = l_Lean_Syntax_getAtomVal___closed__0;
    v___x_4012_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4012_, 0, v___x_4011_);
    crate::leanh::lean_ctor_set(v___x_4012_, 1, v___x_4010_);
    crate::leanh::lean_ctor_set(v___x_4012_, 2, v___x_4009_);
    return v___x_4012_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1(
    mut v_rawVal_4013_: *mut crate::leanh::LeanObject,
    mut v_pos_4014_: *mut crate::leanh::LeanObject,
    mut v_trailing_4015_: *mut crate::leanh::LeanObject,
    mut v_leading_4016_: *mut crate::leanh::LeanObject,
    mut v_a_4017_: *mut crate::leanh::LeanObject,
    mut v_a_4018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4025_: u8 = 0;
    let mut v_fst_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_off_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: u8 = 0;
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: u8 = 0;
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4052_: u8 = 0;
    let mut v_unused_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4017_) == 0 {
                    crate::leanh::lean_dec_ref(v_leading_4016_);
                    crate::leanh::lean_dec_ref(v_trailing_4015_);
                    v___x_4019_ = l_List_reverse___redArg(v_a_4018_);
                    return v___x_4019_;
                } else {
                    v_head_4020_ = crate::leanh::lean_ctor_get(v_a_4017_, 0);
                    crate::leanh::lean_inc(v_head_4020_);
                    v_snd_4021_ = crate::leanh::lean_ctor_get(v_head_4020_, 1);
                    crate::leanh::lean_inc(v_snd_4021_);
                    v_tail_4022_ = crate::leanh::lean_ctor_get(v_a_4017_, 1);
                    v_isSharedCheck_4052_ = (!crate::leanh::lean_is_exclusive(v_a_4017_)) as u8;
                    if v_isSharedCheck_4052_ == 0 {
                        v_unused_4053_ = crate::leanh::lean_ctor_get(v_a_4017_, 0);
                        crate::leanh::lean_dec(v_unused_4053_);
                        v___x_4024_ = v_a_4017_;
                        v_isShared_4025_ = v_isSharedCheck_4052_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4022_);
                        crate::leanh::lean_dec(v_a_4017_);
                        v___x_4024_ = crate::leanh::lean_box(0);
                        v_isShared_4025_ = v_isSharedCheck_4052_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4026_ = crate::leanh::lean_ctor_get(v_head_4020_, 0);
                crate::leanh::lean_inc(v_fst_4026_);
                crate::leanh::lean_dec(v_head_4020_);
                v_startPos_4027_ = crate::leanh::lean_ctor_get(v_snd_4021_, 1);
                v_stopPos_4028_ = crate::leanh::lean_ctor_get(v_snd_4021_, 2);
                v_startPos_4029_ = crate::leanh::lean_ctor_get(v_rawVal_4013_, 1);
                v_stopPos_4030_ = crate::leanh::lean_ctor_get(v_rawVal_4013_, 2);
                v_off_4031_ = lean_nat_sub(v_startPos_4027_, v_startPos_4029_);
                v___x_4049_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4050_ = lean_nat_dec_eq(v_off_4031_, v___x_4049_);
                if v___x_4050_ == 0 {
                    v___x_4051_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1_once), _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1);
                    v___y_4046_ = v___x_4051_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_leading_4016_);
                    v___y_4046_ = v_leading_4016_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_4035_ = lean_nat_add(v_off_4031_, v_pos_4014_);
                crate::leanh::lean_dec(v_off_4031_);
                v___x_4036_ = lean_nat_sub(v_stopPos_4028_, v_startPos_4027_);
                v___x_4037_ = lean_nat_add(v___x_4036_, v___x_4035_);
                crate::leanh::lean_dec(v___x_4036_);
                v_info_4038_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v_info_4038_, 0, v___y_4033_);
                crate::leanh::lean_ctor_set(v_info_4038_, 1, v___x_4035_);
                crate::leanh::lean_ctor_set(v_info_4038_, 2, v___y_4034_);
                crate::leanh::lean_ctor_set(v_info_4038_, 3, v___x_4037_);
                v___x_4039_ = crate::leanh::lean_box(0);
                v___x_4040_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4040_, 0, v_info_4038_);
                crate::leanh::lean_ctor_set(v___x_4040_, 1, v_snd_4021_);
                crate::leanh::lean_ctor_set(v___x_4040_, 2, v_fst_4026_);
                crate::leanh::lean_ctor_set(v___x_4040_, 3, v___x_4039_);
                if v_isShared_4025_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4024_, 1, v_a_4018_);
                    crate::leanh::lean_ctor_set(v___x_4024_, 0, v___x_4040_);
                    v___x_4042_ = v___x_4024_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4044_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4044_, 0, v___x_4040_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4044_, 1, v_a_4018_);
                    v___x_4042_ = v_reuseFailAlloc_4044_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_4017_ = v_tail_4022_;
                v_a_4018_ = v___x_4042_;
                state = 0;
                continue;
            }
            4 => {
                v___x_4047_ = lean_nat_dec_eq(v_stopPos_4028_, v_stopPos_4030_);
                if v___x_4047_ == 0 {
                    v___x_4048_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1_once), _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___closed__1);
                    v___y_4033_ = v___y_4046_;
                    v___y_4034_ = v___x_4048_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_trailing_4015_);
                    v___y_4033_ = v___y_4046_;
                    v___y_4034_ = v_trailing_4015_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1___boxed(
    mut v_rawVal_4054_: *mut crate::leanh::LeanObject,
    mut v_pos_4055_: *mut crate::leanh::LeanObject,
    mut v_trailing_4056_: *mut crate::leanh::LeanObject,
    mut v_leading_4057_: *mut crate::leanh::LeanObject,
    mut v_a_4058_: *mut crate::leanh::LeanObject,
    mut v_a_4059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4060_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1(
        v_rawVal_4054_,
        v_pos_4055_,
        v_trailing_4056_,
        v_leading_4057_,
        v_a_4058_,
        v_a_4059_,
    );
    crate::leanh::lean_dec(v_pos_4055_);
    crate::leanh::lean_dec_ref(v_rawVal_4054_);
    return v_res_4060_;
}
pub unsafe fn l_List_foldl___at___00Lean_Syntax_identComponents_spec__2(
    mut v_x_4061_: *mut crate::leanh::LeanObject,
    mut v_x_4062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4062_) == 0 {
                    return v_x_4061_;
                } else {
                    v_head_4063_ = crate::leanh::lean_ctor_get(v_x_4062_, 0);
                    v_tail_4064_ = crate::leanh::lean_ctor_get(v_x_4062_, 1);
                    v_startPos_4065_ = crate::leanh::lean_ctor_get(v_head_4063_, 1);
                    v_stopPos_4066_ = crate::leanh::lean_ctor_get(v_head_4063_, 2);
                    v___x_4067_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4068_ = lean_nat_sub(v_stopPos_4066_, v_startPos_4065_);
                    v___x_4069_ = lean_nat_add(v_x_4061_, v___x_4068_);
                    crate::leanh::lean_dec(v___x_4068_);
                    crate::leanh::lean_dec(v_x_4061_);
                    v___x_4070_ = lean_nat_add(v___x_4069_, v___x_4067_);
                    crate::leanh::lean_dec(v___x_4069_);
                    v_x_4061_ = v___x_4070_;
                    v_x_4062_ = v_tail_4064_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Lean_Syntax_identComponents_spec__2___boxed(
    mut v_x_4072_: *mut crate::leanh::LeanObject,
    mut v_x_4073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4074_ = l_List_foldl___at___00Lean_Syntax_identComponents_spec__2(v_x_4072_, v_x_4073_);
    crate::leanh::lean_dec(v_x_4073_);
    return v_res_4074_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(
    mut v_info_4075_: *mut crate::leanh::LeanObject,
    mut v_a_4076_: *mut crate::leanh::LeanObject,
    mut v_a_4077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4083_: u8 = 0;
    let mut v___x_4084_: u8 = 0;
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4095_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4076_) == 0 {
                    crate::leanh::lean_dec(v_info_4075_);
                    v___x_4078_ = l_List_reverse___redArg(v_a_4077_);
                    return v___x_4078_;
                } else {
                    v_head_4079_ = crate::leanh::lean_ctor_get(v_a_4076_, 0);
                    v_tail_4080_ = crate::leanh::lean_ctor_get(v_a_4076_, 1);
                    v_isSharedCheck_4095_ = (!crate::leanh::lean_is_exclusive(v_a_4076_)) as u8;
                    if v_isSharedCheck_4095_ == 0 {
                        v___x_4082_ = v_a_4076_;
                        v_isShared_4083_ = v_isSharedCheck_4095_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4080_);
                        crate::leanh::lean_inc(v_head_4079_);
                        crate::leanh::lean_dec(v_a_4076_);
                        v___x_4082_ = crate::leanh::lean_box(0);
                        v_isShared_4083_ = v_isSharedCheck_4095_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4084_ = 1;
                crate::leanh::lean_inc(v_head_4079_);
                v___x_4085_ = l_Lean_Name_toString(v_head_4079_, v___x_4084_);
                v___x_4086_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4087_ = lean_string_utf8_byte_size(v___x_4085_);
                v___x_4088_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4088_, 0, v___x_4085_);
                crate::leanh::lean_ctor_set(v___x_4088_, 1, v___x_4086_);
                crate::leanh::lean_ctor_set(v___x_4088_, 2, v___x_4087_);
                v___x_4089_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_info_4075_);
                v___x_4090_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4090_, 0, v_info_4075_);
                crate::leanh::lean_ctor_set(v___x_4090_, 1, v___x_4088_);
                crate::leanh::lean_ctor_set(v___x_4090_, 2, v_head_4079_);
                crate::leanh::lean_ctor_set(v___x_4090_, 3, v___x_4089_);
                if v_isShared_4083_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4082_, 1, v_a_4077_);
                    crate::leanh::lean_ctor_set(v___x_4082_, 0, v___x_4090_);
                    v___x_4092_ = v___x_4082_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4094_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4094_, 0, v___x_4090_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4094_, 1, v_a_4077_);
                    v___x_4092_ = v_reuseFailAlloc_4094_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4076_ = v_tail_4080_;
                v_a_4077_ = v___x_4092_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Syntax_identComponents___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4104_ = l_Lean_Syntax_identComponents___closed__4;
    v___x_4105_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_4106_ = crate::leanh::lean_unsigned_to_nat(359);
    v___x_4107_ = l_Lean_Syntax_identComponents___closed__3;
    v___x_4108_ = l_Lean_Syntax_identComponents___closed__2;
    v___x_4109_ = l_mkPanicMessageWithDecl(
        v___x_4108_,
        v___x_4107_,
        v___x_4106_,
        v___x_4105_,
        v___x_4104_,
    );
    return v___x_4109_;
}
pub unsafe fn l_Lean_Syntax_identComponents(
    mut v_stx_4110_: *mut crate::leanh::LeanObject,
    mut v_nFields_x3f_4111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_info_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rawVal_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4117_: u8 = 0;
    let mut v_val_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: u8 = 0;
    let mut v_leading_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trailing_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nameComps_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: u8 = 0;
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rawComps_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: u8 = 0;
    let mut v_val_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nPrefix_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prefixSz_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prefixSz_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: u8 = 0;
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: u8 = 0;
    let mut v___x_4161_: u8 = 0;
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4171_: u8 = 0;
    let mut v_unused_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_stx_4110_) == 3 {
                    v_info_4112_ = crate::leanh::lean_ctor_get(v_stx_4110_, 0);
                    v_rawVal_4113_ = crate::leanh::lean_ctor_get(v_stx_4110_, 1);
                    v_val_4114_ = crate::leanh::lean_ctor_get(v_stx_4110_, 2);
                    v_isSharedCheck_4171_ = (!crate::leanh::lean_is_exclusive(v_stx_4110_)) as u8;
                    if v_isSharedCheck_4171_ == 0 {
                        v_unused_4172_ = crate::leanh::lean_ctor_get(v_stx_4110_, 3);
                        crate::leanh::lean_dec(v_unused_4172_);
                        v___x_4116_ = v_stx_4110_;
                        v_isShared_4117_ = v_isSharedCheck_4171_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4114_);
                        crate::leanh::lean_inc(v_rawVal_4113_);
                        crate::leanh::lean_inc(v_info_4112_);
                        crate::leanh::lean_dec(v_stx_4110_);
                        v___x_4116_ = crate::leanh::lean_box(0);
                        v_isShared_4117_ = v_isSharedCheck_4171_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_stx_4110_);
                    v___x_4173_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Syntax_identComponents___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Syntax_identComponents___closed__5_once),
                        _init_l_Lean_Syntax_identComponents___closed__5,
                    );
                    v___x_4174_ = l_panic___at___00Lean_Syntax_identComponents_spec__3(v___x_4173_);
                    return v___x_4174_;
                }
            }
            1 => {
                v_val_4118_ = lean_erase_macro_scopes(v_val_4114_);
                v___x_4119_ = l_Lean_Name_getNumParts(v_val_4118_);
                v___x_4120_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4121_ = lean_nat_dec_le(v___x_4119_, v___x_4120_);
                crate::leanh::lean_dec(v___x_4119_);
                if v___x_4121_ == 0 {
                    crate::leanh::lean_del_object(v___x_4116_);
                    if crate::leanh::lean_obj_tag(v_info_4112_) == 0 {
                        v_leading_4122_ = crate::leanh::lean_ctor_get(v_info_4112_, 0);
                        v_pos_4123_ = crate::leanh::lean_ctor_get(v_info_4112_, 1);
                        v_trailing_4124_ = crate::leanh::lean_ctor_get(v_info_4112_, 2);
                        v_nameComps_4125_ =
                            l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(
                                v_val_4118_,
                                v_nFields_x3f_4111_,
                            );
                        crate::leanh::lean_inc_ref(v_rawVal_4113_);
                        v_rawComps_4137_ = l_Lean_Syntax_splitNameLit(v_rawVal_4113_);
                        v___x_4138_ = l_List_isEmpty___redArg(v_rawComps_4137_);
                        if v___x_4138_ == 0 {
                            if crate::leanh::lean_obj_tag(v_nFields_x3f_4111_) == 1 {
                                v_val_4139_ = crate::leanh::lean_ctor_get(v_nFields_x3f_4111_, 0);
                                v_str_4140_ = crate::leanh::lean_ctor_get(v_rawVal_4113_, 0);
                                v_startPos_4141_ = crate::leanh::lean_ctor_get(v_rawVal_4113_, 1);
                                v_stopPos_4142_ = crate::leanh::lean_ctor_get(v_rawVal_4113_, 2);
                                v___x_4143_ = l_List_lengthTR___redArg(v_rawComps_4137_);
                                v_nPrefix_4144_ = lean_nat_sub(v___x_4143_, v_val_4139_);
                                crate::leanh::lean_dec(v___x_4143_);
                                v___x_4149_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_4150_ = l_Lean_Syntax_identComponents___closed__0;
                                crate::leanh::lean_inc(v_nPrefix_4144_);
                                crate::leanh::lean_inc(v_rawComps_4137_);
                                v___x_4151_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                                    crate::leanh::lean_box(0),
                                    v_rawComps_4137_,
                                    v_rawComps_4137_,
                                    v_nPrefix_4144_,
                                    v___x_4150_,
                                );
                                v_prefixSz_4152_ =
                                    l_List_foldl___at___00Lean_Syntax_identComponents_spec__2(
                                        v___x_4149_,
                                        v___x_4151_,
                                    );
                                crate::leanh::lean_dec(v___x_4151_);
                                v_prefixSz_4153_ = lean_nat_sub(v_prefixSz_4152_, v___x_4120_);
                                crate::leanh::lean_dec(v_prefixSz_4152_);
                                v___x_4160_ = lean_nat_dec_le(v_prefixSz_4153_, v___x_4149_);
                                if v___x_4160_ == 0 {
                                    v___x_4161_ =
                                        lean_nat_dec_le(v_stopPos_4142_, v_startPos_4141_);
                                    if v___x_4161_ == 0 {
                                        crate::leanh::lean_inc(v_startPos_4141_);
                                        v___y_4155_ = v_startPos_4141_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_stopPos_4142_);
                                        v___y_4155_ = v_stopPos_4142_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_prefixSz_4153_);
                                    v___x_4162_ = l_Lean_Syntax_identComponents___closed__1;
                                    v___y_4146_ = v___x_4162_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v___y_4130_ = v_rawComps_4137_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_rawComps_4137_);
                            crate::leanh::lean_dec_ref(v_rawVal_4113_);
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_rawVal_4113_);
                        v___x_4163_ =
                            l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(
                                v_val_4118_,
                                v_nFields_x3f_4111_,
                            );
                        v___x_4164_ = crate::leanh::lean_box(0);
                        v___x_4165_ =
                            l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(
                                v_info_4112_,
                                v___x_4163_,
                                v___x_4164_,
                            );
                        return v___x_4165_;
                    }
                } else {
                    v___x_4166_ = crate::leanh::lean_box(0);
                    if v_isShared_4117_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4116_, 3, v___x_4166_);
                        crate::leanh::lean_ctor_set(v___x_4116_, 2, v_val_4118_);
                        v___x_4168_ = v___x_4116_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4170_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_info_4112_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4170_, 1, v_rawVal_4113_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4170_, 2, v_val_4118_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4170_, 3, v___x_4166_);
                        v___x_4168_ = v_reuseFailAlloc_4170_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4127_ = crate::leanh::lean_box(0);
                v___x_4128_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(
                    v_info_4112_,
                    v_nameComps_4125_,
                    v___x_4127_,
                );
                return v___x_4128_;
            }
            3 => {
                v___x_4131_ = l_List_lengthTR___redArg(v_nameComps_4125_);
                v___x_4132_ = l_List_lengthTR___redArg(v___y_4130_);
                v___x_4133_ = lean_nat_dec_eq(v___x_4131_, v___x_4132_);
                crate::leanh::lean_dec(v___x_4132_);
                crate::leanh::lean_dec(v___x_4131_);
                if v___x_4133_ == 0 {
                    crate::leanh::lean_dec(v___y_4130_);
                    crate::leanh::lean_dec_ref(v_rawVal_4113_);
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_trailing_4124_);
                    crate::leanh::lean_inc(v_pos_4123_);
                    crate::leanh::lean_inc_ref(v_leading_4122_);
                    crate::leanh::lean_dec_ref_known(v_info_4112_, 4);
                    v___x_4134_ = l_List_zipWith___at___00List_zip_spec__0(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v_nameComps_4125_,
                        v___y_4130_,
                    );
                    v___x_4135_ = crate::leanh::lean_box(0);
                    v___x_4136_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__1(
                        v_rawVal_4113_,
                        v_pos_4123_,
                        v_trailing_4124_,
                        v_leading_4122_,
                        v___x_4134_,
                        v___x_4135_,
                    );
                    crate::leanh::lean_dec(v_pos_4123_);
                    crate::leanh::lean_dec_ref(v_rawVal_4113_);
                    return v___x_4136_;
                }
            }
            4 => {
                v___x_4147_ = l_List_drop___redArg(v_nPrefix_4144_, v_rawComps_4137_);
                crate::leanh::lean_dec(v_rawComps_4137_);
                v___x_4148_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4148_, 0, v___y_4146_);
                crate::leanh::lean_ctor_set(v___x_4148_, 1, v___x_4147_);
                v___y_4130_ = v___x_4148_;
                state = 3;
                continue;
            }
            5 => {
                v___x_4156_ = lean_nat_add(v_startPos_4141_, v_prefixSz_4153_);
                crate::leanh::lean_dec(v_prefixSz_4153_);
                v___x_4157_ = lean_nat_dec_le(v_stopPos_4142_, v___x_4156_);
                if v___x_4157_ == 0 {
                    crate::leanh::lean_inc_ref(v_str_4140_);
                    v___x_4158_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4158_, 0, v_str_4140_);
                    crate::leanh::lean_ctor_set(v___x_4158_, 1, v___y_4155_);
                    crate::leanh::lean_ctor_set(v___x_4158_, 2, v___x_4156_);
                    v___y_4146_ = v___x_4158_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_4156_);
                    crate::leanh::lean_inc(v_stopPos_4142_);
                    crate::leanh::lean_inc_ref(v_str_4140_);
                    v___x_4159_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4159_, 0, v_str_4140_);
                    crate::leanh::lean_ctor_set(v___x_4159_, 1, v___y_4155_);
                    crate::leanh::lean_ctor_set(v___x_4159_, 2, v_stopPos_4142_);
                    v___y_4146_ = v___x_4159_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_4169_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4169_, 0, v___x_4168_);
                crate::leanh::lean_ctor_set(v___x_4169_, 1, v___x_4166_);
                return v___x_4169_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_identComponents___boxed(
    mut v_stx_4175_: *mut crate::leanh::LeanObject,
    mut v_nFields_x3f_4176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4177_ = l_Lean_Syntax_identComponents(v_stx_4175_, v_nFields_x3f_4176_);
    crate::leanh::lean_dec(v_nFields_x3f_4176_);
    return v_res_4177_;
}
pub unsafe fn l_Lean_Syntax_topDown(
    mut v_stx_4178_: *mut crate::leanh::LeanObject,
    mut v_firstChoiceOnly_4179_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4180_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4180_, 0, v_stx_4178_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4180_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v_firstChoiceOnly_4179_,
    );
    return v___x_4180_;
}
pub unsafe fn l_Lean_Syntax_topDown___boxed(
    mut v_stx_4181_: *mut crate::leanh::LeanObject,
    mut v_firstChoiceOnly_4182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstChoiceOnly_boxed_4183_: u8 = 0;
    let mut v_res_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstChoiceOnly_boxed_4183_ = (crate::leanh::lean_unbox(v_firstChoiceOnly_4182_) as u8);
    v_res_4184_ = l_Lean_Syntax_topDown(v_stx_4181_, v_firstChoiceOnly_boxed_4183_);
    return v_res_4184_;
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0(
    mut v_toPure_4185_: *mut crate::leanh::LeanObject,
    mut v_____r_4186_: *mut crate::leanh::LeanObject,
    mut v_b_4187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4188_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4188_, 0, v_b_4187_);
    v___x_4189_ =
        crate::leanh::lean_apply_2(v_toPure_4185_, crate::leanh::lean_box(0), v___x_4188_);
    return v___x_4189_;
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1(
    mut v___f_4190_: *mut crate::leanh::LeanObject,
    mut v_toPure_4191_: *mut crate::leanh::LeanObject,
    mut v_____s_4192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_4193_ = crate::leanh::lean_ctor_get(v_____s_4192_, 0);
    if crate::leanh::lean_obj_tag(v_fst_4193_) == 0 {
        let mut v_snd_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_4191_);
        v_snd_4194_ = crate::leanh::lean_ctor_get(v_____s_4192_, 1);
        crate::leanh::lean_inc(v_snd_4194_);
        crate::leanh::lean_dec_ref(v_____s_4192_);
        v___x_4195_ = crate::leanh::lean_box(0);
        v___x_4196_ = crate::leanh::lean_apply_2(v___f_4190_, v___x_4195_, v_snd_4194_);
        return v___x_4196_;
    } else {
        let mut v_val_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_fst_4193_);
        crate::leanh::lean_dec_ref(v_____s_4192_);
        crate::leanh::lean_dec(v___f_4190_);
        v_val_4197_ = crate::leanh::lean_ctor_get(v_fst_4193_, 0);
        crate::leanh::lean_inc(v_val_4197_);
        crate::leanh::lean_dec_ref_known(v_fst_4193_, 1);
        v___x_4198_ =
            crate::leanh::lean_apply_2(v_toPure_4191_, crate::leanh::lean_box(0), v_val_4197_);
        return v___x_4198_;
    }
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2(
    mut v_snd_4199_: *mut crate::leanh::LeanObject,
    mut v_toPure_4200_: *mut crate::leanh::LeanObject,
    mut v___x_4201_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4210_: u8 = 0;
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4216_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_4202_) == 0 {
                    crate::leanh::lean_dec(v___x_4201_);
                    v___x_4203_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4203_, 0, v_____do__lift_4202_);
                    v___x_4204_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4204_, 0, v___x_4203_);
                    crate::leanh::lean_ctor_set(v___x_4204_, 1, v_snd_4199_);
                    v___x_4205_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4205_, 0, v___x_4204_);
                    v___x_4206_ = crate::leanh::lean_apply_2(
                        v_toPure_4200_,
                        crate::leanh::lean_box(0),
                        v___x_4205_,
                    );
                    return v___x_4206_;
                } else {
                    crate::leanh::lean_dec(v_snd_4199_);
                    v_a_4207_ = crate::leanh::lean_ctor_get(v_____do__lift_4202_, 0);
                    v_isSharedCheck_4216_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_4202_)) as u8;
                    if v_isSharedCheck_4216_ == 0 {
                        v___x_4209_ = v_____do__lift_4202_;
                        v_isShared_4210_ = v_isSharedCheck_4216_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4207_);
                        crate::leanh::lean_dec(v_____do__lift_4202_);
                        v___x_4209_ = crate::leanh::lean_box(0);
                        v_isShared_4210_ = v_isSharedCheck_4216_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4211_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4211_, 0, v___x_4201_);
                crate::leanh::lean_ctor_set(v___x_4211_, 1, v_a_4207_);
                if v_isShared_4210_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4209_, 0, v___x_4211_);
                    v___x_4213_ = v___x_4209_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4215_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 0, v___x_4211_);
                    v___x_4213_ = v_reuseFailAlloc_4215_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4214_ = crate::leanh::lean_apply_2(
                    v_toPure_4200_,
                    crate::leanh::lean_box(0),
                    v___x_4213_,
                );
                return v___x_4214_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed(
    mut v_toPure_4217_: *mut crate::leanh::LeanObject,
    mut v___x_4218_: *mut crate::leanh::LeanObject,
    mut v_inst_4219_: *mut crate::leanh::LeanObject,
    mut v_f_4220_: *mut crate::leanh::LeanObject,
    mut v_firstChoiceOnly_4221_: *mut crate::leanh::LeanObject,
    mut v_toBind_4222_: *mut crate::leanh::LeanObject,
    mut v_a_4223_: *mut crate::leanh::LeanObject,
    mut v_x_4224_: *mut crate::leanh::LeanObject,
    mut v___y_4225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstChoiceOnly_boxed_4226_: u8 = 0;
    let mut v_res_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstChoiceOnly_boxed_4226_ = (crate::leanh::lean_unbox(v_firstChoiceOnly_4221_) as u8);
    v_res_4227_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(
        v_toPure_4217_,
        v___x_4218_,
        v_inst_4219_,
        v_f_4220_,
        v_firstChoiceOnly_boxed_4226_,
        v_toBind_4222_,
        v_a_4223_,
        v_x_4224_,
        v___y_4225_,
    );
    return v_res_4227_;
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(
    mut v_toPure_4231_: *mut crate::leanh::LeanObject,
    mut v_stx_4232_: *mut crate::leanh::LeanObject,
    mut v_inst_4233_: *mut crate::leanh::LeanObject,
    mut v_f_4234_: *mut crate::leanh::LeanObject,
    mut v_firstChoiceOnly_4235_: u8,
    mut v_toBind_4236_: *mut crate::leanh::LeanObject,
    mut v___f_4237_: *mut crate::leanh::LeanObject,
    mut v___f_4238_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4249_: usize = 0;
    let mut v___x_4250_: usize = 0;
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: u8 = 0;
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_4239_) == 0 {
                    crate::leanh::lean_dec(v___f_4238_);
                    crate::leanh::lean_dec(v___f_4237_);
                    crate::leanh::lean_dec(v_toBind_4236_);
                    crate::leanh::lean_dec(v_f_4234_);
                    crate::leanh::lean_dec_ref(v_inst_4233_);
                    crate::leanh::lean_dec(v_stx_4232_);
                    v___x_4240_ = crate::leanh::lean_apply_2(
                        v_toPure_4231_,
                        crate::leanh::lean_box(0),
                        v_____do__lift_4239_,
                    );
                    return v___x_4240_;
                } else {
                    if crate::leanh::lean_obj_tag(v_stx_4232_) == 1 {
                        crate::leanh::lean_dec(v___f_4238_);
                        v_a_4241_ = crate::leanh::lean_ctor_get(v_____do__lift_4239_, 0);
                        crate::leanh::lean_inc(v_a_4241_);
                        crate::leanh::lean_dec_ref_known(v_____do__lift_4239_, 1);
                        v_kind_4242_ = crate::leanh::lean_ctor_get(v_stx_4232_, 1);
                        crate::leanh::lean_inc(v_kind_4242_);
                        v_args_4243_ = crate::leanh::lean_ctor_get(v_stx_4232_, 2);
                        crate::leanh::lean_inc_ref(v_args_4243_);
                        crate::leanh::lean_dec_ref_known(v_stx_4232_, 3);
                        if v_firstChoiceOnly_4235_ == 0 {
                            crate::leanh::lean_dec(v_kind_4242_);
                            state = 1;
                            continue;
                        } else {
                            v___x_4253_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1;
                            v___x_4254_ = lean_name_eq(v_kind_4242_, v___x_4253_);
                            crate::leanh::lean_dec(v_kind_4242_);
                            if v___x_4254_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___f_4237_);
                                crate::leanh::lean_dec(v_toBind_4236_);
                                crate::leanh::lean_dec(v_toPure_4231_);
                                v___x_4255_ = crate::leanh::lean_box(0);
                                v___x_4256_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_4257_ =
                                    lean_array_get(v___x_4255_, v_args_4243_, v___x_4256_);
                                crate::leanh::lean_dec_ref(v_args_4243_);
                                v___x_4258_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(
                                    v_inst_4233_,
                                    v_f_4234_,
                                    v_firstChoiceOnly_4235_,
                                    v___x_4257_,
                                    v_a_4241_,
                                );
                                return v___x_4258_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___f_4237_);
                        crate::leanh::lean_dec(v_toBind_4236_);
                        crate::leanh::lean_dec(v_f_4234_);
                        crate::leanh::lean_dec_ref(v_inst_4233_);
                        crate::leanh::lean_dec(v_stx_4232_);
                        crate::leanh::lean_dec(v_toPure_4231_);
                        v_a_4259_ = crate::leanh::lean_ctor_get(v_____do__lift_4239_, 0);
                        crate::leanh::lean_inc(v_a_4259_);
                        crate::leanh::lean_dec_ref_known(v_____do__lift_4239_, 1);
                        v___x_4260_ = crate::leanh::lean_box(0);
                        v___x_4261_ =
                            crate::leanh::lean_apply_2(v___f_4238_, v___x_4260_, v_a_4259_);
                        return v___x_4261_;
                    }
                }
            }
            1 => {
                v___x_4245_ = crate::leanh::lean_box(0);
                v___x_4246_ = crate::leanh::lean_box((v_firstChoiceOnly_4235_) as usize);
                crate::leanh::lean_inc(v_toBind_4236_);
                crate::leanh::lean_inc_ref(v_inst_4233_);
                v___f_4247_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed
                        as *mut core::ffi::c_void,
                    9,
                    6,
                );
                crate::leanh::lean_closure_set(v___f_4247_, 0, v_toPure_4231_);
                crate::leanh::lean_closure_set(v___f_4247_, 1, v___x_4245_);
                crate::leanh::lean_closure_set(v___f_4247_, 2, v_inst_4233_);
                crate::leanh::lean_closure_set(v___f_4247_, 3, v_f_4234_);
                crate::leanh::lean_closure_set(v___f_4247_, 4, v___x_4246_);
                crate::leanh::lean_closure_set(v___f_4247_, 5, v_toBind_4236_);
                v___x_4248_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4248_, 0, v___x_4245_);
                crate::leanh::lean_ctor_set(v___x_4248_, 1, v_a_4241_);
                v_sz_4249_ = lean_array_size(v_args_4243_);
                v___x_4250_ = 0usize;
                v___x_4251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_4233_,
                    v_args_4243_,
                    v___f_4247_,
                    v_sz_4249_,
                    v___x_4250_,
                    v___x_4248_,
                );
                v___x_4252_ = crate::leanh::lean_apply_4(
                    v_toBind_4236_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4251_,
                    v___f_4237_,
                );
                return v___x_4252_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed(
    mut v_toPure_4262_: *mut crate::leanh::LeanObject,
    mut v_stx_4263_: *mut crate::leanh::LeanObject,
    mut v_inst_4264_: *mut crate::leanh::LeanObject,
    mut v_f_4265_: *mut crate::leanh::LeanObject,
    mut v_firstChoiceOnly_4266_: *mut crate::leanh::LeanObject,
    mut v_toBind_4267_: *mut crate::leanh::LeanObject,
    mut v___f_4268_: *mut crate::leanh::LeanObject,
    mut v___f_4269_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstChoiceOnly_boxed_4271_: u8 = 0;
    let mut v_res_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstChoiceOnly_boxed_4271_ = (crate::leanh::lean_unbox(v_firstChoiceOnly_4266_) as u8);
    v_res_4272_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(
        v_toPure_4262_,
        v_stx_4263_,
        v_inst_4264_,
        v_f_4265_,
        v_firstChoiceOnly_boxed_4271_,
        v_toBind_4267_,
        v___f_4268_,
        v___f_4269_,
        v_____do__lift_4270_,
    );
    return v_res_4272_;
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(
    mut v_inst_4273_: *mut crate::leanh::LeanObject,
    mut v_f_4274_: *mut crate::leanh::LeanObject,
    mut v_firstChoiceOnly_4275_: u8,
    mut v_stx_4276_: *mut crate::leanh::LeanObject,
    mut v_b_4277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4278_ = crate::leanh::lean_ctor_get(v_inst_4273_, 0);
    v_toBind_4279_ = crate::leanh::lean_ctor_get(v_inst_4273_, 1);
    crate::leanh::lean_inc_n(v_toBind_4279_, 2);
    v_toPure_4280_ = crate::leanh::lean_ctor_get(v_toApplicative_4278_, 1);
    crate::leanh::lean_inc_n(v_toPure_4280_, 3);
    crate::leanh::lean_inc(v_f_4274_);
    crate::leanh::lean_inc(v_stx_4276_);
    v___x_4281_ = crate::leanh::lean_apply_2(v_f_4274_, v_stx_4276_, v_b_4277_);
    v___f_4282_ = crate::leanh::lean_alloc_closure(
        l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4282_, 0, v_toPure_4280_);
    crate::leanh::lean_inc_ref(v___f_4282_);
    v___f_4283_ = crate::leanh::lean_alloc_closure(
        l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4283_, 0, v___f_4282_);
    crate::leanh::lean_closure_set(v___f_4283_, 1, v_toPure_4280_);
    v___x_4284_ = crate::leanh::lean_box((v_firstChoiceOnly_4275_) as usize);
    v___f_4285_ = crate::leanh::lean_alloc_closure(
        l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed
            as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_4285_, 0, v_toPure_4280_);
    crate::leanh::lean_closure_set(v___f_4285_, 1, v_stx_4276_);
    crate::leanh::lean_closure_set(v___f_4285_, 2, v_inst_4273_);
    crate::leanh::lean_closure_set(v___f_4285_, 3, v_f_4274_);
    crate::leanh::lean_closure_set(v___f_4285_, 4, v___x_4284_);
    crate::leanh::lean_closure_set(v___f_4285_, 5, v_toBind_4279_);
    crate::leanh::lean_closure_set(v___f_4285_, 6, v___f_4283_);
    crate::leanh::lean_closure_set(v___f_4285_, 7, v___f_4282_);
    v___x_4286_ = crate::leanh::lean_apply_4(
        v_toBind_4279_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4281_,
        v___f_4285_,
    );
    return v___x_4286_;
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(
    mut v_toPure_4287_: *mut crate::leanh::LeanObject,
    mut v___x_4288_: *mut crate::leanh::LeanObject,
    mut v_inst_4289_: *mut crate::leanh::LeanObject,
    mut v_f_4290_: *mut crate::leanh::LeanObject,
    mut v_firstChoiceOnly_4291_: u8,
    mut v_toBind_4292_: *mut crate::leanh::LeanObject,
    mut v_a_4293_: *mut crate::leanh::LeanObject,
    mut v_x_4294_: *mut crate::leanh::LeanObject,
    mut v___y_4295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_4296_ = crate::leanh::lean_ctor_get(v___y_4295_, 1);
    crate::leanh::lean_inc_n(v_snd_4296_, 2);
    crate::leanh::lean_dec_ref(v___y_4295_);
    v___f_4297_ = crate::leanh::lean_alloc_closure(
        l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4297_, 0, v_snd_4296_);
    crate::leanh::lean_closure_set(v___f_4297_, 1, v_toPure_4287_);
    crate::leanh::lean_closure_set(v___f_4297_, 2, v___x_4288_);
    v___x_4298_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(
        v_inst_4289_,
        v_f_4290_,
        v_firstChoiceOnly_4291_,
        v_a_4293_,
        v_snd_4296_,
    );
    v___x_4299_ = crate::leanh::lean_apply_4(
        v_toBind_4292_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4298_,
        v___f_4297_,
    );
    return v___x_4299_;
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___boxed(
    mut v_inst_4300_: *mut crate::leanh::LeanObject,
    mut v_f_4301_: *mut crate::leanh::LeanObject,
    mut v_firstChoiceOnly_4302_: *mut crate::leanh::LeanObject,
    mut v_stx_4303_: *mut crate::leanh::LeanObject,
    mut v_b_4304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstChoiceOnly_boxed_4305_: u8 = 0;
    let mut v_res_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstChoiceOnly_boxed_4305_ = (crate::leanh::lean_unbox(v_firstChoiceOnly_4302_) as u8);
    v_res_4306_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(
        v_inst_4300_,
        v_f_4301_,
        v_firstChoiceOnly_boxed_4305_,
        v_stx_4303_,
        v_b_4304_,
    );
    return v_res_4306_;
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad_loop(
    mut v_m_4307_: *mut crate::leanh::LeanObject,
    mut v_inst_4308_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4309_: *mut crate::leanh::LeanObject,
    mut v_f_4310_: *mut crate::leanh::LeanObject,
    mut v_firstChoiceOnly_4311_: u8,
    mut v_stx_4312_: *mut crate::leanh::LeanObject,
    mut v_b_4313_: *mut crate::leanh::LeanObject,
    mut v_inst_4314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4315_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(
        v_inst_4308_,
        v_f_4310_,
        v_firstChoiceOnly_4311_,
        v_stx_4312_,
        v_b_4313_,
    );
    return v___x_4315_;
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad_loop___boxed(
    mut v_m_4316_: *mut crate::leanh::LeanObject,
    mut v_inst_4317_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4318_: *mut crate::leanh::LeanObject,
    mut v_f_4319_: *mut crate::leanh::LeanObject,
    mut v_firstChoiceOnly_4320_: *mut crate::leanh::LeanObject,
    mut v_stx_4321_: *mut crate::leanh::LeanObject,
    mut v_b_4322_: *mut crate::leanh::LeanObject,
    mut v_inst_4323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstChoiceOnly_boxed_4324_: u8 = 0;
    let mut v_res_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstChoiceOnly_boxed_4324_ = (crate::leanh::lean_unbox(v_firstChoiceOnly_4320_) as u8);
    v_res_4325_ = l_Lean_Syntax_instForInTopDownOfMonad_loop(
        v_m_4316_,
        v_inst_4317_,
        v_00_u03b2_4318_,
        v_f_4319_,
        v_firstChoiceOnly_boxed_4324_,
        v_stx_4321_,
        v_b_4322_,
        v_inst_4323_,
    );
    crate::leanh::lean_dec(v_inst_4323_);
    return v_res_4325_;
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0(
    mut v_toPure_4326_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_4328_ = crate::leanh::lean_ctor_get(v_____do__lift_4327_, 0);
    crate::leanh::lean_inc(v_a_4328_);
    crate::leanh::lean_dec_ref(v_____do__lift_4327_);
    v___x_4329_ = crate::leanh::lean_apply_2(v_toPure_4326_, crate::leanh::lean_box(0), v_a_4328_);
    return v___x_4329_;
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1(
    mut v_inst_4330_: *mut crate::leanh::LeanObject,
    mut v_toBind_4331_: *mut crate::leanh::LeanObject,
    mut v___f_4332_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4333_: *mut crate::leanh::LeanObject,
    mut v_x_4334_: *mut crate::leanh::LeanObject,
    mut v_init_4335_: *mut crate::leanh::LeanObject,
    mut v_f_4336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstChoiceOnly_4337_: u8 = 0;
    let mut v_stx_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstChoiceOnly_4337_ = crate::leanh::lean_ctor_get_uint8(
        v_x_4334_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    v_stx_4338_ = crate::leanh::lean_ctor_get(v_x_4334_, 0);
    crate::leanh::lean_inc(v_stx_4338_);
    crate::leanh::lean_dec_ref(v_x_4334_);
    v___x_4339_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(
        v_inst_4330_,
        v_f_4336_,
        v_firstChoiceOnly_4337_,
        v_stx_4338_,
        v_init_4335_,
    );
    v___x_4340_ = crate::leanh::lean_apply_4(
        v_toBind_4331_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4339_,
        v___f_4332_,
    );
    return v___x_4340_;
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad___redArg(
    mut v_inst_4341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4342_ = crate::leanh::lean_ctor_get(v_inst_4341_, 0);
    v_toBind_4343_ = crate::leanh::lean_ctor_get(v_inst_4341_, 1);
    crate::leanh::lean_inc(v_toBind_4343_);
    v_toPure_4344_ = crate::leanh::lean_ctor_get(v_toApplicative_4342_, 1);
    crate::leanh::lean_inc(v_toPure_4344_);
    v___f_4345_ = crate::leanh::lean_alloc_closure(
        l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4345_, 0, v_toPure_4344_);
    v___f_4346_ = crate::leanh::lean_alloc_closure(
        l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        7,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4346_, 0, v_inst_4341_);
    crate::leanh::lean_closure_set(v___f_4346_, 1, v_toBind_4343_);
    crate::leanh::lean_closure_set(v___f_4346_, 2, v___f_4345_);
    return v___f_4346_;
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad(
    mut v_m_4347_: *mut crate::leanh::LeanObject,
    mut v_inst_4348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4349_ = l_Lean_Syntax_instForInTopDownOfMonad___redArg(v_inst_4348_);
    return v___x_4349_;
}
pub unsafe fn l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(
    mut v_info_4351_: *mut crate::leanh::LeanObject,
    mut v_val_4352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_info_4351_) == 0 {
        let mut v_leading_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_trailing_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_leading_4353_ = crate::leanh::lean_ctor_get(v_info_4351_, 0);
        crate::leanh::lean_inc_ref(v_leading_4353_);
        v_trailing_4354_ = crate::leanh::lean_ctor_get(v_info_4351_, 2);
        crate::leanh::lean_inc_ref(v_trailing_4354_);
        crate::leanh::lean_dec_ref_known(v_info_4351_, 4);
        v___x_4355_ = lean_substring_tostring(v_leading_4353_);
        v___x_4356_ = lean_string_append(v___x_4355_, v_val_4352_);
        v___x_4357_ = lean_substring_tostring(v_trailing_4354_);
        v___x_4358_ = lean_string_append(v___x_4356_, v___x_4357_);
        crate::leanh::lean_dec_ref(v___x_4357_);
        return v___x_4358_;
    } else {
        let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_info_4351_);
        v___x_4359_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___closed__0;
        v___x_4360_ = lean_string_append(v___x_4359_, v_val_4352_);
        v___x_4361_ = lean_string_append(v___x_4360_, v___x_4359_);
        return v___x_4361_;
    }
}
pub unsafe fn l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___boxed(
    mut v_info_4362_: *mut crate::leanh::LeanObject,
    mut v_val_4363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4364_ =
        l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_4362_, v_val_4363_);
    crate::leanh::lean_dec_ref(v_val_4363_);
    return v_res_4364_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(
    mut v_firstChoiceOnly_4365_: u8,
    mut v_as_4366_: *mut crate::leanh::LeanObject,
    mut v_sz_4367_: usize,
    mut v_i_4368_: usize,
    mut v_b_4369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4370_: u8 = 0;
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4375_: u8 = 0;
    let mut v_a_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4382_: u8 = 0;
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4389_: u8 = 0;
    let mut v_unused_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: usize = 0;
    let mut v___x_4396_: usize = 0;
    let mut v_reuseFailAlloc_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4399_: u8 = 0;
    let mut v_unused_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4370_ = lean_usize_dec_lt(v_i_4368_, v_sz_4367_);
                if v___x_4370_ == 0 {
                    v___x_4371_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4371_, 0, v_b_4369_);
                    return v___x_4371_;
                } else {
                    v_snd_4372_ = crate::leanh::lean_ctor_get(v_b_4369_, 1);
                    v_isSharedCheck_4399_ = (!crate::leanh::lean_is_exclusive(v_b_4369_)) as u8;
                    if v_isSharedCheck_4399_ == 0 {
                        v_unused_4400_ = crate::leanh::lean_ctor_get(v_b_4369_, 0);
                        crate::leanh::lean_dec(v_unused_4400_);
                        v___x_4374_ = v_b_4369_;
                        v_isShared_4375_ = v_isSharedCheck_4399_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4372_);
                        crate::leanh::lean_dec(v_b_4369_);
                        v___x_4374_ = crate::leanh::lean_box(0);
                        v_isShared_4375_ = v_isSharedCheck_4399_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4376_ = lean_array_uget_borrowed(v_as_4366_, v_i_4368_);
                crate::leanh::lean_inc(v_snd_4372_);
                crate::leanh::lean_inc(v_a_4376_);
                v___x_4377_ =
                    l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(
                        v_firstChoiceOnly_4365_,
                        v_a_4376_,
                        v_snd_4372_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4377_) == 0 {
                    crate::leanh::lean_del_object(v___x_4374_);
                    crate::leanh::lean_dec(v_snd_4372_);
                    v___x_4378_ = crate::leanh::lean_box(0);
                    return v___x_4378_;
                } else {
                    v_val_4379_ = crate::leanh::lean_ctor_get(v___x_4377_, 0);
                    crate::leanh::lean_inc(v_val_4379_);
                    if crate::leanh::lean_obj_tag(v_val_4379_) == 0 {
                        v_isSharedCheck_4389_ =
                            (!crate::leanh::lean_is_exclusive(v_val_4379_)) as u8;
                        if v_isSharedCheck_4389_ == 0 {
                            v_unused_4390_ = crate::leanh::lean_ctor_get(v_val_4379_, 0);
                            crate::leanh::lean_dec(v_unused_4390_);
                            v___x_4381_ = v_val_4379_;
                            v_isShared_4382_ = v_isSharedCheck_4389_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_val_4379_);
                            v___x_4381_ = crate::leanh::lean_box(0);
                            v_isShared_4382_ = v_isSharedCheck_4389_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_4377_, 1);
                        crate::leanh::lean_dec(v_snd_4372_);
                        v_a_4391_ = crate::leanh::lean_ctor_get(v_val_4379_, 0);
                        crate::leanh::lean_inc(v_a_4391_);
                        crate::leanh::lean_dec_ref_known(v_val_4379_, 1);
                        v___x_4392_ = crate::leanh::lean_box(0);
                        if v_isShared_4375_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4374_, 1, v_a_4391_);
                            crate::leanh::lean_ctor_set(v___x_4374_, 0, v___x_4392_);
                            v___x_4394_ = v___x_4374_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_4398_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4398_, 0, v___x_4392_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4398_, 1, v_a_4391_);
                            v___x_4394_ = v_reuseFailAlloc_4398_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_4375_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4374_, 0, v___x_4377_);
                    v___x_4384_ = v___x_4374_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4388_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4388_, 0, v___x_4377_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4388_, 1, v_snd_4372_);
                    v___x_4384_ = v_reuseFailAlloc_4388_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4382_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4381_, 1);
                    crate::leanh::lean_ctor_set(v___x_4381_, 0, v___x_4384_);
                    v___x_4386_ = v___x_4381_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4387_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4387_, 0, v___x_4384_);
                    v___x_4386_ = v_reuseFailAlloc_4387_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4386_;
            }
            5 => {
                v___x_4395_ = 1usize;
                v___x_4396_ = lean_usize_add(v_i_4368_, v___x_4395_);
                v_i_4368_ = v___x_4396_;
                v_b_4369_ = v___x_4394_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(
    mut v_val_4401_: *mut crate::leanh::LeanObject,
    mut v_a_4402_: *mut crate::leanh::LeanObject,
    mut v_b_4403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4409_: u8 = 0;
    let mut v___x_4410_: u8 = 0;
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: u8 = 0;
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4425_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4404_ = crate::leanh::lean_ctor_get(v_a_4402_, 0);
                v_start_4405_ = crate::leanh::lean_ctor_get(v_a_4402_, 1);
                v_stop_4406_ = crate::leanh::lean_ctor_get(v_a_4402_, 2);
                v_isSharedCheck_4425_ = (!crate::leanh::lean_is_exclusive(v_a_4402_)) as u8;
                if v_isSharedCheck_4425_ == 0 {
                    v___x_4408_ = v_a_4402_;
                    v_isShared_4409_ = v_isSharedCheck_4425_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_4406_);
                    crate::leanh::lean_inc(v_start_4405_);
                    crate::leanh::lean_inc(v_array_4404_);
                    crate::leanh::lean_dec(v_a_4402_);
                    v___x_4408_ = crate::leanh::lean_box(0);
                    v_isShared_4409_ = v_isSharedCheck_4425_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4410_ = lean_nat_dec_lt(v_start_4405_, v_stop_4406_);
                if v___x_4410_ == 0 {
                    crate::leanh::lean_del_object(v___x_4408_);
                    crate::leanh::lean_dec(v_stop_4406_);
                    crate::leanh::lean_dec(v_start_4405_);
                    crate::leanh::lean_dec_ref(v_array_4404_);
                    v___x_4411_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4411_, 0, v_b_4403_);
                    return v___x_4411_;
                } else {
                    v___x_4412_ = lean_array_fget_borrowed(v_array_4404_, v_start_4405_);
                    crate::leanh::lean_inc(v___x_4412_);
                    v___x_4413_ = l_Lean_Syntax_reprint(v___x_4412_);
                    if crate::leanh::lean_obj_tag(v___x_4413_) == 0 {
                        crate::leanh::lean_del_object(v___x_4408_);
                        crate::leanh::lean_dec(v_stop_4406_);
                        crate::leanh::lean_dec(v_start_4405_);
                        crate::leanh::lean_dec_ref(v_array_4404_);
                        v___x_4414_ = crate::leanh::lean_box(0);
                        return v___x_4414_;
                    } else {
                        v_val_4415_ = crate::leanh::lean_ctor_get(v___x_4413_, 0);
                        crate::leanh::lean_inc(v_val_4415_);
                        crate::leanh::lean_dec_ref_known(v___x_4413_, 1);
                        v___x_4416_ = lean_string_dec_eq(v_val_4401_, v_val_4415_);
                        crate::leanh::lean_dec(v_val_4415_);
                        if v___x_4416_ == 0 {
                            crate::leanh::lean_del_object(v___x_4408_);
                            crate::leanh::lean_dec(v_stop_4406_);
                            crate::leanh::lean_dec(v_start_4405_);
                            crate::leanh::lean_dec_ref(v_array_4404_);
                            v___x_4417_ = crate::leanh::lean_box(0);
                            return v___x_4417_;
                        } else {
                            v___x_4418_ = crate::leanh::lean_box(0);
                            v___x_4419_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_4420_ = lean_nat_add(v_start_4405_, v___x_4419_);
                            crate::leanh::lean_dec(v_start_4405_);
                            if v_isShared_4409_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4408_, 1, v___x_4420_);
                                v___x_4422_ = v___x_4408_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_4424_ =
                                    crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4424_,
                                    0,
                                    v_array_4404_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4424_, 1, v___x_4420_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4424_,
                                    2,
                                    v_stop_4406_,
                                );
                                v___x_4422_ = v_reuseFailAlloc_4424_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v_a_4402_ = v___x_4422_;
                v_b_4403_ = v___x_4418_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(
    mut v_firstChoiceOnly_4426_: u8,
    mut v_stx_4427_: *mut crate::leanh::LeanObject,
    mut v_b_4428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4438_: usize = 0;
    let mut v___x_4439_: usize = 0;
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: u8 = 0;
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rawVal_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: u8 = 0;
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_stx_4427_) {
                2 => {
                    v_info_4455_ = crate::leanh::lean_ctor_get(v_stx_4427_, 0);
                    v_val_4456_ = crate::leanh::lean_ctor_get(v_stx_4427_, 1);
                    crate::leanh::lean_inc(v_info_4455_);
                    v___x_4457_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(
                        v_info_4455_,
                        v_val_4456_,
                    );
                    v_s_4458_ = lean_string_append(v_b_4428_, v___x_4457_);
                    crate::leanh::lean_dec_ref(v___x_4457_);
                    v_a_4445_ = v_s_4458_;
                    state = 3;
                    continue;
                }
                3 => {
                    v_rawVal_4459_ = crate::leanh::lean_ctor_get(v_stx_4427_, 1);
                    v_info_4460_ = crate::leanh::lean_ctor_get(v_stx_4427_, 0);
                    v_str_4461_ = crate::leanh::lean_ctor_get(v_rawVal_4459_, 0);
                    v_startPos_4462_ = crate::leanh::lean_ctor_get(v_rawVal_4459_, 1);
                    v_stopPos_4463_ = crate::leanh::lean_ctor_get(v_rawVal_4459_, 2);
                    v___x_4464_ =
                        lean_string_utf8_extract(v_str_4461_, v_startPos_4462_, v_stopPos_4463_);
                    crate::leanh::lean_inc(v_info_4460_);
                    v___x_4465_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(
                        v_info_4460_,
                        v___x_4464_,
                    );
                    crate::leanh::lean_dec_ref(v___x_4464_);
                    v_s_4466_ = lean_string_append(v_b_4428_, v___x_4465_);
                    crate::leanh::lean_dec_ref(v___x_4465_);
                    v_a_4445_ = v_s_4466_;
                    state = 3;
                    continue;
                }
                1 => {
                    v_kind_4467_ = crate::leanh::lean_ctor_get(v_stx_4427_, 1);
                    v_args_4468_ = crate::leanh::lean_ctor_get(v_stx_4427_, 2);
                    v___x_4469_ =
                        l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1;
                    v___x_4470_ = lean_name_eq(v_kind_4467_, v___x_4469_);
                    if v___x_4470_ == 0 {
                        v_a_4445_ = v_b_4428_;
                        state = 3;
                        continue;
                    } else {
                        v___x_4471_ = crate::leanh::lean_box(0);
                        v___x_4472_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4473_ =
                            lean_array_get_borrowed(v___x_4471_, v_args_4468_, v___x_4472_);
                        crate::leanh::lean_inc(v___x_4473_);
                        v___x_4474_ = l_Lean_Syntax_reprint(v___x_4473_);
                        if crate::leanh::lean_obj_tag(v___x_4474_) == 0 {
                            crate::leanh::lean_dec_ref_known(v_stx_4427_, 3);
                            crate::leanh::lean_dec_ref(v_b_4428_);
                            v___x_4475_ = crate::leanh::lean_box(0);
                            return v___x_4475_;
                        } else {
                            v_val_4476_ = crate::leanh::lean_ctor_get(v___x_4474_, 0);
                            crate::leanh::lean_inc(v_val_4476_);
                            crate::leanh::lean_dec_ref_known(v___x_4474_, 1);
                            v___x_4477_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_4478_ = lean_array_get_size(v_args_4468_);
                            crate::leanh::lean_inc_ref(v_args_4468_);
                            v___x_4479_ =
                                l_Array_toSubarray___redArg(v_args_4468_, v___x_4477_, v___x_4478_);
                            v___x_4480_ = crate::leanh::lean_box(0);
                            v___x_4481_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_4476_, v___x_4479_, v___x_4480_);
                            crate::leanh::lean_dec(v_val_4476_);
                            if crate::leanh::lean_obj_tag(v___x_4481_) == 0 {
                                crate::leanh::lean_dec_ref_known(v_stx_4427_, 3);
                                crate::leanh::lean_dec_ref(v_b_4428_);
                                v___x_4482_ = crate::leanh::lean_box(0);
                                return v___x_4482_;
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_4481_, 1);
                                v_a_4445_ = v_b_4428_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
                _ => {
                    v_a_4445_ = v_b_4428_;
                    state = 3;
                    continue;
                }
            },
            1 => {
                v___x_4431_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4431_, 0, v_b_4430_);
                v___x_4432_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4432_, 0, v___x_4431_);
                return v___x_4432_;
            }
            2 => {
                v___x_4436_ = crate::leanh::lean_box(0);
                v___x_4437_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4437_, 0, v___x_4436_);
                crate::leanh::lean_ctor_set(v___x_4437_, 1, v___y_4435_);
                v_sz_4438_ = lean_array_size(v___y_4434_);
                v___x_4439_ = 0usize;
                v___x_4440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_4426_, v___y_4434_, v_sz_4438_, v___x_4439_, v___x_4437_);
                crate::leanh::lean_dec_ref(v___y_4434_);
                if crate::leanh::lean_obj_tag(v___x_4440_) == 0 {
                    return v___x_4436_;
                } else {
                    v_val_4441_ = crate::leanh::lean_ctor_get(v___x_4440_, 0);
                    crate::leanh::lean_inc(v_val_4441_);
                    crate::leanh::lean_dec_ref_known(v___x_4440_, 1);
                    v_fst_4442_ = crate::leanh::lean_ctor_get(v_val_4441_, 0);
                    if crate::leanh::lean_obj_tag(v_fst_4442_) == 0 {
                        v_snd_4443_ = crate::leanh::lean_ctor_get(v_val_4441_, 1);
                        crate::leanh::lean_inc(v_snd_4443_);
                        crate::leanh::lean_dec(v_val_4441_);
                        v_b_4430_ = v_snd_4443_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc_ref(v_fst_4442_);
                        crate::leanh::lean_dec(v_val_4441_);
                        return v_fst_4442_;
                    }
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_stx_4427_) == 1 {
                    if v_firstChoiceOnly_4426_ == 0 {
                        v_args_4446_ = crate::leanh::lean_ctor_get(v_stx_4427_, 2);
                        crate::leanh::lean_inc_ref(v_args_4446_);
                        crate::leanh::lean_dec_ref_known(v_stx_4427_, 3);
                        v___y_4434_ = v_args_4446_;
                        v___y_4435_ = v_a_4445_;
                        state = 2;
                        continue;
                    } else {
                        v_kind_4447_ = crate::leanh::lean_ctor_get(v_stx_4427_, 1);
                        crate::leanh::lean_inc(v_kind_4447_);
                        v_args_4448_ = crate::leanh::lean_ctor_get(v_stx_4427_, 2);
                        crate::leanh::lean_inc_ref(v_args_4448_);
                        crate::leanh::lean_dec_ref_known(v_stx_4427_, 3);
                        v___x_4449_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1;
                        v___x_4450_ = lean_name_eq(v_kind_4447_, v___x_4449_);
                        crate::leanh::lean_dec(v_kind_4447_);
                        if v___x_4450_ == 0 {
                            v___y_4434_ = v_args_4448_;
                            v___y_4435_ = v_a_4445_;
                            state = 2;
                            continue;
                        } else {
                            v___x_4451_ = crate::leanh::lean_box(0);
                            v___x_4452_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_4453_ = lean_array_get(v___x_4451_, v_args_4448_, v___x_4452_);
                            crate::leanh::lean_dec_ref(v_args_4448_);
                            v_stx_4427_ = v___x_4453_;
                            v_b_4428_ = v_a_4445_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_stx_4427_);
                    v_b_4430_ = v_a_4445_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_reprint(
    mut v_stx_4483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: u8 = 0;
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4491_: u8 = 0;
    let mut v_a_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_4484_ = l_Lean_Syntax_getAtomVal___closed__0;
                v___x_4485_ = 1;
                v___x_4486_ =
                    l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(
                        v___x_4485_,
                        v_stx_4483_,
                        v_s_4484_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4486_) == 0 {
                    v___x_4487_ = crate::leanh::lean_box(0);
                    return v___x_4487_;
                } else {
                    v_val_4488_ = crate::leanh::lean_ctor_get(v___x_4486_, 0);
                    v_isSharedCheck_4496_ = (!crate::leanh::lean_is_exclusive(v___x_4486_)) as u8;
                    if v_isSharedCheck_4496_ == 0 {
                        v___x_4490_ = v___x_4486_;
                        v_isShared_4491_ = v_isSharedCheck_4496_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4488_);
                        crate::leanh::lean_dec(v___x_4486_);
                        v___x_4490_ = crate::leanh::lean_box(0);
                        v_isShared_4491_ = v_isSharedCheck_4496_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4492_ = crate::leanh::lean_ctor_get(v_val_4488_, 0);
                crate::leanh::lean_inc(v_a_4492_);
                crate::leanh::lean_dec(v_val_4488_);
                if v_isShared_4491_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4490_, 0, v_a_4492_);
                    v___x_4494_ = v___x_4490_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4495_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_a_4492_);
                    v___x_4494_ = v_reuseFailAlloc_4495_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4494_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg___boxed(
    mut v_val_4497_: *mut crate::leanh::LeanObject,
    mut v_a_4498_: *mut crate::leanh::LeanObject,
    mut v_b_4499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4500_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(
        v_val_4497_,
        v_a_4498_,
        v_b_4499_,
    );
    crate::leanh::lean_dec_ref(v_val_4497_);
    return v_res_4500_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1___boxed(
    mut v_firstChoiceOnly_4501_: *mut crate::leanh::LeanObject,
    mut v_as_4502_: *mut crate::leanh::LeanObject,
    mut v_sz_4503_: *mut crate::leanh::LeanObject,
    mut v_i_4504_: *mut crate::leanh::LeanObject,
    mut v_b_4505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstChoiceOnly_boxed_4506_: u8 = 0;
    let mut v_sz_boxed_4507_: usize = 0;
    let mut v_i_boxed_4508_: usize = 0;
    let mut v_res_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstChoiceOnly_boxed_4506_ = (crate::leanh::lean_unbox(v_firstChoiceOnly_4501_) as u8);
    v_sz_boxed_4507_ = crate::leanh::lean_unbox_usize(v_sz_4503_);
    crate::leanh::lean_dec(v_sz_4503_);
    v_i_boxed_4508_ = crate::leanh::lean_unbox_usize(v_i_4504_);
    crate::leanh::lean_dec(v_i_4504_);
    v_res_4509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_boxed_4506_, v_as_4502_, v_sz_boxed_4507_, v_i_boxed_4508_, v_b_4505_);
    crate::leanh::lean_dec_ref(v_as_4502_);
    return v_res_4509_;
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1___boxed(
    mut v_firstChoiceOnly_4510_: *mut crate::leanh::LeanObject,
    mut v_stx_4511_: *mut crate::leanh::LeanObject,
    mut v_b_4512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstChoiceOnly_boxed_4513_: u8 = 0;
    let mut v_res_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstChoiceOnly_boxed_4513_ = (crate::leanh::lean_unbox(v_firstChoiceOnly_4510_) as u8);
    v_res_4514_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(
        v_firstChoiceOnly_boxed_4513_,
        v_stx_4511_,
        v_b_4512_,
    );
    return v_res_4514_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(
    mut v_val_4515_: *mut crate::leanh::LeanObject,
    mut v_inst_4516_: *mut crate::leanh::LeanObject,
    mut v_R_4517_: *mut crate::leanh::LeanObject,
    mut v_a_4518_: *mut crate::leanh::LeanObject,
    mut v_b_4519_: *mut crate::leanh::LeanObject,
    mut v_c_4520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4521_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(
        v_val_4515_,
        v_a_4518_,
        v_b_4519_,
    );
    return v___x_4521_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___boxed(
    mut v_val_4522_: *mut crate::leanh::LeanObject,
    mut v_inst_4523_: *mut crate::leanh::LeanObject,
    mut v_R_4524_: *mut crate::leanh::LeanObject,
    mut v_a_4525_: *mut crate::leanh::LeanObject,
    mut v_b_4526_: *mut crate::leanh::LeanObject,
    mut v_c_4527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4528_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(
        v_val_4522_,
        v_inst_4523_,
        v_R_4524_,
        v_a_4525_,
        v_b_4526_,
        v_c_4527_,
    );
    crate::leanh::lean_dec_ref(v_val_4522_);
    return v_res_4528_;
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(
    mut v_firstChoiceOnly_4537_: u8,
    mut v_stx_4538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: u8 = 0;
    let mut v_kind_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4545_: usize = 0;
    let mut v___x_4546_: usize = 0;
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: u8 = 0;
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4539_ = crate::leanh::lean_box(0);
                v___x_4540_ = l_Lean_Syntax_isMissing(v_stx_4538_);
                if v___x_4540_ == 0 {
                    if crate::leanh::lean_obj_tag(v_stx_4538_) == 1 {
                        v_kind_4541_ = crate::leanh::lean_ctor_get(v_stx_4538_, 1);
                        v_args_4542_ = crate::leanh::lean_ctor_get(v_stx_4538_, 2);
                        if v_firstChoiceOnly_4537_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_4552_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1;
                            v___x_4553_ = lean_name_eq(v_kind_4541_, v___x_4552_);
                            if v___x_4553_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                v___x_4554_ = crate::leanh::lean_box(0);
                                v___x_4555_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_4556_ =
                                    lean_array_get_borrowed(v___x_4554_, v_args_4542_, v___x_4555_);
                                v_stx_4538_ = v___x_4556_;
                                state = 0;
                                continue;
                            }
                        }
                    } else {
                        v___x_4558_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__2;
                        return v___x_4558_;
                    }
                } else {
                    v___x_4559_ = crate::leanh::lean_box((v___x_4540_) as usize);
                    v___x_4560_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4560_, 0, v___x_4559_);
                    v___x_4561_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4561_, 0, v___x_4560_);
                    crate::leanh::lean_ctor_set(v___x_4561_, 1, v___x_4539_);
                    v___x_4562_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4562_, 0, v___x_4561_);
                    return v___x_4562_;
                }
            }
            1 => {
                v___x_4544_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__1;
                v_sz_4545_ = lean_array_size(v_args_4542_);
                v___x_4546_ = 0usize;
                v___x_4547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_4537_, v_args_4542_, v_sz_4545_, v___x_4546_, v___x_4544_);
                v_fst_4548_ = crate::leanh::lean_ctor_get(v___x_4547_, 0);
                crate::leanh::lean_inc(v_fst_4548_);
                if crate::leanh::lean_obj_tag(v_fst_4548_) == 0 {
                    v_snd_4549_ = crate::leanh::lean_ctor_get(v___x_4547_, 1);
                    crate::leanh::lean_inc(v_snd_4549_);
                    crate::leanh::lean_dec_ref(v___x_4547_);
                    v___x_4550_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4550_, 0, v_snd_4549_);
                    return v___x_4550_;
                } else {
                    crate::leanh::lean_dec_ref(v___x_4547_);
                    v_val_4551_ = crate::leanh::lean_ctor_get(v_fst_4548_, 0);
                    crate::leanh::lean_inc(v_val_4551_);
                    crate::leanh::lean_dec_ref_known(v_fst_4548_, 1);
                    return v_val_4551_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(
    mut v_firstChoiceOnly_4563_: u8,
    mut v_as_4564_: *mut crate::leanh::LeanObject,
    mut v_sz_4565_: usize,
    mut v_i_4566_: usize,
    mut v_b_4567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4568_: u8 = 0;
    let mut v_snd_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4572_: u8 = 0;
    let mut v_a_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: usize = 0;
    let mut v___x_4584_: usize = 0;
    let mut v_reuseFailAlloc_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4587_: u8 = 0;
    let mut v_unused_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4568_ = lean_usize_dec_lt(v_i_4566_, v_sz_4565_);
                if v___x_4568_ == 0 {
                    return v_b_4567_;
                } else {
                    v_snd_4569_ = crate::leanh::lean_ctor_get(v_b_4567_, 1);
                    v_isSharedCheck_4587_ = (!crate::leanh::lean_is_exclusive(v_b_4567_)) as u8;
                    if v_isSharedCheck_4587_ == 0 {
                        v_unused_4588_ = crate::leanh::lean_ctor_get(v_b_4567_, 0);
                        crate::leanh::lean_dec(v_unused_4588_);
                        v___x_4571_ = v_b_4567_;
                        v_isShared_4572_ = v_isSharedCheck_4587_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4569_);
                        crate::leanh::lean_dec(v_b_4567_);
                        v___x_4571_ = crate::leanh::lean_box(0);
                        v_isShared_4572_ = v_isSharedCheck_4587_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4573_ = lean_array_uget_borrowed(v_as_4564_, v_i_4566_);
                v___x_4574_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_4563_, v_a_4573_);
                if crate::leanh::lean_obj_tag(v___x_4574_) == 0 {
                    v___x_4575_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4575_, 0, v___x_4574_);
                    if v_isShared_4572_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4571_, 0, v___x_4575_);
                        v___x_4577_ = v___x_4571_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4578_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4578_, 0, v___x_4575_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4578_, 1, v_snd_4569_);
                        v___x_4577_ = v_reuseFailAlloc_4578_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_4569_);
                    v_a_4579_ = crate::leanh::lean_ctor_get(v___x_4574_, 0);
                    crate::leanh::lean_inc(v_a_4579_);
                    crate::leanh::lean_dec_ref_known(v___x_4574_, 1);
                    v___x_4580_ = crate::leanh::lean_box(0);
                    if v_isShared_4572_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4571_, 1, v_a_4579_);
                        crate::leanh::lean_ctor_set(v___x_4571_, 0, v___x_4580_);
                        v___x_4582_ = v___x_4571_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4586_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4586_, 0, v___x_4580_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4586_, 1, v_a_4579_);
                        v___x_4582_ = v_reuseFailAlloc_4586_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4577_;
            }
            3 => {
                v___x_4583_ = 1usize;
                v___x_4584_ = lean_usize_add(v_i_4566_, v___x_4583_);
                v_i_4566_ = v___x_4584_;
                v_b_4567_ = v___x_4582_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0___boxed(
    mut v_firstChoiceOnly_4589_: *mut crate::leanh::LeanObject,
    mut v_as_4590_: *mut crate::leanh::LeanObject,
    mut v_sz_4591_: *mut crate::leanh::LeanObject,
    mut v_i_4592_: *mut crate::leanh::LeanObject,
    mut v_b_4593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstChoiceOnly_boxed_4594_: u8 = 0;
    let mut v_sz_boxed_4595_: usize = 0;
    let mut v_i_boxed_4596_: usize = 0;
    let mut v_res_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstChoiceOnly_boxed_4594_ = (crate::leanh::lean_unbox(v_firstChoiceOnly_4589_) as u8);
    v_sz_boxed_4595_ = crate::leanh::lean_unbox_usize(v_sz_4591_);
    crate::leanh::lean_dec(v_sz_4591_);
    v_i_boxed_4596_ = crate::leanh::lean_unbox_usize(v_i_4592_);
    crate::leanh::lean_dec(v_i_4592_);
    v_res_4597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_boxed_4594_, v_as_4590_, v_sz_boxed_4595_, v_i_boxed_4596_, v_b_4593_);
    crate::leanh::lean_dec_ref(v_as_4590_);
    return v_res_4597_;
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___boxed(
    mut v_firstChoiceOnly_4598_: *mut crate::leanh::LeanObject,
    mut v_stx_4599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstChoiceOnly_boxed_4600_: u8 = 0;
    let mut v_res_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstChoiceOnly_boxed_4600_ = (crate::leanh::lean_unbox(v_firstChoiceOnly_4598_) as u8);
    v_res_4601_ =
        l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(
            v_firstChoiceOnly_boxed_4600_,
            v_stx_4599_,
        );
    crate::leanh::lean_dec(v_stx_4599_);
    return v_res_4601_;
}
pub unsafe fn l_Lean_Syntax_hasMissing(mut v_stx_4602_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_4603_: u8 = 0;
    let mut v___y_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: u8 = 0;
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4603_ = 0;
                v___x_4609_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v___x_4603_, v_stx_4602_);
                v_a_4610_ = crate::leanh::lean_ctor_get(v___x_4609_, 0);
                crate::leanh::lean_inc(v_a_4610_);
                crate::leanh::lean_dec_ref(v___x_4609_);
                v___y_4605_ = v_a_4610_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_4606_ = crate::leanh::lean_ctor_get(v___y_4605_, 0);
                crate::leanh::lean_inc(v_fst_4606_);
                crate::leanh::lean_dec_ref(v___y_4605_);
                if crate::leanh::lean_obj_tag(v_fst_4606_) == 0 {
                    return v___x_4603_;
                } else {
                    v_val_4607_ = crate::leanh::lean_ctor_get(v_fst_4606_, 0);
                    crate::leanh::lean_inc(v_val_4607_);
                    crate::leanh::lean_dec_ref_known(v_fst_4606_, 1);
                    v___x_4608_ = (crate::leanh::lean_unbox(v_val_4607_) as u8);
                    crate::leanh::lean_dec(v_val_4607_);
                    return v___x_4608_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_hasMissing___boxed(
    mut v_stx_4611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4612_: u8 = 0;
    let mut v_r_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4612_ = l_Lean_Syntax_hasMissing(v_stx_4611_);
    crate::leanh::lean_dec(v_stx_4611_);
    v_r_4613_ = crate::leanh::lean_box((v_res_4612_) as usize);
    return v_r_4613_;
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(
    mut v_firstChoiceOnly_4614_: u8,
    mut v_stx_4615_: *mut crate::leanh::LeanObject,
    mut v_b_4616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4617_ =
        l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(
            v_firstChoiceOnly_4614_,
            v_stx_4615_,
        );
    return v___x_4617_;
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___boxed(
    mut v_firstChoiceOnly_4618_: *mut crate::leanh::LeanObject,
    mut v_stx_4619_: *mut crate::leanh::LeanObject,
    mut v_b_4620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstChoiceOnly_boxed_4621_: u8 = 0;
    let mut v_res_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstChoiceOnly_boxed_4621_ = (crate::leanh::lean_unbox(v_firstChoiceOnly_4618_) as u8);
    v_res_4622_ =
        l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(
            v_firstChoiceOnly_boxed_4621_,
            v_stx_4619_,
            v_b_4620_,
        );
    crate::leanh::lean_dec_ref(v_b_4620_);
    crate::leanh::lean_dec(v_stx_4619_);
    return v_res_4622_;
}
pub unsafe fn l_Lean_Syntax_getRange_x3f(
    mut v_stx_4623_: *mut crate::leanh::LeanObject,
    mut v_canonicalOnly_4624_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4631_: u8 = 0;
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4636_: u8 = 0;
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4625_ = l_Lean_Syntax_getPos_x3f(v_stx_4623_, v_canonicalOnly_4624_);
                if crate::leanh::lean_obj_tag(v___x_4625_) == 1 {
                    v_val_4626_ = crate::leanh::lean_ctor_get(v___x_4625_, 0);
                    crate::leanh::lean_inc(v_val_4626_);
                    crate::leanh::lean_dec_ref_known(v___x_4625_, 1);
                    v___x_4627_ = l_Lean_Syntax_getTailPos_x3f(v_stx_4623_, v_canonicalOnly_4624_);
                    if crate::leanh::lean_obj_tag(v___x_4627_) == 1 {
                        v_val_4628_ = crate::leanh::lean_ctor_get(v___x_4627_, 0);
                        v_isSharedCheck_4636_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4627_)) as u8;
                        if v_isSharedCheck_4636_ == 0 {
                            v___x_4630_ = v___x_4627_;
                            v_isShared_4631_ = v_isSharedCheck_4636_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4628_);
                            crate::leanh::lean_dec(v___x_4627_);
                            v___x_4630_ = crate::leanh::lean_box(0);
                            v_isShared_4631_ = v_isSharedCheck_4636_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4627_);
                        crate::leanh::lean_dec(v_val_4626_);
                        v___x_4637_ = crate::leanh::lean_box(0);
                        return v___x_4637_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4625_);
                    v___x_4638_ = crate::leanh::lean_box(0);
                    return v___x_4638_;
                }
            }
            1 => {
                v___x_4632_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4632_, 0, v_val_4626_);
                crate::leanh::lean_ctor_set(v___x_4632_, 1, v_val_4628_);
                if v_isShared_4631_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4630_, 0, v___x_4632_);
                    v___x_4634_ = v___x_4630_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4635_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4635_, 0, v___x_4632_);
                    v___x_4634_ = v_reuseFailAlloc_4635_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4634_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_getRange_x3f___boxed(
    mut v_stx_4639_: *mut crate::leanh::LeanObject,
    mut v_canonicalOnly_4640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonicalOnly_boxed_4641_: u8 = 0;
    let mut v_res_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_4641_ = (crate::leanh::lean_unbox(v_canonicalOnly_4640_) as u8);
    v_res_4642_ = l_Lean_Syntax_getRange_x3f(v_stx_4639_, v_canonicalOnly_boxed_4641_);
    crate::leanh::lean_dec(v_stx_4639_);
    return v_res_4642_;
}
pub unsafe fn l_Lean_Syntax_getRangeWithTrailing_x3f(
    mut v_stx_4643_: *mut crate::leanh::LeanObject,
    mut v_canonicalOnly_4644_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4653_: u8 = 0;
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4658_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4645_ = l_Lean_Syntax_getPos_x3f(v_stx_4643_, v_canonicalOnly_4644_);
                if crate::leanh::lean_obj_tag(v___x_4645_) == 0 {
                    v___x_4646_ = crate::leanh::lean_box(0);
                    return v___x_4646_;
                } else {
                    v_val_4647_ = crate::leanh::lean_ctor_get(v___x_4645_, 0);
                    crate::leanh::lean_inc(v_val_4647_);
                    crate::leanh::lean_dec_ref_known(v___x_4645_, 1);
                    v___x_4648_ =
                        l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_4643_, v_canonicalOnly_4644_);
                    if crate::leanh::lean_obj_tag(v___x_4648_) == 0 {
                        crate::leanh::lean_dec(v_val_4647_);
                        v___x_4649_ = crate::leanh::lean_box(0);
                        return v___x_4649_;
                    } else {
                        v_val_4650_ = crate::leanh::lean_ctor_get(v___x_4648_, 0);
                        v_isSharedCheck_4658_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4648_)) as u8;
                        if v_isSharedCheck_4658_ == 0 {
                            v___x_4652_ = v___x_4648_;
                            v_isShared_4653_ = v_isSharedCheck_4658_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4650_);
                            crate::leanh::lean_dec(v___x_4648_);
                            v___x_4652_ = crate::leanh::lean_box(0);
                            v_isShared_4653_ = v_isSharedCheck_4658_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4654_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4654_, 0, v_val_4647_);
                crate::leanh::lean_ctor_set(v___x_4654_, 1, v_val_4650_);
                if v_isShared_4653_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4652_, 0, v___x_4654_);
                    v___x_4656_ = v___x_4652_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4657_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4657_, 0, v___x_4654_);
                    v___x_4656_ = v_reuseFailAlloc_4657_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4656_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_getRangeWithTrailing_x3f___boxed(
    mut v_stx_4659_: *mut crate::leanh::LeanObject,
    mut v_canonicalOnly_4660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonicalOnly_boxed_4661_: u8 = 0;
    let mut v_res_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_4661_ = (crate::leanh::lean_unbox(v_canonicalOnly_4660_) as u8);
    v_res_4662_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_4659_, v_canonicalOnly_boxed_4661_);
    crate::leanh::lean_dec(v_stx_4659_);
    return v_res_4662_;
}
pub unsafe fn l_Lean_Syntax_ofRange(
    mut v_range_4663_: *mut crate::leanh::LeanObject,
    mut v_canonical_4664_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4669_: u8 = 0;
    let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4675_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_4665_ = crate::leanh::lean_ctor_get(v_range_4663_, 0);
                v_stop_4666_ = crate::leanh::lean_ctor_get(v_range_4663_, 1);
                v_isSharedCheck_4675_ = (!crate::leanh::lean_is_exclusive(v_range_4663_)) as u8;
                if v_isSharedCheck_4675_ == 0 {
                    v___x_4668_ = v_range_4663_;
                    v_isShared_4669_ = v_isSharedCheck_4675_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_4666_);
                    crate::leanh::lean_inc(v_start_4665_);
                    crate::leanh::lean_dec(v_range_4663_);
                    v___x_4668_ = crate::leanh::lean_box(0);
                    v_isShared_4669_ = v_isSharedCheck_4675_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4670_ = crate::leanh::lean_alloc_ctor(1, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4670_, 0, v_start_4665_);
                crate::leanh::lean_ctor_set(v___x_4670_, 1, v_stop_4666_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4670_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_canonical_4664_,
                );
                v___x_4671_ = l_Lean_Syntax_getAtomVal___closed__0;
                if v_isShared_4669_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4668_, 2);
                    crate::leanh::lean_ctor_set(v___x_4668_, 1, v___x_4671_);
                    crate::leanh::lean_ctor_set(v___x_4668_, 0, v___x_4670_);
                    v___x_4673_ = v___x_4668_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4674_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4674_, 0, v___x_4670_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4674_, 1, v___x_4671_);
                    v___x_4673_ = v_reuseFailAlloc_4674_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4673_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_ofRange___boxed(
    mut v_range_4676_: *mut crate::leanh::LeanObject,
    mut v_canonical_4677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonical_boxed_4678_: u8 = 0;
    let mut v_res_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonical_boxed_4678_ = (crate::leanh::lean_unbox(v_canonical_4677_) as u8);
    v_res_4679_ = l_Lean_Syntax_ofRange(v_range_4676_, v_canonical_boxed_4678_);
    return v_res_4679_;
}
pub unsafe fn l_Lean_Syntax_Traverser_fromSyntax(
    mut v_stx_4682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4683_ = l_Lean_Syntax_Traverser_fromSyntax___closed__0;
    v___x_4684_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4684_, 0, v_stx_4682_);
    crate::leanh::lean_ctor_set(v___x_4684_, 1, v___x_4683_);
    crate::leanh::lean_ctor_set(v___x_4684_, 2, v___x_4683_);
    return v___x_4684_;
}
pub unsafe fn l_Lean_Syntax_Traverser_setCur(
    mut v_t_4685_: *mut crate::leanh::LeanObject,
    mut v_stx_4686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_parents_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idxs_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4691_: u8 = 0;
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4695_: u8 = 0;
    let mut v_unused_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_parents_4687_ = crate::leanh::lean_ctor_get(v_t_4685_, 1);
                v_idxs_4688_ = crate::leanh::lean_ctor_get(v_t_4685_, 2);
                v_isSharedCheck_4695_ = (!crate::leanh::lean_is_exclusive(v_t_4685_)) as u8;
                if v_isSharedCheck_4695_ == 0 {
                    v_unused_4696_ = crate::leanh::lean_ctor_get(v_t_4685_, 0);
                    crate::leanh::lean_dec(v_unused_4696_);
                    v___x_4690_ = v_t_4685_;
                    v_isShared_4691_ = v_isSharedCheck_4695_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idxs_4688_);
                    crate::leanh::lean_inc(v_parents_4687_);
                    crate::leanh::lean_dec(v_t_4685_);
                    v___x_4690_ = crate::leanh::lean_box(0);
                    v_isShared_4691_ = v_isSharedCheck_4695_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_4691_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4690_, 0, v_stx_4686_);
                    v___x_4693_ = v___x_4690_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4694_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4694_, 0, v_stx_4686_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4694_, 1, v_parents_4687_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4694_, 2, v_idxs_4688_);
                    v___x_4693_ = v_reuseFailAlloc_4694_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4693_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_Traverser_down(
    mut v_t_4697_: *mut crate::leanh::LeanObject,
    mut v_idx_4698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cur_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_parents_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idxs_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4704_: u8 = 0;
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: u8 = 0;
    let mut v___x_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4721_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cur_4699_ = crate::leanh::lean_ctor_get(v_t_4697_, 0);
                v_parents_4700_ = crate::leanh::lean_ctor_get(v_t_4697_, 1);
                v_idxs_4701_ = crate::leanh::lean_ctor_get(v_t_4697_, 2);
                v_isSharedCheck_4721_ = (!crate::leanh::lean_is_exclusive(v_t_4697_)) as u8;
                if v_isSharedCheck_4721_ == 0 {
                    v___x_4703_ = v_t_4697_;
                    v_isShared_4704_ = v_isSharedCheck_4721_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idxs_4701_);
                    crate::leanh::lean_inc(v_parents_4700_);
                    crate::leanh::lean_inc(v_cur_4699_);
                    crate::leanh::lean_dec(v_t_4697_);
                    v___x_4703_ = crate::leanh::lean_box(0);
                    v_isShared_4704_ = v_isSharedCheck_4721_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4705_ = l_Lean_Syntax_getNumArgs(v_cur_4699_);
                v___x_4706_ = lean_nat_dec_lt(v_idx_4698_, v___x_4705_);
                crate::leanh::lean_dec(v___x_4705_);
                if v___x_4706_ == 0 {
                    v___x_4707_ = crate::leanh::lean_box(0);
                    v___x_4708_ = lean_array_push(v_parents_4700_, v_cur_4699_);
                    v___x_4709_ = lean_array_push(v_idxs_4701_, v_idx_4698_);
                    if v_isShared_4704_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4703_, 2, v___x_4709_);
                        crate::leanh::lean_ctor_set(v___x_4703_, 1, v___x_4708_);
                        crate::leanh::lean_ctor_set(v___x_4703_, 0, v___x_4707_);
                        v___x_4711_ = v___x_4703_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4712_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4712_, 0, v___x_4707_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4712_, 1, v___x_4708_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4712_, 2, v___x_4709_);
                        v___x_4711_ = v_reuseFailAlloc_4712_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4713_ = l_Lean_Syntax_getArg(v_cur_4699_, v_idx_4698_);
                    v___x_4714_ = crate::leanh::lean_box(0);
                    v___x_4715_ = l_Lean_Syntax_setArg(v_cur_4699_, v_idx_4698_, v___x_4714_);
                    v___x_4716_ = lean_array_push(v_parents_4700_, v___x_4715_);
                    v___x_4717_ = lean_array_push(v_idxs_4701_, v_idx_4698_);
                    if v_isShared_4704_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4703_, 2, v___x_4717_);
                        crate::leanh::lean_ctor_set(v___x_4703_, 1, v___x_4716_);
                        crate::leanh::lean_ctor_set(v___x_4703_, 0, v___x_4713_);
                        v___x_4719_ = v___x_4703_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4720_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4720_, 0, v___x_4713_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4720_, 1, v___x_4716_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4720_, 2, v___x_4717_);
                        v___x_4719_ = v_reuseFailAlloc_4720_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4711_;
            }
            3 => {
                return v___x_4719_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_Traverser_up(
    mut v_t_4722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cur_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_parents_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idxs_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: u8 = 0;
    let mut v___x_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: u8 = 0;
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cur_4723_ = crate::leanh::lean_ctor_get(v_t_4722_, 0);
                v_parents_4724_ = crate::leanh::lean_ctor_get(v_t_4722_, 1);
                v_idxs_4725_ = crate::leanh::lean_ctor_get(v_t_4722_, 2);
                v___x_4731_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4732_ = lean_array_get_size(v_parents_4724_);
                v___x_4733_ = lean_nat_dec_lt(v___x_4731_, v___x_4732_);
                if v___x_4733_ == 0 {
                    return v_t_4722_;
                } else {
                    crate::leanh::lean_inc_ref(v_idxs_4725_);
                    crate::leanh::lean_inc_ref(v_parents_4724_);
                    crate::leanh::lean_inc(v_cur_4723_);
                    crate::leanh::lean_dec_ref(v_t_4722_);
                    v___x_4734_ = lean_array_get_size(v_idxs_4725_);
                    v___x_4735_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4736_ = lean_nat_sub(v___x_4734_, v___x_4735_);
                    v___x_4737_ = lean_array_get_borrowed(v___x_4731_, v_idxs_4725_, v___x_4736_);
                    crate::leanh::lean_dec(v___x_4736_);
                    v___x_4738_ = crate::leanh::lean_box(0);
                    v___x_4739_ = lean_nat_sub(v___x_4732_, v___x_4735_);
                    v___x_4740_ =
                        lean_array_get_borrowed(v___x_4738_, v_parents_4724_, v___x_4739_);
                    crate::leanh::lean_dec(v___x_4739_);
                    v___x_4741_ = l_Lean_Syntax_getNumArgs(v___x_4740_);
                    v___x_4742_ = lean_nat_dec_lt(v___x_4737_, v___x_4741_);
                    crate::leanh::lean_dec(v___x_4741_);
                    if v___x_4742_ == 0 {
                        crate::leanh::lean_dec(v_cur_4723_);
                        crate::leanh::lean_inc(v___x_4740_);
                        v___y_4727_ = v___x_4740_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v___x_4740_);
                        v___x_4743_ = l_Lean_Syntax_setArg(v___x_4740_, v___x_4737_, v_cur_4723_);
                        v___y_4727_ = v___x_4743_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4728_ = lean_array_pop(v_parents_4724_);
                v___x_4729_ = lean_array_pop(v_idxs_4725_);
                v___x_4730_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4730_, 0, v___y_4727_);
                crate::leanh::lean_ctor_set(v___x_4730_, 1, v___x_4728_);
                crate::leanh::lean_ctor_set(v___x_4730_, 2, v___x_4729_);
                return v___x_4730_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_Traverser_left(
    mut v_t_4744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_parents_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idxs_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: u8 = 0;
    v_parents_4745_ = crate::leanh::lean_ctor_get(v_t_4744_, 1);
    v_idxs_4746_ = crate::leanh::lean_ctor_get(v_t_4744_, 2);
    v___x_4747_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4748_ = lean_array_get_size(v_parents_4745_);
    v___x_4749_ = lean_nat_dec_lt(v___x_4747_, v___x_4748_);
    if v___x_4749_ == 0 {
        return v_t_4744_;
    } else {
        let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_idxs_4746_);
        v___x_4750_ = l_Lean_Syntax_Traverser_up(v_t_4744_);
        v___x_4751_ = lean_array_get_size(v_idxs_4746_);
        v___x_4752_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4753_ = lean_nat_sub(v___x_4751_, v___x_4752_);
        v___x_4754_ = lean_array_get(v___x_4747_, v_idxs_4746_, v___x_4753_);
        crate::leanh::lean_dec(v___x_4753_);
        crate::leanh::lean_dec_ref(v_idxs_4746_);
        v___x_4755_ = lean_nat_sub(v___x_4754_, v___x_4752_);
        crate::leanh::lean_dec(v___x_4754_);
        v___x_4756_ = l_Lean_Syntax_Traverser_down(v___x_4750_, v___x_4755_);
        return v___x_4756_;
    }
}
pub unsafe fn l_Lean_Syntax_Traverser_right(
    mut v_t_4757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_parents_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idxs_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: u8 = 0;
    v_parents_4758_ = crate::leanh::lean_ctor_get(v_t_4757_, 1);
    v_idxs_4759_ = crate::leanh::lean_ctor_get(v_t_4757_, 2);
    v___x_4760_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4761_ = lean_array_get_size(v_parents_4758_);
    v___x_4762_ = lean_nat_dec_lt(v___x_4760_, v___x_4761_);
    if v___x_4762_ == 0 {
        return v_t_4757_;
    } else {
        let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_idxs_4759_);
        v___x_4763_ = l_Lean_Syntax_Traverser_up(v_t_4757_);
        v___x_4764_ = lean_array_get_size(v_idxs_4759_);
        v___x_4765_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4766_ = lean_nat_sub(v___x_4764_, v___x_4765_);
        v___x_4767_ = lean_array_get(v___x_4760_, v_idxs_4759_, v___x_4766_);
        crate::leanh::lean_dec(v___x_4766_);
        crate::leanh::lean_dec_ref(v_idxs_4759_);
        v___x_4768_ = lean_nat_add(v___x_4767_, v___x_4765_);
        crate::leanh::lean_dec(v___x_4767_);
        v___x_4769_ = l_Lean_Syntax_Traverser_down(v___x_4763_, v___x_4768_);
        return v___x_4769_;
    }
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(
    mut v_self_4770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cur_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cur_4771_ = crate::leanh::lean_ctor_get(v_self_4770_, 0);
    crate::leanh::lean_inc(v_cur_4771_);
    return v_cur_4771_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0___boxed(
    mut v_self_4772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4773_ = l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(v_self_4772_);
    crate::leanh::lean_dec_ref(v_self_4772_);
    return v_res_4773_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur___redArg(
    mut v_inst_4775_: *mut crate::leanh::LeanObject,
    mut v_t_4776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4777_ = crate::leanh::lean_ctor_get(v_inst_4775_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4777_);
    crate::leanh::lean_dec_ref(v_inst_4775_);
    v_toFunctor_4778_ = crate::leanh::lean_ctor_get(v_toApplicative_4777_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_4778_);
    crate::leanh::lean_dec_ref(v_toApplicative_4777_);
    v_map_4779_ = crate::leanh::lean_ctor_get(v_toFunctor_4778_, 0);
    crate::leanh::lean_inc(v_map_4779_);
    crate::leanh::lean_dec_ref(v_toFunctor_4778_);
    v_get_4780_ = crate::leanh::lean_ctor_get(v_t_4776_, 0);
    crate::leanh::lean_inc(v_get_4780_);
    crate::leanh::lean_dec_ref(v_t_4776_);
    v___f_4781_ = l_Lean_Syntax_MonadTraverser_getCur___redArg___closed__0;
    v___x_4782_ = crate::leanh::lean_apply_4(
        v_map_4779_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_4781_,
        v_get_4780_,
    );
    return v___x_4782_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur(
    mut v_m_4783_: *mut crate::leanh::LeanObject,
    mut v_inst_4784_: *mut crate::leanh::LeanObject,
    mut v_t_4785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4786_ = l_Lean_Syntax_MonadTraverser_getCur___redArg(v_inst_4784_, v_t_4785_);
    return v___x_4786_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0(
    mut v_stx_4787_: *mut crate::leanh::LeanObject,
    mut v_s_4788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4789_ = crate::leanh::lean_box(0);
    v___x_4790_ = l_Lean_Syntax_Traverser_setCur(v_s_4788_, v_stx_4787_);
    v___x_4791_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4791_, 0, v___x_4789_);
    crate::leanh::lean_ctor_set(v___x_4791_, 1, v___x_4790_);
    return v___x_4791_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_setCur___redArg(
    mut v_t_4792_: *mut crate::leanh::LeanObject,
    mut v_stx_4793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyGet_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyGet_4794_ = crate::leanh::lean_ctor_get(v_t_4792_, 2);
    crate::leanh::lean_inc(v_modifyGet_4794_);
    crate::leanh::lean_dec_ref(v_t_4792_);
    v___f_4795_ = crate::leanh::lean_alloc_closure(
        l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4795_, 0, v_stx_4793_);
    v___x_4796_ =
        crate::leanh::lean_apply_2(v_modifyGet_4794_, crate::leanh::lean_box(0), v___f_4795_);
    return v___x_4796_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_setCur(
    mut v_m_4797_: *mut crate::leanh::LeanObject,
    mut v_t_4798_: *mut crate::leanh::LeanObject,
    mut v_stx_4799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4800_ = l_Lean_Syntax_MonadTraverser_setCur___redArg(v_t_4798_, v_stx_4799_);
    return v___x_4800_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0(
    mut v_idx_4801_: *mut crate::leanh::LeanObject,
    mut v_s_4802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4803_ = crate::leanh::lean_box(0);
    v___x_4804_ = l_Lean_Syntax_Traverser_down(v_s_4802_, v_idx_4801_);
    v___x_4805_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4805_, 0, v___x_4803_);
    crate::leanh::lean_ctor_set(v___x_4805_, 1, v___x_4804_);
    return v___x_4805_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goDown___redArg(
    mut v_t_4806_: *mut crate::leanh::LeanObject,
    mut v_idx_4807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyGet_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyGet_4808_ = crate::leanh::lean_ctor_get(v_t_4806_, 2);
    crate::leanh::lean_inc(v_modifyGet_4808_);
    crate::leanh::lean_dec_ref(v_t_4806_);
    v___f_4809_ = crate::leanh::lean_alloc_closure(
        l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4809_, 0, v_idx_4807_);
    v___x_4810_ =
        crate::leanh::lean_apply_2(v_modifyGet_4808_, crate::leanh::lean_box(0), v___f_4809_);
    return v___x_4810_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goDown(
    mut v_m_4811_: *mut crate::leanh::LeanObject,
    mut v_t_4812_: *mut crate::leanh::LeanObject,
    mut v_idx_4813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4814_ = l_Lean_Syntax_MonadTraverser_goDown___redArg(v_t_4812_, v_idx_4813_);
    return v___x_4814_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goUp___redArg___lam__0(
    mut v_s_4815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4816_ = crate::leanh::lean_box(0);
    v___x_4817_ = l_Lean_Syntax_Traverser_up(v_s_4815_);
    v___x_4818_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4818_, 0, v___x_4816_);
    crate::leanh::lean_ctor_set(v___x_4818_, 1, v___x_4817_);
    return v___x_4818_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goUp___redArg(
    mut v_t_4820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyGet_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyGet_4821_ = crate::leanh::lean_ctor_get(v_t_4820_, 2);
    crate::leanh::lean_inc(v_modifyGet_4821_);
    crate::leanh::lean_dec_ref(v_t_4820_);
    v___f_4822_ = l_Lean_Syntax_MonadTraverser_goUp___redArg___closed__0;
    v___x_4823_ =
        crate::leanh::lean_apply_2(v_modifyGet_4821_, crate::leanh::lean_box(0), v___f_4822_);
    return v___x_4823_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goUp(
    mut v_m_4824_: *mut crate::leanh::LeanObject,
    mut v_t_4825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4826_ = l_Lean_Syntax_MonadTraverser_goUp___redArg(v_t_4825_);
    return v___x_4826_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goLeft___redArg___lam__0(
    mut v_s_4827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4828_ = crate::leanh::lean_box(0);
    v___x_4829_ = l_Lean_Syntax_Traverser_left(v_s_4827_);
    v___x_4830_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4830_, 0, v___x_4828_);
    crate::leanh::lean_ctor_set(v___x_4830_, 1, v___x_4829_);
    return v___x_4830_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goLeft___redArg(
    mut v_t_4832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyGet_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyGet_4833_ = crate::leanh::lean_ctor_get(v_t_4832_, 2);
    crate::leanh::lean_inc(v_modifyGet_4833_);
    crate::leanh::lean_dec_ref(v_t_4832_);
    v___f_4834_ = l_Lean_Syntax_MonadTraverser_goLeft___redArg___closed__0;
    v___x_4835_ =
        crate::leanh::lean_apply_2(v_modifyGet_4833_, crate::leanh::lean_box(0), v___f_4834_);
    return v___x_4835_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goLeft(
    mut v_m_4836_: *mut crate::leanh::LeanObject,
    mut v_t_4837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4838_ = l_Lean_Syntax_MonadTraverser_goLeft___redArg(v_t_4837_);
    return v___x_4838_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goRight___redArg___lam__0(
    mut v_s_4839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4840_ = crate::leanh::lean_box(0);
    v___x_4841_ = l_Lean_Syntax_Traverser_right(v_s_4839_);
    v___x_4842_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4842_, 0, v___x_4840_);
    crate::leanh::lean_ctor_set(v___x_4842_, 1, v___x_4841_);
    return v___x_4842_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goRight___redArg(
    mut v_t_4844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyGet_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyGet_4845_ = crate::leanh::lean_ctor_get(v_t_4844_, 2);
    crate::leanh::lean_inc(v_modifyGet_4845_);
    crate::leanh::lean_dec_ref(v_t_4844_);
    v___f_4846_ = l_Lean_Syntax_MonadTraverser_goRight___redArg___closed__0;
    v___x_4847_ =
        crate::leanh::lean_apply_2(v_modifyGet_4845_, crate::leanh::lean_box(0), v___f_4846_);
    return v___x_4847_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goRight(
    mut v_m_4848_: *mut crate::leanh::LeanObject,
    mut v_t_4849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4850_ = l_Lean_Syntax_MonadTraverser_goRight___redArg(v_t_4849_);
    return v___x_4850_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(
    mut v_toPure_4851_: *mut crate::leanh::LeanObject,
    mut v_st_4852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_idxs_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: u8 = 0;
    v_idxs_4853_ = crate::leanh::lean_ctor_get(v_st_4852_, 2);
    v___x_4854_ = lean_array_get_size(v_idxs_4853_);
    v___x_4855_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4856_ = lean_nat_sub(v___x_4854_, v___x_4855_);
    v___x_4857_ = lean_nat_dec_lt(v___x_4856_, v___x_4854_);
    if v___x_4857_ == 0 {
        let mut v___x_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_4856_);
        v___x_4858_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_4859_ =
            crate::leanh::lean_apply_2(v_toPure_4851_, crate::leanh::lean_box(0), v___x_4858_);
        return v___x_4859_;
    } else {
        let mut v___x_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4860_ = lean_array_fget_borrowed(v_idxs_4853_, v___x_4856_);
        crate::leanh::lean_dec(v___x_4856_);
        crate::leanh::lean_inc(v___x_4860_);
        v___x_4861_ =
            crate::leanh::lean_apply_2(v_toPure_4851_, crate::leanh::lean_box(0), v___x_4860_);
        return v___x_4861_;
    }
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed(
    mut v_toPure_4862_: *mut crate::leanh::LeanObject,
    mut v_st_4863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4864_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(v_toPure_4862_, v_st_4863_);
    crate::leanh::lean_dec_ref(v_st_4863_);
    return v_res_4864_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getIdx___redArg(
    mut v_inst_4865_: *mut crate::leanh::LeanObject,
    mut v_t_4866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4867_ = crate::leanh::lean_ctor_get(v_inst_4865_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4867_);
    v_toBind_4868_ = crate::leanh::lean_ctor_get(v_inst_4865_, 1);
    crate::leanh::lean_inc(v_toBind_4868_);
    crate::leanh::lean_dec_ref(v_inst_4865_);
    v_get_4869_ = crate::leanh::lean_ctor_get(v_t_4866_, 0);
    crate::leanh::lean_inc(v_get_4869_);
    crate::leanh::lean_dec_ref(v_t_4866_);
    v_toPure_4870_ = crate::leanh::lean_ctor_get(v_toApplicative_4867_, 1);
    crate::leanh::lean_inc(v_toPure_4870_);
    crate::leanh::lean_dec_ref(v_toApplicative_4867_);
    v___f_4871_ = crate::leanh::lean_alloc_closure(
        l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4871_, 0, v_toPure_4870_);
    v___x_4872_ = crate::leanh::lean_apply_4(
        v_toBind_4868_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_get_4869_,
        v___f_4871_,
    );
    return v___x_4872_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getIdx(
    mut v_m_4873_: *mut crate::leanh::LeanObject,
    mut v_inst_4874_: *mut crate::leanh::LeanObject,
    mut v_t_4875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4876_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg(v_inst_4874_, v_t_4875_);
    return v___x_4876_;
}
pub unsafe fn l_Lean_SyntaxNode_getIdAt(
    mut v_n_4877_: *mut crate::leanh::LeanObject,
    mut v_i_4878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_args_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_args_4879_ = crate::leanh::lean_ctor_get(v_n_4877_, 2);
    v___x_4880_ = crate::leanh::lean_box(0);
    v___x_4881_ = lean_array_get_borrowed(v___x_4880_, v_args_4879_, v_i_4878_);
    v___x_4882_ = l_Lean_Syntax_getId(v___x_4881_);
    return v___x_4882_;
}
pub unsafe fn l_Lean_SyntaxNode_getIdAt___boxed(
    mut v_n_4883_: *mut crate::leanh::LeanObject,
    mut v_i_4884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4885_ = l_Lean_SyntaxNode_getIdAt(v_n_4883_, v_i_4884_);
    crate::leanh::lean_dec(v_i_4884_);
    crate::leanh::lean_dec(v_n_4883_);
    return v_res_4885_;
}
pub unsafe fn l_Lean_mkListNode(
    mut v_args_4886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4887_ = l_Lean_Syntax_asNode___closed__2;
    v___x_4888_ = crate::leanh::lean_box(2);
    v___x_4889_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4889_, 0, v___x_4888_);
    crate::leanh::lean_ctor_set(v___x_4889_, 1, v___x_4887_);
    crate::leanh::lean_ctor_set(v___x_4889_, 2, v_args_4886_);
    return v___x_4889_;
}
pub unsafe fn l_Lean_Syntax_isQuot(mut v_x_4895_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4895_) == 1 {
        let mut v_kind_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_kind_4896_ = crate::leanh::lean_ctor_get(v_x_4895_, 1);
        if crate::leanh::lean_obj_tag(v_kind_4896_) == 1 {
            let mut v_pre_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_str_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4900_: u8 = 0;
            v_pre_4897_ = crate::leanh::lean_ctor_get(v_kind_4896_, 0);
            v_str_4898_ = crate::leanh::lean_ctor_get(v_kind_4896_, 1);
            v___x_4899_ = l_Lean_Syntax_isQuot___closed__0;
            v___x_4900_ = lean_string_dec_eq(v_str_4898_, v___x_4899_);
            if v___x_4900_ == 0 {
                let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4902_: u8 = 0;
                v___x_4901_ = l_Lean_Syntax_isQuot___closed__1;
                v___x_4902_ = lean_string_dec_eq(v_str_4898_, v___x_4901_);
                if v___x_4902_ == 0 {
                    return v___x_4902_;
                } else {
                    if crate::leanh::lean_obj_tag(v_pre_4897_) == 1 {
                        let mut v_pre_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_4903_ = crate::leanh::lean_ctor_get(v_pre_4897_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_4903_) == 1 {
                            let mut v_pre_4904_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            v_pre_4904_ = crate::leanh::lean_ctor_get(v_pre_4903_, 0);
                            if crate::leanh::lean_obj_tag(v_pre_4904_) == 1 {
                                let mut v_pre_4905_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                v_pre_4905_ = crate::leanh::lean_ctor_get(v_pre_4904_, 0);
                                if crate::leanh::lean_obj_tag(v_pre_4905_) == 0 {
                                    let mut v_str_4906_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v_str_4907_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v_str_4908_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_4909_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_4910_: u8 = 0;
                                    v_str_4906_ = crate::leanh::lean_ctor_get(v_pre_4897_, 1);
                                    v_str_4907_ = crate::leanh::lean_ctor_get(v_pre_4903_, 1);
                                    v_str_4908_ = crate::leanh::lean_ctor_get(v_pre_4904_, 1);
                                    v___x_4909_ = l_Lean_Syntax_isQuot___closed__2;
                                    v___x_4910_ = lean_string_dec_eq(v_str_4908_, v___x_4909_);
                                    if v___x_4910_ == 0 {
                                        return v___x_4910_;
                                    } else {
                                        let mut v___x_4911_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_4912_: u8 = 0;
                                        v___x_4911_ = l_Lean_Syntax_isQuot___closed__3;
                                        v___x_4912_ = lean_string_dec_eq(v_str_4907_, v___x_4911_);
                                        if v___x_4912_ == 0 {
                                            return v___x_4912_;
                                        } else {
                                            let mut v___x_4913_: *mut crate::leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_4914_: u8 = 0;
                                            v___x_4913_ = l_Lean_Syntax_isQuot___closed__4;
                                            v___x_4914_ =
                                                lean_string_dec_eq(v_str_4906_, v___x_4913_);
                                            return v___x_4914_;
                                        }
                                    }
                                } else {
                                    return v___x_4900_;
                                }
                            } else {
                                return v___x_4900_;
                            }
                        } else {
                            return v___x_4900_;
                        }
                    } else {
                        return v___x_4900_;
                    }
                }
            } else {
                return v___x_4900_;
            }
        } else {
            let mut v___x_4915_: u8 = 0;
            v___x_4915_ = 0;
            return v___x_4915_;
        }
    } else {
        let mut v___x_4916_: u8 = 0;
        v___x_4916_ = 0;
        return v___x_4916_;
    }
}
pub unsafe fn l_Lean_Syntax_isQuot___boxed(
    mut v_x_4917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4918_: u8 = 0;
    let mut v_r_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4918_ = l_Lean_Syntax_isQuot(v_x_4917_);
    crate::leanh::lean_dec(v_x_4917_);
    v_r_4919_ = crate::leanh::lean_box((v_res_4918_) as usize);
    return v_r_4919_;
}
pub unsafe fn l_Lean_Syntax_getQuotContent(
    mut v_stx_4925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: u8 = 0;
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: u8 = 0;
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4926_ = l_Lean_Syntax_getNumArgs(v_stx_4925_);
                v___x_4927_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4935_ = lean_nat_dec_eq(v___x_4926_, v___x_4927_);
                crate::leanh::lean_dec(v___x_4926_);
                if v___x_4935_ == 0 {
                    v___y_4929_ = v_stx_4925_;
                    state = 1;
                    continue;
                } else {
                    v___x_4936_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4937_ = l_Lean_Syntax_getArg(v_stx_4925_, v___x_4936_);
                    crate::leanh::lean_dec(v_stx_4925_);
                    v___y_4929_ = v___x_4937_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4930_ = l_Lean_Syntax_getQuotContent___closed__0;
                crate::leanh::lean_inc(v___y_4929_);
                v___x_4931_ = l_Lean_Syntax_isOfKind(v___y_4929_, v___x_4930_);
                if v___x_4931_ == 0 {
                    v___x_4932_ = l_Lean_Syntax_getArg(v___y_4929_, v___x_4927_);
                    crate::leanh::lean_dec(v___y_4929_);
                    return v___x_4932_;
                } else {
                    v___x_4933_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_4934_ = l_Lean_Syntax_getArg(v___y_4929_, v___x_4933_);
                    crate::leanh::lean_dec(v___y_4929_);
                    return v___x_4934_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_isAntiquot(mut v_x_4939_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4939_) == 1 {
        let mut v_kind_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_kind_4940_ = crate::leanh::lean_ctor_get(v_x_4939_, 1);
        if crate::leanh::lean_obj_tag(v_kind_4940_) == 1 {
            let mut v_str_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4943_: u8 = 0;
            v_str_4941_ = crate::leanh::lean_ctor_get(v_kind_4940_, 1);
            v___x_4942_ = l_Lean_Syntax_isAntiquot___closed__0;
            v___x_4943_ = lean_string_dec_eq(v_str_4941_, v___x_4942_);
            return v___x_4943_;
        } else {
            let mut v___x_4944_: u8 = 0;
            v___x_4944_ = 0;
            return v___x_4944_;
        }
    } else {
        let mut v___x_4945_: u8 = 0;
        v___x_4945_ = 0;
        return v___x_4945_;
    }
}
pub unsafe fn l_Lean_Syntax_isAntiquot___boxed(
    mut v_x_4946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4947_: u8 = 0;
    let mut v_r_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4947_ = l_Lean_Syntax_isAntiquot(v_x_4946_);
    crate::leanh::lean_dec(v_x_4946_);
    v_r_4948_ = crate::leanh::lean_box((v_res_4947_) as usize);
    return v_r_4948_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(
    mut v___y_4949_: u8,
    mut v___x_4950_: u8,
    mut v_as_4951_: *mut crate::leanh::LeanObject,
    mut v_i_4952_: usize,
    mut v_stop_4953_: usize,
) -> u8 {
    let mut v___x_4954_: u8 = 0;
    let mut v___x_4955_: u8 = 0;
    let mut v___y_4957_: u8 = 0;
    let mut v___x_4958_: usize = 0;
    let mut v___x_4959_: usize = 0;
    let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: u8 = 0;
    let mut v___x_4963_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4954_ = lean_usize_dec_eq(v_i_4952_, v_stop_4953_);
                if v___x_4954_ == 0 {
                    v___x_4955_ = 1;
                    v___x_4961_ = lean_array_uget_borrowed(v_as_4951_, v_i_4952_);
                    v___x_4962_ = l_Lean_Syntax_isAntiquot(v___x_4961_);
                    if v___x_4962_ == 0 {
                        v___y_4957_ = v___y_4949_;
                        state = 1;
                        continue;
                    } else {
                        v___y_4957_ = v___x_4950_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_4963_ = 0;
                    return v___x_4963_;
                }
            }
            1 => {
                if v___y_4957_ == 0 {
                    v___x_4958_ = 1usize;
                    v___x_4959_ = lean_usize_add(v_i_4952_, v___x_4958_);
                    v_i_4952_ = v___x_4959_;
                    state = 0;
                    continue;
                } else {
                    return v___x_4955_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0___boxed(
    mut v___y_4964_: *mut crate::leanh::LeanObject,
    mut v___x_4965_: *mut crate::leanh::LeanObject,
    mut v_as_4966_: *mut crate::leanh::LeanObject,
    mut v_i_4967_: *mut crate::leanh::LeanObject,
    mut v_stop_4968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_340__boxed_4969_: u8 = 0;
    let mut v___x_341__boxed_4970_: u8 = 0;
    let mut v_i_boxed_4971_: usize = 0;
    let mut v_stop_boxed_4972_: usize = 0;
    let mut v_res_4973_: u8 = 0;
    let mut v_r_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_340__boxed_4969_ = (crate::leanh::lean_unbox(v___y_4964_) as u8);
    v___x_341__boxed_4970_ = (crate::leanh::lean_unbox(v___x_4965_) as u8);
    v_i_boxed_4971_ = crate::leanh::lean_unbox_usize(v_i_4967_);
    crate::leanh::lean_dec(v_i_4967_);
    v_stop_boxed_4972_ = crate::leanh::lean_unbox_usize(v_stop_4968_);
    crate::leanh::lean_dec(v_stop_4968_);
    v_res_4973_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___y_340__boxed_4969_, v___x_341__boxed_4970_, v_as_4966_, v_i_boxed_4971_, v_stop_boxed_4972_);
    crate::leanh::lean_dec_ref(v_as_4966_);
    v_r_4974_ = crate::leanh::lean_box((v_res_4973_) as usize);
    return v_r_4974_;
}
pub unsafe fn l_Lean_Syntax_isAntiquots(mut v_stx_4975_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_4976_: u8 = 0;
    let mut v___y_4978_: u8 = 0;
    let mut v___x_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: u8 = 0;
    let mut v___x_4983_: usize = 0;
    let mut v___x_4984_: usize = 0;
    let mut v___x_4985_: u8 = 0;
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: u8 = 0;
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4976_ = l_Lean_Syntax_isAntiquot(v_stx_4975_);
                if v___x_4976_ == 0 {
                    v___x_4986_ =
                        l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1;
                    crate::leanh::lean_inc(v_stx_4975_);
                    v___x_4987_ = l_Lean_Syntax_isOfKind(v_stx_4975_, v___x_4986_);
                    if v___x_4987_ == 0 {
                        v___y_4978_ = v___x_4987_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4988_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4989_ = l_Lean_Syntax_getNumArgs(v_stx_4975_);
                        v___x_4990_ = lean_nat_dec_lt(v___x_4988_, v___x_4989_);
                        crate::leanh::lean_dec(v___x_4989_);
                        v___y_4978_ = v___x_4990_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_stx_4975_);
                    return v___x_4976_;
                }
            }
            1 => {
                if v___y_4978_ == 0 {
                    crate::leanh::lean_dec(v_stx_4975_);
                    return v___y_4978_;
                } else {
                    v___x_4979_ = l_Lean_Syntax_getArgs(v_stx_4975_);
                    crate::leanh::lean_dec(v_stx_4975_);
                    v___x_4980_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4981_ = lean_array_get_size(v___x_4979_);
                    v___x_4982_ = lean_nat_dec_lt(v___x_4980_, v___x_4981_);
                    if v___x_4982_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_4979_);
                        return v___y_4978_;
                    } else {
                        if v___x_4982_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_4979_);
                            return v___y_4978_;
                        } else {
                            v___x_4983_ = 0usize;
                            v___x_4984_ = lean_usize_of_nat(v___x_4981_);
                            v___x_4985_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___y_4978_, v___x_4976_, v___x_4979_, v___x_4983_, v___x_4984_);
                            crate::leanh::lean_dec_ref(v___x_4979_);
                            if v___x_4985_ == 0 {
                                return v___y_4978_;
                            } else {
                                return v___x_4976_;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_isAntiquots___boxed(
    mut v_stx_4991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4992_: u8 = 0;
    let mut v_r_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4992_ = l_Lean_Syntax_isAntiquots(v_stx_4991_);
    v_r_4993_ = crate::leanh::lean_box((v_res_4992_) as usize);
    return v_r_4993_;
}
pub unsafe fn l_Lean_Syntax_getCanonicalAntiquot(
    mut v_stx_4994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: u8 = 0;
    v___x_4995_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1;
    crate::leanh::lean_inc(v_stx_4994_);
    v___x_4996_ = l_Lean_Syntax_isOfKind(v_stx_4994_, v___x_4995_);
    if v___x_4996_ == 0 {
        return v_stx_4994_;
    } else {
        let mut v___x_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4997_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_4998_ = l_Lean_Syntax_getArg(v_stx_4994_, v___x_4997_);
        crate::leanh::lean_dec(v_stx_4994_);
        return v___x_4998_;
    }
}
pub unsafe fn _init_l_Lean_Syntax_mkAntiquotNode___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5000_ = l_Lean_Syntax_mkAntiquotNode___closed__0;
    v___x_5001_ = l_Lean_mkAtom(v___x_5000_);
    return v___x_5001_;
}
pub unsafe fn _init_l_Lean_Syntax_mkAntiquotNode___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5004_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotNode___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotNode___closed__1_once),
        _init_l_Lean_Syntax_mkAntiquotNode___closed__1,
    );
    v___x_5005_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_5006_ = lean_mk_empty_array_with_capacity(v___x_5005_);
    v___x_5007_ = lean_array_push(v___x_5006_, v___x_5004_);
    return v___x_5007_;
}
pub unsafe fn _init_l_Lean_Syntax_mkAntiquotNode___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5015_ = l_Lean_Syntax_mkAntiquotNode___closed__8;
    v___x_5016_ = l_Lean_mkAtom(v___x_5015_);
    return v___x_5016_;
}
pub unsafe fn _init_l_Lean_Syntax_mkAntiquotNode___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5017_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotNode___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotNode___closed__9_once),
        _init_l_Lean_Syntax_mkAntiquotNode___closed__9,
    );
    v___x_5018_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_5019_ = lean_mk_empty_array_with_capacity(v___x_5018_);
    v___x_5020_ = lean_array_push(v___x_5019_, v___x_5017_);
    return v___x_5020_;
}
pub unsafe fn _init_l_Lean_Syntax_mkAntiquotNode___closed__16() -> *mut crate::leanh::LeanObject {
    let mut v___x_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5031_ = l_Lean_Syntax_mkAntiquotNode___closed__15;
    v___x_5032_ = l_Lean_mkAtom(v___x_5031_);
    return v___x_5032_;
}
pub unsafe fn _init_l_Lean_Syntax_mkAntiquotNode___closed__18() -> *mut crate::leanh::LeanObject {
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5034_ = l_Lean_Syntax_mkAntiquotNode___closed__17;
    v___x_5035_ = l_Lean_mkAtom(v___x_5034_);
    return v___x_5035_;
}
pub unsafe fn _init_l_Lean_Syntax_mkAntiquotNode___closed__19() -> *mut crate::leanh::LeanObject {
    let mut v___x_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5036_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotNode___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotNode___closed__16_once),
        _init_l_Lean_Syntax_mkAntiquotNode___closed__16,
    );
    v___x_5037_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_5038_ = lean_mk_empty_array_with_capacity(v___x_5037_);
    v___x_5039_ = lean_array_push(v___x_5038_, v___x_5036_);
    return v___x_5039_;
}
pub unsafe fn l_Lean_Syntax_mkAntiquotNode(
    mut v_kind_5040_: *mut crate::leanh::LeanObject,
    mut v_term_5041_: *mut crate::leanh::LeanObject,
    mut v_nesting_5042_: *mut crate::leanh::LeanObject,
    mut v_name_5043_: *mut crate::leanh::LeanObject,
    mut v_isPseudoKind_5044_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nesting_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: u8 = 0;
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: u8 = 0;
    let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5045_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotNode___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotNode___closed__1_once),
                    _init_l_Lean_Syntax_mkAntiquotNode___closed__1,
                );
                v___x_5046_ = lean_mk_array(v_nesting_5042_, v___x_5045_);
                v___x_5047_ = l_Lean_Syntax_asNode___closed__2;
                v___x_5048_ = crate::leanh::lean_box(2);
                v_nesting_5049_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v_nesting_5049_, 0, v___x_5048_);
                crate::leanh::lean_ctor_set(v_nesting_5049_, 1, v___x_5047_);
                crate::leanh::lean_ctor_set(v_nesting_5049_, 2, v___x_5046_);
                v___x_5076_ = l_Lean_Syntax_isIdent(v_term_5041_);
                if v___x_5076_ == 0 {
                    v___x_5077_ = l_Lean_Syntax_mkAntiquotNode___closed__12;
                    crate::leanh::lean_inc(v_term_5041_);
                    v___x_5078_ = l_Lean_Syntax_isOfKind(v_term_5041_, v___x_5077_);
                    if v___x_5078_ == 0 {
                        v___x_5079_ = l_Lean_Syntax_mkAntiquotNode___closed__14;
                        v___x_5080_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotNode___closed__18),
                            core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotNode___closed__18_once),
                            _init_l_Lean_Syntax_mkAntiquotNode___closed__18,
                        );
                        v___x_5081_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotNode___closed__19),
                            core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotNode___closed__19_once),
                            _init_l_Lean_Syntax_mkAntiquotNode___closed__19,
                        );
                        v___x_5082_ = lean_array_push(v___x_5081_, v_term_5041_);
                        v___x_5083_ = lean_array_push(v___x_5082_, v___x_5080_);
                        v___x_5084_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5084_, 0, v___x_5048_);
                        crate::leanh::lean_ctor_set(v___x_5084_, 1, v___x_5079_);
                        crate::leanh::lean_ctor_set(v___x_5084_, 2, v___x_5083_);
                        v___y_5068_ = v___x_5084_;
                        state = 3;
                        continue;
                    } else {
                        v___x_5085_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_5086_ = l_Lean_Syntax_getArg(v_term_5041_, v___x_5085_);
                        crate::leanh::lean_dec(v_term_5041_);
                        v___y_5068_ = v___x_5086_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___y_5068_ = v_term_5041_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_5053_);
                v___x_5054_ = l_Lean_Name_append(v_kind_5040_, v___y_5053_);
                v___x_5055_ = l_Lean_Syntax_mkAntiquotNode___closed__2;
                v___x_5056_ = l_Lean_Name_append(v___x_5054_, v___x_5055_);
                v___x_5057_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotNode___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotNode___closed__3_once),
                    _init_l_Lean_Syntax_mkAntiquotNode___closed__3,
                );
                v___x_5058_ = lean_array_push(v___x_5057_, v_nesting_5049_);
                v___x_5059_ = lean_array_push(v___x_5058_, v___y_5051_);
                v___x_5060_ = lean_array_push(v___x_5059_, v___y_5052_);
                v___x_5061_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5061_, 0, v___x_5048_);
                crate::leanh::lean_ctor_set(v___x_5061_, 1, v___x_5056_);
                crate::leanh::lean_ctor_set(v___x_5061_, 2, v___x_5060_);
                return v___x_5061_;
            }
            2 => {
                if v_isPseudoKind_5044_ == 0 {
                    v___x_5065_ = crate::leanh::lean_box(0);
                    v___y_5051_ = v___y_5063_;
                    v___y_5052_ = v___y_5064_;
                    v___y_5053_ = v___x_5065_;
                    state = 1;
                    continue;
                } else {
                    v___x_5066_ = l_Lean_Syntax_mkAntiquotNode___closed__5;
                    v___y_5051_ = v___y_5063_;
                    v___y_5052_ = v___y_5064_;
                    v___y_5053_ = v___x_5066_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_name_5043_) == 0 {
                    v___x_5069_ = l_Lean_Syntax_asNode___closed__3;
                    v___y_5063_ = v___y_5068_;
                    v___y_5064_ = v___x_5069_;
                    state = 2;
                    continue;
                } else {
                    v_val_5070_ = crate::leanh::lean_ctor_get(v_name_5043_, 0);
                    crate::leanh::lean_inc(v_val_5070_);
                    crate::leanh::lean_dec_ref_known(v_name_5043_, 1);
                    v___x_5071_ = l_Lean_Syntax_mkAntiquotNode___closed__7;
                    v___x_5072_ = l_Lean_mkAtom(v_val_5070_);
                    v___x_5073_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotNode___closed__10),
                        core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotNode___closed__10_once),
                        _init_l_Lean_Syntax_mkAntiquotNode___closed__10,
                    );
                    v___x_5074_ = lean_array_push(v___x_5073_, v___x_5072_);
                    v___x_5075_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5075_, 0, v___x_5048_);
                    crate::leanh::lean_ctor_set(v___x_5075_, 1, v___x_5071_);
                    crate::leanh::lean_ctor_set(v___x_5075_, 2, v___x_5074_);
                    v___y_5063_ = v___y_5068_;
                    v___y_5064_ = v___x_5075_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_mkAntiquotNode___boxed(
    mut v_kind_5087_: *mut crate::leanh::LeanObject,
    mut v_term_5088_: *mut crate::leanh::LeanObject,
    mut v_nesting_5089_: *mut crate::leanh::LeanObject,
    mut v_name_5090_: *mut crate::leanh::LeanObject,
    mut v_isPseudoKind_5091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isPseudoKind_boxed_5092_: u8 = 0;
    let mut v_res_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isPseudoKind_boxed_5092_ = (crate::leanh::lean_unbox(v_isPseudoKind_5091_) as u8);
    v_res_5093_ = l_Lean_Syntax_mkAntiquotNode(
        v_kind_5087_,
        v_term_5088_,
        v_nesting_5089_,
        v_name_5090_,
        v_isPseudoKind_boxed_5092_,
    );
    return v_res_5093_;
}
pub unsafe fn l_Lean_Syntax_isEscapedAntiquot(
    mut v_stx_5094_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: u8 = 0;
    v___x_5095_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_5096_ = l_Lean_Syntax_getArg(v_stx_5094_, v___x_5095_);
    v___x_5097_ = l_Lean_Syntax_getArgs(v___x_5096_);
    crate::leanh::lean_dec(v___x_5096_);
    v___x_5098_ = lean_array_get_size(v___x_5097_);
    crate::leanh::lean_dec_ref(v___x_5097_);
    v___x_5099_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5100_ = lean_nat_dec_eq(v___x_5098_, v___x_5099_);
    if v___x_5100_ == 0 {
        let mut v___x_5101_: u8 = 0;
        v___x_5101_ = 1;
        return v___x_5101_;
    } else {
        let mut v___x_5102_: u8 = 0;
        v___x_5102_ = 0;
        return v___x_5102_;
    }
}
pub unsafe fn l_Lean_Syntax_isEscapedAntiquot___boxed(
    mut v_stx_5103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5104_: u8 = 0;
    let mut v_r_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5104_ = l_Lean_Syntax_isEscapedAntiquot(v_stx_5103_);
    crate::leanh::lean_dec(v_stx_5103_);
    v_r_5105_ = crate::leanh::lean_box((v_res_5104_) as usize);
    return v_r_5105_;
}
pub unsafe fn l_Lean_Syntax_unescapeAntiquot(
    mut v_stx_5106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5107_: u8 = 0;
    v___x_5107_ = l_Lean_Syntax_isAntiquot(v_stx_5106_);
    if v___x_5107_ == 0 {
        return v_stx_5106_;
    } else {
        let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5108_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_5109_ = l_Lean_Syntax_getArg(v_stx_5106_, v___x_5108_);
        v___x_5110_ = l_Lean_Syntax_getArgs(v___x_5109_);
        crate::leanh::lean_dec(v___x_5109_);
        v___x_5111_ = lean_array_pop(v___x_5110_);
        v___x_5112_ = l_Lean_Syntax_asNode___closed__2;
        v___x_5113_ = crate::leanh::lean_box(2);
        v___x_5114_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5114_, 0, v___x_5113_);
        crate::leanh::lean_ctor_set(v___x_5114_, 1, v___x_5112_);
        crate::leanh::lean_ctor_set(v___x_5114_, 2, v___x_5111_);
        v___x_5115_ = l_Lean_Syntax_setArg(v_stx_5106_, v___x_5108_, v___x_5114_);
        return v___x_5115_;
    }
}
pub unsafe fn l_Lean_Syntax_getAntiquotTerm(
    mut v_stx_5116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: u8 = 0;
    let mut v___x_5120_: u8 = 0;
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: u8 = 0;
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5129_ = l_Lean_Syntax_isAntiquot(v_stx_5116_);
                if v___x_5129_ == 0 {
                    v___x_5130_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_5131_ = l_Lean_Syntax_getArg(v_stx_5116_, v___x_5130_);
                    v___y_5118_ = v___x_5131_;
                    state = 1;
                    continue;
                } else {
                    v___x_5132_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_5133_ = l_Lean_Syntax_getArg(v_stx_5116_, v___x_5132_);
                    v___y_5118_ = v___x_5133_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5119_ = l_Lean_Syntax_isIdent(v___y_5118_);
                if v___x_5119_ == 0 {
                    v___x_5120_ = l_Lean_Syntax_isAtom(v___y_5118_);
                    if v___x_5120_ == 0 {
                        v___x_5121_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5122_ = l_Lean_Syntax_getArg(v___y_5118_, v___x_5121_);
                        crate::leanh::lean_dec(v___y_5118_);
                        return v___x_5122_;
                    } else {
                        v___x_5123_ = l_Lean_Syntax_mkAntiquotNode___closed__12;
                        v___x_5124_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5125_ = lean_mk_empty_array_with_capacity(v___x_5124_);
                        v___x_5126_ = lean_array_push(v___x_5125_, v___y_5118_);
                        v___x_5127_ = crate::leanh::lean_box(2);
                        v___x_5128_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5128_, 0, v___x_5127_);
                        crate::leanh::lean_ctor_set(v___x_5128_, 1, v___x_5123_);
                        crate::leanh::lean_ctor_set(v___x_5128_, 2, v___x_5126_);
                        return v___x_5128_;
                    }
                } else {
                    return v___y_5118_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_getAntiquotTerm___boxed(
    mut v_stx_5134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5135_ = l_Lean_Syntax_getAntiquotTerm(v_stx_5134_);
    crate::leanh::lean_dec(v_stx_5134_);
    return v_res_5135_;
}
pub unsafe fn l_Lean_Syntax_antiquotKind_x3f(
    mut v_x_5136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: u8 = 0;
    let mut v___x_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: u8 = 0;
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: u8 = 0;
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: u8 = 0;
    let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: u8 = 0;
    let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5136_) == 1 {
                    v_kind_5137_ = crate::leanh::lean_ctor_get(v_x_5136_, 1);
                    if crate::leanh::lean_obj_tag(v_kind_5137_) == 1 {
                        v_pre_5138_ = crate::leanh::lean_ctor_get(v_kind_5137_, 0);
                        v_str_5139_ = crate::leanh::lean_ctor_get(v_kind_5137_, 1);
                        if crate::leanh::lean_obj_tag(v_pre_5138_) == 1 {
                            v_pre_5145_ = crate::leanh::lean_ctor_get(v_pre_5138_, 0);
                            v_str_5146_ = crate::leanh::lean_ctor_get(v_pre_5138_, 1);
                            v___x_5147_ = l_Lean_Syntax_mkAntiquotNode___closed__4;
                            v___x_5148_ = lean_string_dec_eq(v_str_5146_, v___x_5147_);
                            if v___x_5148_ == 0 {
                                v___x_5149_ = l_Lean_Syntax_isAntiquot___closed__0;
                                v___x_5150_ = lean_string_dec_eq(v_str_5139_, v___x_5149_);
                                if v___x_5150_ == 0 {
                                    v___x_5151_ = crate::leanh::lean_box(0);
                                    return v___x_5151_;
                                } else {
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___x_5152_ = l_Lean_Syntax_isAntiquot___closed__0;
                                v___x_5153_ = lean_string_dec_eq(v_str_5139_, v___x_5152_);
                                if v___x_5153_ == 0 {
                                    v___x_5154_ = crate::leanh::lean_box(0);
                                    return v___x_5154_;
                                } else {
                                    v___x_5155_ = crate::leanh::lean_box((v___x_5153_) as usize);
                                    crate::leanh::lean_inc(v_pre_5145_);
                                    v___x_5156_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_5156_, 0, v_pre_5145_);
                                    crate::leanh::lean_ctor_set(v___x_5156_, 1, v___x_5155_);
                                    v___x_5157_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_5157_, 0, v___x_5156_);
                                    return v___x_5157_;
                                }
                            }
                        } else {
                            v___x_5158_ = l_Lean_Syntax_isAntiquot___closed__0;
                            v___x_5159_ = lean_string_dec_eq(v_str_5139_, v___x_5158_);
                            if v___x_5159_ == 0 {
                                v___x_5160_ = crate::leanh::lean_box(0);
                                return v___x_5160_;
                            } else {
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v___x_5161_ = crate::leanh::lean_box(0);
                        return v___x_5161_;
                    }
                } else {
                    v___x_5162_ = crate::leanh::lean_box(0);
                    return v___x_5162_;
                }
            }
            1 => {
                v___x_5141_ = 0;
                v___x_5142_ = crate::leanh::lean_box((v___x_5141_) as usize);
                crate::leanh::lean_inc(v_pre_5138_);
                v___x_5143_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5143_, 0, v_pre_5138_);
                crate::leanh::lean_ctor_set(v___x_5143_, 1, v___x_5142_);
                v___x_5144_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5144_, 0, v___x_5143_);
                return v___x_5144_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_antiquotKind_x3f___boxed(
    mut v_x_5163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5164_ = l_Lean_Syntax_antiquotKind_x3f(v_x_5163_);
    crate::leanh::lean_dec(v_x_5163_);
    return v_res_5164_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(
    mut v_as_5165_: *mut crate::leanh::LeanObject,
    mut v_i_5166_: usize,
    mut v_stop_5167_: usize,
    mut v_b_5168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: usize = 0;
    let mut v___x_5172_: usize = 0;
    let mut v___x_5174_: u8 = 0;
    let mut v___x_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5174_ = lean_usize_dec_eq(v_i_5166_, v_stop_5167_);
                if v___x_5174_ == 0 {
                    v___x_5175_ = lean_array_uget_borrowed(v_as_5165_, v_i_5166_);
                    v___x_5176_ = l_Lean_Syntax_antiquotKind_x3f(v___x_5175_);
                    if crate::leanh::lean_obj_tag(v___x_5176_) == 0 {
                        v___y_5170_ = v_b_5168_;
                        state = 1;
                        continue;
                    } else {
                        v_val_5177_ = crate::leanh::lean_ctor_get(v___x_5176_, 0);
                        crate::leanh::lean_inc(v_val_5177_);
                        crate::leanh::lean_dec_ref_known(v___x_5176_, 1);
                        v___x_5178_ = lean_array_push(v_b_5168_, v_val_5177_);
                        v___y_5170_ = v___x_5178_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_5168_;
                }
            }
            1 => {
                v___x_5171_ = 1usize;
                v___x_5172_ = lean_usize_add(v_i_5166_, v___x_5171_);
                v_i_5166_ = v___x_5172_;
                v_b_5168_ = v___y_5170_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0___boxed(
    mut v_as_5179_: *mut crate::leanh::LeanObject,
    mut v_i_5180_: *mut crate::leanh::LeanObject,
    mut v_stop_5181_: *mut crate::leanh::LeanObject,
    mut v_b_5182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5183_: usize = 0;
    let mut v_stop_boxed_5184_: usize = 0;
    let mut v_res_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5183_ = crate::leanh::lean_unbox_usize(v_i_5180_);
    crate::leanh::lean_dec(v_i_5180_);
    v_stop_boxed_5184_ = crate::leanh::lean_unbox_usize(v_stop_5181_);
    crate::leanh::lean_dec(v_stop_5181_);
    v_res_5185_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_5179_, v_i_boxed_5183_, v_stop_boxed_5184_, v_b_5182_);
    crate::leanh::lean_dec_ref(v_as_5179_);
    return v_res_5185_;
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(
    mut v_as_5188_: *mut crate::leanh::LeanObject,
    mut v_start_5189_: *mut crate::leanh::LeanObject,
    mut v_stop_5190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: u8 = 0;
    v___x_5191_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___closed__0;
    v___x_5192_ = lean_nat_dec_lt(v_start_5189_, v_stop_5190_);
    if v___x_5192_ == 0 {
        return v___x_5191_;
    } else {
        let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5194_: u8 = 0;
        v___x_5193_ = lean_array_get_size(v_as_5188_);
        v___x_5194_ = lean_nat_dec_le(v_stop_5190_, v___x_5193_);
        if v___x_5194_ == 0 {
            let mut v___x_5195_: u8 = 0;
            v___x_5195_ = lean_nat_dec_lt(v_start_5189_, v___x_5193_);
            if v___x_5195_ == 0 {
                return v___x_5191_;
            } else {
                let mut v___x_5196_: usize = 0;
                let mut v___x_5197_: usize = 0;
                let mut v___x_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5196_ = lean_usize_of_nat(v_start_5189_);
                v___x_5197_ = lean_usize_of_nat(v___x_5193_);
                v___x_5198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_5188_, v___x_5196_, v___x_5197_, v___x_5191_);
                return v___x_5198_;
            }
        } else {
            let mut v___x_5199_: usize = 0;
            let mut v___x_5200_: usize = 0;
            let mut v___x_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5199_ = lean_usize_of_nat(v_start_5189_);
            v___x_5200_ = lean_usize_of_nat(v_stop_5190_);
            v___x_5201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_5188_, v___x_5199_, v___x_5200_, v___x_5191_);
            return v___x_5201_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___boxed(
    mut v_as_5202_: *mut crate::leanh::LeanObject,
    mut v_start_5203_: *mut crate::leanh::LeanObject,
    mut v_stop_5204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5205_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(
        v_as_5202_,
        v_start_5203_,
        v_stop_5204_,
    );
    crate::leanh::lean_dec(v_stop_5204_);
    crate::leanh::lean_dec(v_start_5203_);
    crate::leanh::lean_dec_ref(v_as_5202_);
    return v_res_5205_;
}
pub unsafe fn l_Lean_Syntax_antiquotKinds(
    mut v_stx_5206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: u8 = 0;
    v___x_5207_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1;
    crate::leanh::lean_inc(v_stx_5206_);
    v___x_5208_ = l_Lean_Syntax_isOfKind(v_stx_5206_, v___x_5207_);
    if v___x_5208_ == 0 {
        let mut v___x_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5209_ = l_Lean_Syntax_antiquotKind_x3f(v_stx_5206_);
        crate::leanh::lean_dec(v_stx_5206_);
        if crate::leanh::lean_obj_tag(v___x_5209_) == 0 {
            let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5210_ = crate::leanh::lean_box(0);
            return v___x_5210_;
        } else {
            let mut v_val_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_5211_ = crate::leanh::lean_ctor_get(v___x_5209_, 0);
            crate::leanh::lean_inc(v_val_5211_);
            crate::leanh::lean_dec_ref_known(v___x_5209_, 1);
            v___x_5212_ = crate::leanh::lean_box(0);
            v___x_5213_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5213_, 0, v_val_5211_);
            crate::leanh::lean_ctor_set(v___x_5213_, 1, v___x_5212_);
            return v___x_5213_;
        }
    } else {
        let mut v___x_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5214_ = l_Lean_Syntax_getArgs(v_stx_5206_);
        crate::leanh::lean_dec(v_stx_5206_);
        v___x_5215_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_5216_ = lean_array_get_size(v___x_5214_);
        v___x_5217_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(
            v___x_5214_,
            v___x_5215_,
            v___x_5216_,
        );
        crate::leanh::lean_dec_ref(v___x_5214_);
        v___x_5218_ = lean_array_to_list(v___x_5217_);
        return v___x_5218_;
    }
}
pub unsafe fn l_Lean_Syntax_antiquotSpliceKind_x3f(
    mut v_x_5220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5220_) == 1 {
        let mut v_kind_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_kind_5221_ = crate::leanh::lean_ctor_get(v_x_5220_, 1);
        if crate::leanh::lean_obj_tag(v_kind_5221_) == 1 {
            let mut v_pre_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_str_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5225_: u8 = 0;
            v_pre_5222_ = crate::leanh::lean_ctor_get(v_kind_5221_, 0);
            v_str_5223_ = crate::leanh::lean_ctor_get(v_kind_5221_, 1);
            v___x_5224_ = l_Lean_Syntax_antiquotSpliceKind_x3f___closed__0;
            v___x_5225_ = lean_string_dec_eq(v_str_5223_, v___x_5224_);
            if v___x_5225_ == 0 {
                let mut v___x_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5226_ = crate::leanh::lean_box(0);
                return v___x_5226_;
            } else {
                let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_inc(v_pre_5222_);
                v___x_5227_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5227_, 0, v_pre_5222_);
                return v___x_5227_;
            }
        } else {
            let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5228_ = crate::leanh::lean_box(0);
            return v___x_5228_;
        }
    } else {
        let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5229_ = crate::leanh::lean_box(0);
        return v___x_5229_;
    }
}
pub unsafe fn l_Lean_Syntax_antiquotSpliceKind_x3f___boxed(
    mut v_x_5230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5231_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_x_5230_);
    crate::leanh::lean_dec(v_x_5230_);
    return v_res_5231_;
}
pub unsafe fn l_Lean_Syntax_isAntiquotSplice(mut v_stx_5232_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5233_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_stx_5232_);
    if crate::leanh::lean_obj_tag(v___x_5233_) == 0 {
        let mut v___x_5234_: u8 = 0;
        v___x_5234_ = 0;
        return v___x_5234_;
    } else {
        let mut v___x_5235_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_5233_, 1);
        v___x_5235_ = 1;
        return v___x_5235_;
    }
}
pub unsafe fn l_Lean_Syntax_isAntiquotSplice___boxed(
    mut v_stx_5236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5237_: u8 = 0;
    let mut v_r_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5237_ = l_Lean_Syntax_isAntiquotSplice(v_stx_5236_);
    crate::leanh::lean_dec(v_stx_5236_);
    v_r_5238_ = crate::leanh::lean_box((v_res_5237_) as usize);
    return v_r_5238_;
}
pub unsafe fn l_Lean_Syntax_getAntiquotSpliceContents(
    mut v_stx_5239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5240_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_5241_ = l_Lean_Syntax_getArg(v_stx_5239_, v___x_5240_);
    v___x_5242_ = l_Lean_Syntax_getArgs(v___x_5241_);
    crate::leanh::lean_dec(v___x_5241_);
    return v___x_5242_;
}
pub unsafe fn l_Lean_Syntax_getAntiquotSpliceContents___boxed(
    mut v_stx_5243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5244_ = l_Lean_Syntax_getAntiquotSpliceContents(v_stx_5243_);
    crate::leanh::lean_dec(v_stx_5243_);
    return v_res_5244_;
}
pub unsafe fn l_Lean_Syntax_getAntiquotSpliceSuffix(
    mut v_stx_5245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5246_: u8 = 0;
    v___x_5246_ = l_Lean_Syntax_isAntiquotSplice(v_stx_5245_);
    if v___x_5246_ == 0 {
        let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5247_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_5248_ = l_Lean_Syntax_getArg(v_stx_5245_, v___x_5247_);
        return v___x_5248_;
    } else {
        let mut v___x_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5249_ = crate::leanh::lean_unsigned_to_nat(5);
        v___x_5250_ = l_Lean_Syntax_getArg(v_stx_5245_, v___x_5249_);
        return v___x_5250_;
    }
}
pub unsafe fn l_Lean_Syntax_getAntiquotSpliceSuffix___boxed(
    mut v_stx_5251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5252_ = l_Lean_Syntax_getAntiquotSpliceSuffix(v_stx_5251_);
    crate::leanh::lean_dec(v_stx_5251_);
    return v_res_5252_;
}
pub unsafe fn _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5257_ = l_Lean_Syntax_mkAntiquotSpliceNode___closed__2;
    v___x_5258_ = l_Lean_mkAtom(v___x_5257_);
    return v___x_5258_;
}
pub unsafe fn _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5260_ = l_Lean_Syntax_mkAntiquotSpliceNode___closed__4;
    v___x_5261_ = l_Lean_mkAtom(v___x_5260_);
    return v___x_5261_;
}
pub unsafe fn _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5262_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotNode___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotNode___closed__1_once),
        _init_l_Lean_Syntax_mkAntiquotNode___closed__1,
    );
    v___x_5263_ = crate::leanh::lean_unsigned_to_nat(6);
    v___x_5264_ = lean_mk_empty_array_with_capacity(v___x_5263_);
    v___x_5265_ = lean_array_push(v___x_5264_, v___x_5262_);
    return v___x_5265_;
}
pub unsafe fn l_Lean_Syntax_mkAntiquotSpliceNode(
    mut v_kind_5266_: *mut crate::leanh::LeanObject,
    mut v_contents_5267_: *mut crate::leanh::LeanObject,
    mut v_suffix_5268_: *mut crate::leanh::LeanObject,
    mut v_nesting_5269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nesting_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5270_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotNode___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotNode___closed__1_once),
        _init_l_Lean_Syntax_mkAntiquotNode___closed__1,
    );
    v___x_5271_ = lean_mk_array(v_nesting_5269_, v___x_5270_);
    v___x_5272_ = l_Lean_Syntax_asNode___closed__2;
    v___x_5273_ = crate::leanh::lean_box(2);
    v_nesting_5274_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v_nesting_5274_, 0, v___x_5273_);
    crate::leanh::lean_ctor_set(v_nesting_5274_, 1, v___x_5272_);
    crate::leanh::lean_ctor_set(v_nesting_5274_, 2, v___x_5271_);
    v___x_5275_ = l_Lean_Syntax_mkAntiquotSpliceNode___closed__1;
    v___x_5276_ = l_Lean_Name_append(v_kind_5266_, v___x_5275_);
    v___x_5277_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotSpliceNode___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotSpliceNode___closed__3_once),
        _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3,
    );
    v___x_5278_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5278_, 0, v___x_5273_);
    crate::leanh::lean_ctor_set(v___x_5278_, 1, v___x_5272_);
    crate::leanh::lean_ctor_set(v___x_5278_, 2, v_contents_5267_);
    v___x_5279_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotSpliceNode___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotSpliceNode___closed__5_once),
        _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5,
    );
    v___x_5280_ = l_Lean_mkAtom(v_suffix_5268_);
    v___x_5281_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotSpliceNode___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Syntax_mkAntiquotSpliceNode___closed__6_once),
        _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6,
    );
    v___x_5282_ = lean_array_push(v___x_5281_, v_nesting_5274_);
    v___x_5283_ = lean_array_push(v___x_5282_, v___x_5277_);
    v___x_5284_ = lean_array_push(v___x_5283_, v___x_5278_);
    v___x_5285_ = lean_array_push(v___x_5284_, v___x_5279_);
    v___x_5286_ = lean_array_push(v___x_5285_, v___x_5280_);
    v___x_5287_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5287_, 0, v___x_5273_);
    crate::leanh::lean_ctor_set(v___x_5287_, 1, v___x_5276_);
    crate::leanh::lean_ctor_set(v___x_5287_, 2, v___x_5286_);
    return v___x_5287_;
}
pub unsafe fn l_Lean_Syntax_antiquotSuffixSplice_x3f(
    mut v_x_5289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5289_) == 1 {
        let mut v_kind_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_kind_5290_ = crate::leanh::lean_ctor_get(v_x_5289_, 1);
        if crate::leanh::lean_obj_tag(v_kind_5290_) == 1 {
            let mut v_pre_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_str_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5294_: u8 = 0;
            v_pre_5291_ = crate::leanh::lean_ctor_get(v_kind_5290_, 0);
            v_str_5292_ = crate::leanh::lean_ctor_get(v_kind_5290_, 1);
            v___x_5293_ = l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0;
            v___x_5294_ = lean_string_dec_eq(v_str_5292_, v___x_5293_);
            if v___x_5294_ == 0 {
                let mut v___x_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5295_ = crate::leanh::lean_box(0);
                return v___x_5295_;
            } else {
                let mut v___x_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_inc(v_pre_5291_);
                v___x_5296_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5296_, 0, v_pre_5291_);
                return v___x_5296_;
            }
        } else {
            let mut v___x_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5297_ = crate::leanh::lean_box(0);
            return v___x_5297_;
        }
    } else {
        let mut v___x_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5298_ = crate::leanh::lean_box(0);
        return v___x_5298_;
    }
}
pub unsafe fn l_Lean_Syntax_antiquotSuffixSplice_x3f___boxed(
    mut v_x_5299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5300_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_x_5299_);
    crate::leanh::lean_dec(v_x_5299_);
    return v_res_5300_;
}
pub unsafe fn l_Lean_Syntax_isAntiquotSuffixSplice(
    mut v_stx_5301_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5302_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_stx_5301_);
    if crate::leanh::lean_obj_tag(v___x_5302_) == 0 {
        let mut v___x_5303_: u8 = 0;
        v___x_5303_ = 0;
        return v___x_5303_;
    } else {
        let mut v___x_5304_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_5302_, 1);
        v___x_5304_ = 1;
        return v___x_5304_;
    }
}
pub unsafe fn l_Lean_Syntax_isAntiquotSuffixSplice___boxed(
    mut v_stx_5305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5306_: u8 = 0;
    let mut v_r_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5306_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_5305_);
    crate::leanh::lean_dec(v_stx_5305_);
    v_r_5307_ = crate::leanh::lean_box((v_res_5306_) as usize);
    return v_r_5307_;
}
pub unsafe fn l_Lean_Syntax_getAntiquotSuffixSpliceInner(
    mut v_stx_5308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5309_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5310_ = l_Lean_Syntax_getArg(v_stx_5308_, v___x_5309_);
    return v___x_5310_;
}
pub unsafe fn l_Lean_Syntax_getAntiquotSuffixSpliceInner___boxed(
    mut v_stx_5311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5312_ = l_Lean_Syntax_getAntiquotSuffixSpliceInner(v_stx_5311_);
    crate::leanh::lean_dec(v_stx_5311_);
    return v_res_5312_;
}
pub unsafe fn l_Lean_Syntax_mkAntiquotSuffixSpliceNode(
    mut v_kind_5315_: *mut crate::leanh::LeanObject,
    mut v_inner_5316_: *mut crate::leanh::LeanObject,
    mut v_suffix_5317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5318_ = l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__0;
    v___x_5319_ = l_Lean_Name_append(v_kind_5315_, v___x_5318_);
    v___x_5320_ = l_Lean_mkAtom(v_suffix_5317_);
    v___x_5321_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_5322_ = lean_mk_empty_array_with_capacity(v___x_5321_);
    v___x_5323_ = lean_array_push(v___x_5322_, v_inner_5316_);
    v___x_5324_ = lean_array_push(v___x_5323_, v___x_5320_);
    v___x_5325_ = crate::leanh::lean_box(2);
    v___x_5326_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5326_, 0, v___x_5325_);
    crate::leanh::lean_ctor_set(v___x_5326_, 1, v___x_5319_);
    crate::leanh::lean_ctor_set(v___x_5326_, 2, v___x_5324_);
    return v___x_5326_;
}
pub unsafe fn l_Lean_Syntax_isTokenAntiquot(mut v_stx_5330_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: u8 = 0;
    v___x_5331_ = l_Lean_Syntax_isTokenAntiquot___closed__1;
    v___x_5332_ = l_Lean_Syntax_isOfKind(v_stx_5330_, v___x_5331_);
    return v___x_5332_;
}
pub unsafe fn l_Lean_Syntax_isTokenAntiquot___boxed(
    mut v_stx_5333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5334_: u8 = 0;
    let mut v_r_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5334_ = l_Lean_Syntax_isTokenAntiquot(v_stx_5333_);
    v_r_5335_ = crate::leanh::lean_box((v_res_5334_) as usize);
    return v_r_5335_;
}
pub unsafe fn l_Lean_Syntax_isAnyAntiquot(mut v_stx_5336_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___y_5338_: u8 = 0;
    let mut v___x_5339_: u8 = 0;
    let mut v___x_5340_: u8 = 0;
    let mut v___x_5341_: u8 = 0;
    let mut v___x_5342_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5341_ = l_Lean_Syntax_isAntiquot(v_stx_5336_);
                if v___x_5341_ == 0 {
                    v___x_5342_ = l_Lean_Syntax_isAntiquotSplice(v_stx_5336_);
                    v___y_5338_ = v___x_5342_;
                    state = 1;
                    continue;
                } else {
                    v___y_5338_ = v___x_5341_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_5338_ == 0 {
                    v___x_5339_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_5336_);
                    if v___x_5339_ == 0 {
                        v___x_5340_ = l_Lean_Syntax_isTokenAntiquot(v_stx_5336_);
                        return v___x_5340_;
                    } else {
                        crate::leanh::lean_dec(v_stx_5336_);
                        return v___x_5339_;
                    }
                } else {
                    crate::leanh::lean_dec(v_stx_5336_);
                    return v___y_5338_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_isAnyAntiquot___boxed(
    mut v_stx_5343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5344_: u8 = 0;
    let mut v_r_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5344_ = l_Lean_Syntax_isAnyAntiquot(v_stx_5343_);
    v_r_5345_ = crate::leanh::lean_box((v_res_5344_) as usize);
    return v_r_5345_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(
    mut v_upperBound_5349_: *mut crate::leanh::LeanObject,
    mut v_stx_5350_: *mut crate::leanh::LeanObject,
    mut v_visit_5351_: *mut crate::leanh::LeanObject,
    mut v_stack_5352_: *mut crate::leanh::LeanObject,
    mut v_accept_5353_: *mut crate::leanh::LeanObject,
    mut v_a_5354_: *mut crate::leanh::LeanObject,
    mut v_b_5355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: u8 = 0;
    let mut v___x_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: u8 = 0;
    let mut v___x_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5361_ = lean_nat_dec_lt(v_a_5354_, v_upperBound_5349_);
                if v___x_5361_ == 0 {
                    crate::leanh::lean_dec(v_a_5354_);
                    crate::leanh::lean_dec_ref(v_accept_5353_);
                    crate::leanh::lean_dec(v_stack_5352_);
                    crate::leanh::lean_dec_ref(v_visit_5351_);
                    crate::leanh::lean_dec(v_stx_5350_);
                    crate::leanh::lean_inc_ref(v_b_5355_);
                    return v_b_5355_;
                } else {
                    v___x_5362_ = crate::leanh::lean_box(0);
                    v___x_5363_ =
                        l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0;
                    v___x_5364_ = l_Lean_Syntax_getArg(v_stx_5350_, v_a_5354_);
                    crate::leanh::lean_inc_ref(v_visit_5351_);
                    crate::leanh::lean_inc(v___x_5364_);
                    v___x_5365_ = crate::leanh::lean_apply_1(v_visit_5351_, v___x_5364_);
                    v___x_5366_ = (crate::leanh::lean_unbox(v___x_5365_) as u8);
                    if v___x_5366_ == 0 {
                        crate::leanh::lean_dec(v___x_5364_);
                        v_a_5357_ = v___x_5363_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5354_);
                        crate::leanh::lean_inc(v_stx_5350_);
                        v___x_5367_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5367_, 0, v_stx_5350_);
                        crate::leanh::lean_ctor_set(v___x_5367_, 1, v_a_5354_);
                        crate::leanh::lean_inc(v_stack_5352_);
                        v___x_5368_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5368_, 0, v___x_5367_);
                        crate::leanh::lean_ctor_set(v___x_5368_, 1, v_stack_5352_);
                        crate::leanh::lean_inc_ref(v_accept_5353_);
                        crate::leanh::lean_inc_ref(v_visit_5351_);
                        v___x_5369_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(
                            v_visit_5351_,
                            v_accept_5353_,
                            v___x_5368_,
                            v___x_5364_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5369_) == 1 {
                            crate::leanh::lean_dec(v_a_5354_);
                            crate::leanh::lean_dec_ref(v_accept_5353_);
                            crate::leanh::lean_dec(v_stack_5352_);
                            crate::leanh::lean_dec_ref(v_visit_5351_);
                            crate::leanh::lean_dec(v_stx_5350_);
                            v___x_5370_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5370_, 0, v___x_5369_);
                            v___x_5371_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5371_, 0, v___x_5370_);
                            crate::leanh::lean_ctor_set(v___x_5371_, 1, v___x_5362_);
                            return v___x_5371_;
                        } else {
                            crate::leanh::lean_dec(v___x_5369_);
                            v_a_5357_ = v___x_5363_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5358_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5359_ = lean_nat_add(v_a_5354_, v___x_5358_);
                crate::leanh::lean_dec(v_a_5354_);
                v_a_5354_ = v___x_5359_;
                v_b_5355_ = v_a_5357_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(
    mut v_visit_5372_: *mut crate::leanh::LeanObject,
    mut v_accept_5373_: *mut crate::leanh::LeanObject,
    mut v_stack_5374_: *mut crate::leanh::LeanObject,
    mut v_stx_5375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: u8 = 0;
    crate::leanh::lean_inc_ref(v_accept_5373_);
    crate::leanh::lean_inc(v_stx_5375_);
    v___x_5376_ = crate::leanh::lean_apply_1(v_accept_5373_, v_stx_5375_);
    v___x_5377_ = (crate::leanh::lean_unbox(v___x_5376_) as u8);
    if v___x_5377_ == 0 {
        let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5378_ = l_Lean_Syntax_getNumArgs(v_stx_5375_);
        v___x_5379_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_5380_ = crate::leanh::lean_box(0);
        v___x_5381_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0;
        v___x_5382_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v___x_5378_, v_stx_5375_, v_visit_5372_, v_stack_5374_, v_accept_5373_, v___x_5379_, v___x_5381_);
        crate::leanh::lean_dec(v___x_5378_);
        v_fst_5383_ = crate::leanh::lean_ctor_get(v___x_5382_, 0);
        crate::leanh::lean_inc(v_fst_5383_);
        crate::leanh::lean_dec_ref(v___x_5382_);
        if crate::leanh::lean_obj_tag(v_fst_5383_) == 0 {
            return v___x_5380_;
        } else {
            let mut v_val_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_5384_ = crate::leanh::lean_ctor_get(v_fst_5383_, 0);
            crate::leanh::lean_inc(v_val_5384_);
            crate::leanh::lean_dec_ref_known(v_fst_5383_, 1);
            return v_val_5384_;
        }
    } else {
        let mut v___x_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_accept_5373_);
        crate::leanh::lean_dec_ref(v_visit_5372_);
        v___x_5385_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_5386_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5386_, 0, v_stx_5375_);
        crate::leanh::lean_ctor_set(v___x_5386_, 1, v___x_5385_);
        v___x_5387_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5387_, 0, v___x_5386_);
        crate::leanh::lean_ctor_set(v___x_5387_, 1, v_stack_5374_);
        v___x_5388_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5388_, 0, v___x_5387_);
        return v___x_5388_;
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg___boxed(
    mut v_upperBound_5389_: *mut crate::leanh::LeanObject,
    mut v_stx_5390_: *mut crate::leanh::LeanObject,
    mut v_visit_5391_: *mut crate::leanh::LeanObject,
    mut v_stack_5392_: *mut crate::leanh::LeanObject,
    mut v_accept_5393_: *mut crate::leanh::LeanObject,
    mut v_a_5394_: *mut crate::leanh::LeanObject,
    mut v_b_5395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5396_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_5389_, v_stx_5390_, v_visit_5391_, v_stack_5392_, v_accept_5393_, v_a_5394_, v_b_5395_);
    crate::leanh::lean_dec_ref(v_b_5395_);
    crate::leanh::lean_dec(v_upperBound_5389_);
    return v_res_5396_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(
    mut v_upperBound_5397_: *mut crate::leanh::LeanObject,
    mut v_stx_5398_: *mut crate::leanh::LeanObject,
    mut v_visit_5399_: *mut crate::leanh::LeanObject,
    mut v_stack_5400_: *mut crate::leanh::LeanObject,
    mut v_accept_5401_: *mut crate::leanh::LeanObject,
    mut v_inst_5402_: *mut crate::leanh::LeanObject,
    mut v_R_5403_: *mut crate::leanh::LeanObject,
    mut v_a_5404_: *mut crate::leanh::LeanObject,
    mut v_b_5405_: *mut crate::leanh::LeanObject,
    mut v_c_5406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5407_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_5397_, v_stx_5398_, v_visit_5399_, v_stack_5400_, v_accept_5401_, v_a_5404_, v_b_5405_);
    return v___x_5407_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___boxed(
    mut v_upperBound_5408_: *mut crate::leanh::LeanObject,
    mut v_stx_5409_: *mut crate::leanh::LeanObject,
    mut v_visit_5410_: *mut crate::leanh::LeanObject,
    mut v_stack_5411_: *mut crate::leanh::LeanObject,
    mut v_accept_5412_: *mut crate::leanh::LeanObject,
    mut v_inst_5413_: *mut crate::leanh::LeanObject,
    mut v_R_5414_: *mut crate::leanh::LeanObject,
    mut v_a_5415_: *mut crate::leanh::LeanObject,
    mut v_b_5416_: *mut crate::leanh::LeanObject,
    mut v_c_5417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5418_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(v_upperBound_5408_, v_stx_5409_, v_visit_5410_, v_stack_5411_, v_accept_5412_, v_inst_5413_, v_R_5414_, v_a_5415_, v_b_5416_, v_c_5417_);
    crate::leanh::lean_dec_ref(v_b_5416_);
    crate::leanh::lean_dec(v_upperBound_5408_);
    return v_res_5418_;
}
pub unsafe fn l_Lean_Syntax_findStack_x3f(
    mut v_root_5419_: *mut crate::leanh::LeanObject,
    mut v_visit_5420_: *mut crate::leanh::LeanObject,
    mut v_accept_5421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: u8 = 0;
    crate::leanh::lean_inc_ref(v_visit_5420_);
    crate::leanh::lean_inc(v_root_5419_);
    v___x_5422_ = crate::leanh::lean_apply_1(v_visit_5420_, v_root_5419_);
    v___x_5423_ = (crate::leanh::lean_unbox(v___x_5422_) as u8);
    if v___x_5423_ == 0 {
        let mut v___x_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_accept_5421_);
        crate::leanh::lean_dec_ref(v_visit_5420_);
        crate::leanh::lean_dec(v_root_5419_);
        v___x_5424_ = crate::leanh::lean_box(0);
        return v___x_5424_;
    } else {
        let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5425_ = crate::leanh::lean_box(0);
        v___x_5426_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(
            v_visit_5420_,
            v_accept_5421_,
            v___x_5425_,
            v_root_5419_,
        );
        return v___x_5426_;
    }
}
pub unsafe fn l_Lean_Syntax_Stack_matches___lam__0(
    mut v___x_5427_: u8,
    mut v_x_5428_: *mut crate::leanh::LeanObject,
    mut v_p_5429_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_p_5429_) == 0 {
        crate::leanh::lean_dec_ref(v_x_5428_);
        return v___x_5427_;
    } else {
        let mut v_fst_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5432_: u8 = 0;
        v_fst_5430_ = crate::leanh::lean_ctor_get(v_x_5428_, 0);
        crate::leanh::lean_inc(v_fst_5430_);
        crate::leanh::lean_dec_ref(v_x_5428_);
        v_val_5431_ = crate::leanh::lean_ctor_get(v_p_5429_, 0);
        v___x_5432_ = l_Lean_Syntax_isOfKind(v_fst_5430_, v_val_5431_);
        return v___x_5432_;
    }
}
pub unsafe fn l_Lean_Syntax_Stack_matches___lam__0___boxed(
    mut v___x_5433_: *mut crate::leanh::LeanObject,
    mut v_x_5434_: *mut crate::leanh::LeanObject,
    mut v_p_5435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_121__boxed_5436_: u8 = 0;
    let mut v_res_5437_: u8 = 0;
    let mut v_r_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_121__boxed_5436_ = (crate::leanh::lean_unbox(v___x_5433_) as u8);
    v_res_5437_ =
        l_Lean_Syntax_Stack_matches___lam__0(v___x_121__boxed_5436_, v_x_5434_, v_p_5435_);
    crate::leanh::lean_dec(v_p_5435_);
    v_r_5438_ = crate::leanh::lean_box((v_res_5437_) as usize);
    return v_r_5438_;
}
pub unsafe fn l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(
    mut v_x_5439_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5440_: u8 = 0;
    let mut v_head_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: u8 = 0;
    let mut v___x_5443_: u8 = 0;
    let mut v_tail_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5439_) == 0 {
                    v___x_5440_ = 1;
                    return v___x_5440_;
                } else {
                    v_head_5441_ = crate::leanh::lean_ctor_get(v_x_5439_, 0);
                    v___x_5442_ = (crate::leanh::lean_unbox(v_head_5441_) as u8);
                    if v___x_5442_ == 0 {
                        v___x_5443_ = (crate::leanh::lean_unbox(v_head_5441_) as u8);
                        return v___x_5443_;
                    } else {
                        v_tail_5444_ = crate::leanh::lean_ctor_get(v_x_5439_, 1);
                        v_x_5439_ = v_tail_5444_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_all___at___00Lean_Syntax_Stack_matches_spec__0___boxed(
    mut v_x_5446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5447_: u8 = 0;
    let mut v_r_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5447_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v_x_5446_);
    crate::leanh::lean_dec(v_x_5446_);
    v_r_5448_ = crate::leanh::lean_box((v_res_5447_) as usize);
    return v_r_5448_;
}
pub unsafe fn l_Lean_Syntax_Stack_matches(
    mut v_stack_5451_: *mut crate::leanh::LeanObject,
    mut v_pattern_5452_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: u8 = 0;
    v___x_5453_ = l_List_lengthTR___redArg(v_pattern_5452_);
    v___x_5454_ = l_List_lengthTR___redArg(v_stack_5451_);
    v___x_5455_ = lean_nat_dec_le(v___x_5453_, v___x_5454_);
    crate::leanh::lean_dec(v___x_5454_);
    crate::leanh::lean_dec(v___x_5453_);
    if v___x_5455_ == 0 {
        crate::leanh::lean_dec(v_pattern_5452_);
        crate::leanh::lean_dec(v_stack_5451_);
        return v___x_5455_;
    } else {
        let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5460_: u8 = 0;
        v___x_5456_ = crate::leanh::lean_box((v___x_5455_) as usize);
        v___f_5457_ = crate::leanh::lean_alloc_closure(
            l_Lean_Syntax_Stack_matches___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_5457_, 0, v___x_5456_);
        v___x_5458_ = l_Lean_Syntax_Stack_matches___closed__0;
        v___x_5459_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_5457_,
            v_stack_5451_,
            v_pattern_5452_,
            v___x_5458_,
        );
        v___x_5460_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v___x_5459_);
        crate::leanh::lean_dec(v___x_5459_);
        return v___x_5460_;
    }
}
pub unsafe fn l_Lean_Syntax_Stack_matches___boxed(
    mut v_stack_5461_: *mut crate::leanh::LeanObject,
    mut v_pattern_5462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5463_: u8 = 0;
    let mut v_r_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5463_ = l_Lean_Syntax_Stack_matches(v_stack_5461_, v_pattern_5462_);
    v_r_5464_ = crate::leanh::lean_box((v_res_5463_) as usize);
    return v_r_5464_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Syntax(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Hashable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Format(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Coe(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Hashable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Syntax(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Syntax(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Hashable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Format(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Coe(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Hashable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Syntax(builtin);
}
