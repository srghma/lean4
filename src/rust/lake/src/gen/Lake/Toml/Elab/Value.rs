// Lean compiler output
// Module: Lake.Toml.Elab.Value
// Imports: Lake.Toml.Data.Value Lake.Toml.Grammar Lake.Toml.Grammar
use crate::ffi::{
    lean_array_get, lean_array_get_size, lean_array_pop, lean_array_push, lean_array_size,
    lean_array_to_list, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_float_div,
    lean_float_negate, lean_int_add, lean_int_dec_lt, lean_mk_empty_array_with_capacity,
    lean_nat_abs, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul,
    lean_nat_sub, lean_nat_to_int, lean_panic_fn_borrowed, lean_st_ref_get, lean_string_append,
    lean_string_dec_eq, lean_string_is_valid_pos, lean_string_length, lean_string_push,
    lean_string_utf8_at_end, lean_string_utf8_byte_size, lean_string_utf8_extract,
    lean_string_utf8_get, lean_string_utf8_get_fast, lean_string_utf8_next,
    lean_string_utf8_next_fast, lean_substring_tostring, lean_uint32_dec_eq, lean_uint32_dec_le,
    lean_uint32_of_nat, lean_uint32_sub, lean_uint32_to_nat, lean_usize_add, lean_usize_dec_eq,
    lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Int::Basic::l_Int_negOfNat;
use crate::r#gen::Init::Data::OfScientific::{l_Float_ofScientific, lean_float_of_nat};
use crate::r#gen::Init::Data::String::Basic::{
    l_String_Slice_Pos_get_x3f, l_String_Slice_Pos_nextn,
};
use crate::r#gen::Init::Data::String::Defs::l_String_instInhabitedSlice;
use crate::r#gen::Init::Data::String::FindPos::l_String_Slice_Pos_prevn;
use crate::r#gen::Init::Data::String::Iterate::l_String_Slice_positions;
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_toString;
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Data::String::Substring::l_Substring_Raw_nextn;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_TSepArray_getElems___redArg, l_Lean_Syntax_isLit_x3f,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_str___override, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_isOfKind, l_Lean_replaceRef, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lake::Toml::Data::DateTime::l_Lake_Toml_DateTime_ofString_x3f;
use crate::r#gen::Lake::Toml::Data::Dict::{
    l_Lake_Toml_RBDict_contains___redArg, l_Lake_Toml_RBDict_empty,
    l_Lake_Toml_RBDict_findEntry_x3f___redArg, l_Lake_Toml_RBDict_push___redArg,
};
use crate::r#gen::Lake::Toml::Data::Value::{
    initialize_Lake_Toml_Data_Value, runtime_initialize_Lake_Toml_Data_Value,
};
use crate::r#gen::Lake::Toml::Grammar::{
    initialize_Lake_Toml_Grammar, runtime_initialize_Lake_Toml_Grammar,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instAddMessageContextCoreM, l_Lean_Core_instMonadCoreM___lam__0___boxed,
    l_Lean_Core_instMonadCoreM___lam__1___boxed, l_Lean_Core_instMonadRefCoreM,
    l_Lean_instMonadExceptOfExceptionCoreM,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Exception::{
    l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg,
    l_Lean_throwErrorAt___redArg,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 0],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [32, 115, 121, 110, 116, 97, 120, 0],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value:
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
    m_data: [76, 97, 107, 101, 0],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value:
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
    m_data: [84, 111, 109, 108, 0],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__2_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [98, 111, 111, 108, 101, 97, 110, 0],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__2_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value_aux_0:
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
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        16525079986463702690 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        8637345244662348 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__4_value:
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
        105, 110, 118, 97, 108, 105, 100, 32, 98, 111, 111, 108, 101, 97, 110, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__6_value:
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
    m_data: [116, 114, 117, 101, 0],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__6_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value_aux_0:
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
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        16525079986463702690 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        5919785301382904414 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__8_value:
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
    m_data: [102, 97, 108, 115, 101, 0],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__8_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value_aux_0:
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
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        16525079986463702690 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__8_value
        ) as *mut crate::leanh::LeanObject,
        4008786854061235757 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__0_value:
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
    m_data: [100, 101, 99, 73, 110, 116, 0],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value_aux_0:
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
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        16525079986463702690 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        7221221276125824402 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__2_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
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
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 100, 101, 99, 105, 109, 97, 108, 32,
        105, 110, 116, 101, 103, 101, 114, 32, 115, 121, 110, 116, 97, 120, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2_value:
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
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [105, 110, 102, 0],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [110, 97, 110, 0],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2: f64 = 0.0;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__0_value:
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
    m_data: [102, 108, 111, 97, 116, 0],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value_aux_0:
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
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        16525079986463702690 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        17795691646878718568 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__2_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 102, 108, 111, 97, 116, 32, 115, 121,
        110, 116, 97, 120, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__0_value:
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
    m_data: [98, 105, 110, 78, 117, 109, 0],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value_aux_0:
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
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        16525079986463702690 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        486821199203679291 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__2_value:
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
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 98, 105, 110, 97, 114, 121, 32, 110,
        117, 109, 98, 101, 114, 32, 115, 121, 110, 116, 97, 120, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__0_value:
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
    m_data: [111, 99, 116, 78, 117, 109, 0],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value_aux_0:
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
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        16525079986463702690 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        14236009889605174877 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__2_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 111, 99, 116, 97, 108, 32, 110, 117,
        109, 98, 101, 114, 32, 115, 121, 110, 116, 97, 120, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__0_value:
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
    m_data: [104, 101, 120, 78, 117, 109, 0],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value_aux_0:
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
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        16525079986463702690 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        18206715719635152477 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__2_value:
    crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 104, 101, 120, 97, 100, 101, 99, 105,
        109, 97, 108, 32, 110, 117, 109, 98, 101, 114, 32, 115, 121, 110, 116, 97, 120, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
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
        105, 110, 118, 97, 108, 105, 100, 32, 100, 97, 116, 101, 45, 116, 105, 109, 101, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__2_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [100, 97, 116, 101, 84, 105, 109, 101, 0],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__2_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value_aux_0:
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
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        16525079986463702690 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        14620934732133821028 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__4_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
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
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 100, 97, 116, 101, 45, 116, 105, 109,
        101, 32, 115, 121, 110, 116, 97, 120, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__0_value:
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
        108, 105, 116, 101, 114, 97, 108, 83, 116, 114, 105, 110, 103, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__0_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value_aux_0:
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
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        16525079986463702690 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        6024408818386315505 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__2_value:
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
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 108, 105, 116, 101, 114, 97, 108, 83,
        116, 114, 105, 110, 103, 32, 115, 121, 110, 116, 97, 120, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
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
        73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115,
        105, 99, 65, 117, 120, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
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
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2_value:
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
        118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
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
        105, 110, 118, 97, 108, 105, 100, 32, 117, 110, 105, 99, 111, 100, 101, 32, 101, 115, 99,
        97, 112, 101, 32, 96, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2_value:
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
    m_data: [96, 0],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0_value:
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
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__1_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [98, 97, 115, 105, 99, 83, 116, 114, 105, 110, 103, 0],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__1_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value_aux_0:
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
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        16525079986463702690 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        16849499249217381028 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__3_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 98, 97, 115, 105, 99, 32, 115, 116,
        114, 105, 110, 103, 32, 115, 121, 110, 116, 97, 120, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__4_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__3_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__0_value:
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
        109, 108, 76, 105, 116, 101, 114, 97, 108, 83, 116, 114, 105, 110, 103, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__0_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value_aux_0:
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
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value) as *mut crate::leanh::LeanObject,16525079986463702690 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__0_value) as *mut crate::leanh::LeanObject,3891709539368753145 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__2_value:
    crate::leanh::LeanStringObject<44> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 44,
    m_capacity: 44,
    m_length: 43,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 109, 117, 108, 116, 105, 45, 108, 105,
        110, 101, 32, 108, 105, 116, 101, 114, 97, 108, 32, 115, 116, 114, 105, 110, 103, 32, 115,
        121, 110, 116, 97, 120, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__0_value:
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
        109, 108, 66, 97, 115, 105, 99, 83, 116, 114, 105, 110, 103, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__0_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value_aux_0:
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
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        16525079986463702690 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        1863697331681762253 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__2_value:
    crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 109, 117, 108, 116, 105, 45, 108, 105,
        110, 101, 32, 98, 97, 115, 105, 99, 32, 115, 116, 114, 105, 110, 103, 32, 115, 121, 110,
        116, 97, 120, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__0_value:
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
    m_data: [115, 116, 114, 105, 110, 103, 0],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value_aux_0:
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
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        16525079986463702690 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        14667688617378285135 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__2_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
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
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 115, 116, 114, 105, 110, 103, 32, 115,
        121, 110, 116, 97, 120, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__0_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [117, 110, 113, 117, 111, 116, 101, 100, 75, 101, 121, 0],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__0_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value_aux_0:
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
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        16525079986463702690 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        17377064587868252984 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__2_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 117, 110, 113, 117, 111, 116, 101,
        100, 32, 107, 101, 121, 32, 115, 121, 110, 116, 97, 120, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_elabSimpleKey___closed__0_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [115, 105, 109, 112, 108, 101, 75, 101, 121, 0],
    };
static mut l_Lake_Toml_elabSimpleKey___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_elabSimpleKey___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Toml_elabSimpleKey___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value
            ) as *mut crate::leanh::LeanObject,
            13012506173997729135 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_Toml_elabSimpleKey___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_elabSimpleKey___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value
            ) as *mut crate::leanh::LeanObject,
            16525079986463702690 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Toml_elabSimpleKey___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Toml_elabSimpleKey___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_elabSimpleKey___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15900767148364346299 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_elabSimpleKey___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_elabSimpleKey___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_elabSimpleKey___closed__2_value: crate::leanh::LeanStringObject<29> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 115, 105, 109, 112, 108, 101, 32,
            107, 101, 121, 32, 115, 121, 110, 116, 97, 120, 0,
        ],
    };
static mut l_Lake_Toml_elabSimpleKey___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_elabSimpleKey___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_Toml_elabSimpleKey___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_elabSimpleKey___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__0_value:
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
    m_data: [97, 114, 114, 97, 121, 0],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value_aux_0:
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
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value) as *mut crate::leanh::LeanObject,16525079986463702690 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__0_value) as *mut crate::leanh::LeanObject,9671799119587300413 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__2_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 97, 114, 114, 97, 121, 32, 115, 121,
        110, 116, 97, 120, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [99, 97, 110, 110, 111, 116, 32, 114, 101, 100, 101, 102, 105, 110, 101, 32, 107, 101, 121, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [107, 101, 121, 118, 97, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value) as *mut crate::leanh::LeanObject,16525079986463702690 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__0_value) as *mut crate::leanh::LeanObject,1860500813421358697 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__2_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 107, 101, 121, 45, 118, 97, 108, 117, 101, 32, 112, 97, 105, 114, 32, 115, 121, 110, 116, 97, 120, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__4_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [107, 101, 121, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value) as *mut crate::leanh::LeanObject,16525079986463702690 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__4_value) as *mut crate::leanh::LeanObject,3865642880800790572 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 107, 101, 121, 32, 115, 121, 110, 116, 97, 120, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__0_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [105, 110, 108, 105, 110, 101, 84, 97, 98, 108, 101, 0],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__0_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value_aux_0:
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
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        16525079986463702690 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        1671555236049616288 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__2_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 105, 110, 108, 105, 110, 101, 32, 116,
        97, 98, 108, 101, 32, 115, 121, 110, 116, 97, 120, 0,
    ],
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_elabVal___closed__0_value: crate::leanh::LeanStringObject<24> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 118, 97, 108, 117, 101, 32, 115,
            121, 110, 116, 97, 120, 0,
        ],
    };
static mut l_Lake_Toml_elabVal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_elabVal___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_Toml_elabVal___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_elabVal___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2321_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_2321_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2322_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0_once
        ),
        _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0,
    );
    v___x_2323_ = l_StateRefT_x27_instMonad___redArg(v___x_2322_);
    return v___x_2323_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit(
    mut v_k_2328_: *mut crate::leanh::LeanObject,
    mut v_x_2329_: *mut crate::leanh::LeanObject,
    mut v_name_2330_: *mut crate::leanh::LeanObject,
    mut v_a_2331_: *mut crate::leanh::LeanObject,
    mut v_a_2332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2359_: u8 = 0;
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2363_: u8 = 0;
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231__overap_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2334_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1_once
                    ),
                    _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1,
                );
                v_toApplicative_2335_ = crate::leanh::lean_ctor_get(v___x_2334_, 0);
                v_toFunctor_2336_ = crate::leanh::lean_ctor_get(v_toApplicative_2335_, 0);
                v_toSeq_2337_ = crate::leanh::lean_ctor_get(v_toApplicative_2335_, 2);
                v_toSeqLeft_2338_ = crate::leanh::lean_ctor_get(v_toApplicative_2335_, 3);
                v_toSeqRight_2339_ = crate::leanh::lean_ctor_get(v_toApplicative_2335_, 4);
                v___f_2340_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2;
                v___f_2341_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_2336_, 2);
                v___f_2342_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2342_, 0, v_toFunctor_2336_);
                v___f_2343_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2343_, 0, v_toFunctor_2336_);
                v___x_2344_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2344_, 0, v___f_2342_);
                crate::leanh::lean_ctor_set(v___x_2344_, 1, v___f_2343_);
                crate::leanh::lean_inc(v_toSeqRight_2339_);
                v___f_2345_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2345_, 0, v_toSeqRight_2339_);
                crate::leanh::lean_inc(v_toSeqLeft_2338_);
                v___f_2346_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2346_, 0, v_toSeqLeft_2338_);
                crate::leanh::lean_inc(v_toSeq_2337_);
                v___f_2347_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2347_, 0, v_toSeq_2337_);
                v___x_2348_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2348_, 0, v___x_2344_);
                crate::leanh::lean_ctor_set(v___x_2348_, 1, v___f_2340_);
                crate::leanh::lean_ctor_set(v___x_2348_, 2, v___f_2347_);
                crate::leanh::lean_ctor_set(v___x_2348_, 3, v___f_2346_);
                crate::leanh::lean_ctor_set(v___x_2348_, 4, v___f_2345_);
                v___x_2349_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2349_, 0, v___x_2348_);
                crate::leanh::lean_ctor_set(v___x_2349_, 1, v___f_2341_);
                v___x_2350_ = l_Lean_instMonadExceptOfExceptionCoreM;
                v___x_2351_ = l_Lean_Core_instMonadRefCoreM;
                v___x_2352_ = l_Lean_Core_instAddMessageContextCoreM;
                crate::leanh::lean_inc_ref(v___x_2349_);
                v___x_2353_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___x_2352_,
                    v___x_2349_,
                );
                v___x_2354_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2354_, 0, v___x_2350_);
                crate::leanh::lean_ctor_set(v___x_2354_, 1, v___x_2351_);
                crate::leanh::lean_ctor_set(v___x_2354_, 2, v___x_2353_);
                v___x_2355_ = l_Lean_Syntax_isLit_x3f(v_k_2328_, v_x_2329_);
                if crate::leanh::lean_obj_tag(v___x_2355_) == 1 {
                    crate::leanh::lean_dec_ref_known(v___x_2354_, 3);
                    crate::leanh::lean_dec_ref_known(v___x_2349_, 2);
                    crate::leanh::lean_dec(v_x_2329_);
                    v_val_2356_ = crate::leanh::lean_ctor_get(v___x_2355_, 0);
                    v_isSharedCheck_2363_ = (!crate::leanh::lean_is_exclusive(v___x_2355_)) as u8;
                    if v_isSharedCheck_2363_ == 0 {
                        v___x_2358_ = v___x_2355_;
                        v_isShared_2359_ = v_isSharedCheck_2363_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2356_);
                        crate::leanh::lean_dec(v___x_2355_);
                        v___x_2358_ = crate::leanh::lean_box(0);
                        v_isShared_2359_ = v_isSharedCheck_2363_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2355_);
                    v___x_2364_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4;
                    v___x_2365_ = lean_string_append(v___x_2364_, v_name_2330_);
                    v___x_2366_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5;
                    v___x_2367_ = lean_string_append(v___x_2365_, v___x_2366_);
                    v___x_2368_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2368_, 0, v___x_2367_);
                    v___x_2369_ = l_Lean_MessageData_ofFormat(v___x_2368_);
                    v___x_231__overap_2370_ = l_Lean_throwErrorAt___redArg(
                        v___x_2349_,
                        v___x_2354_,
                        v_x_2329_,
                        v___x_2369_,
                    );
                    crate::leanh::lean_inc(v_a_2332_);
                    crate::leanh::lean_inc_ref(v_a_2331_);
                    v___x_2371_ = crate::leanh::lean_apply_3(
                        v___x_231__overap_2370_,
                        v_a_2331_,
                        v_a_2332_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_2371_;
                }
            }
            1 => {
                if v_isShared_2359_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2358_, 0);
                    v___x_2361_ = v___x_2358_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2362_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_val_2356_);
                    v___x_2361_ = v_reuseFailAlloc_2362_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2361_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___boxed(
    mut v_k_2372_: *mut crate::leanh::LeanObject,
    mut v_x_2373_: *mut crate::leanh::LeanObject,
    mut v_name_2374_: *mut crate::leanh::LeanObject,
    mut v_a_2375_: *mut crate::leanh::LeanObject,
    mut v_a_2376_: *mut crate::leanh::LeanObject,
    mut v_a_2377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2378_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit(
        v_k_2372_,
        v_x_2373_,
        v_name_2374_,
        v_a_2375_,
        v_a_2376_,
    );
    crate::leanh::lean_dec(v_a_2376_);
    crate::leanh::lean_dec_ref(v_a_2375_);
    crate::leanh::lean_dec_ref(v_name_2374_);
    crate::leanh::lean_dec(v_k_2372_);
    return v_res_2378_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2379_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2379_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2380_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0);
    v___x_2381_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2381_, 0, v___x_2380_);
    return v___x_2381_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2382_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1);
    v___x_2383_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2384_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2384_, 0, v___x_2383_);
    crate::leanh::lean_ctor_set(v___x_2384_, 1, v___x_2383_);
    crate::leanh::lean_ctor_set(v___x_2384_, 2, v___x_2383_);
    crate::leanh::lean_ctor_set(v___x_2384_, 3, v___x_2383_);
    crate::leanh::lean_ctor_set(v___x_2384_, 4, v___x_2382_);
    crate::leanh::lean_ctor_set(v___x_2384_, 5, v___x_2382_);
    crate::leanh::lean_ctor_set(v___x_2384_, 6, v___x_2382_);
    crate::leanh::lean_ctor_set(v___x_2384_, 7, v___x_2382_);
    crate::leanh::lean_ctor_set(v___x_2384_, 8, v___x_2382_);
    crate::leanh::lean_ctor_set(v___x_2384_, 9, v___x_2382_);
    return v___x_2384_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2385_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2386_ = lean_mk_empty_array_with_capacity(v___x_2385_);
    v___x_2387_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2387_, 0, v___x_2386_);
    return v___x_2387_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2388_: usize = 0;
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2388_ = 5usize;
    v___x_2389_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2390_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2391_ = lean_mk_empty_array_with_capacity(v___x_2390_);
    v___x_2392_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3);
    v___x_2393_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_2393_, 0, v___x_2392_);
    crate::leanh::lean_ctor_set(v___x_2393_, 1, v___x_2391_);
    crate::leanh::lean_ctor_set(v___x_2393_, 2, v___x_2389_);
    crate::leanh::lean_ctor_set(v___x_2393_, 3, v___x_2389_);
    crate::leanh::lean_ctor_set_usize(v___x_2393_, 4, v___x_2388_);
    return v___x_2393_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2394_ = crate::leanh::lean_box(1);
    v___x_2395_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4);
    v___x_2396_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1);
    v___x_2397_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2397_, 0, v___x_2396_);
    crate::leanh::lean_ctor_set(v___x_2397_, 1, v___x_2395_);
    crate::leanh::lean_ctor_set(v___x_2397_, 2, v___x_2394_);
    return v___x_2397_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(
    mut v_msgData_2398_: *mut crate::leanh::LeanObject,
    mut v___y_2399_: *mut crate::leanh::LeanObject,
    mut v___y_2400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2402_ = lean_st_ref_get(v___y_2400_);
    v_env_2403_ = crate::leanh::lean_ctor_get(v___x_2402_, 0);
    crate::leanh::lean_inc_ref(v_env_2403_);
    crate::leanh::lean_dec(v___x_2402_);
    v_options_2404_ = crate::leanh::lean_ctor_get(v___y_2399_, 2);
    v___x_2405_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2);
    v___x_2406_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5);
    crate::leanh::lean_inc_ref(v_options_2404_);
    v___x_2407_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2407_, 0, v_env_2403_);
    crate::leanh::lean_ctor_set(v___x_2407_, 1, v___x_2405_);
    crate::leanh::lean_ctor_set(v___x_2407_, 2, v___x_2406_);
    crate::leanh::lean_ctor_set(v___x_2407_, 3, v_options_2404_);
    v___x_2408_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2408_, 0, v___x_2407_);
    crate::leanh::lean_ctor_set(v___x_2408_, 1, v_msgData_2398_);
    v___x_2409_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2409_, 0, v___x_2408_);
    return v___x_2409_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_2410_: *mut crate::leanh::LeanObject,
    mut v___y_2411_: *mut crate::leanh::LeanObject,
    mut v___y_2412_: *mut crate::leanh::LeanObject,
    mut v___y_2413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2414_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(v_msgData_2410_, v___y_2411_, v___y_2412_);
    crate::leanh::lean_dec(v___y_2412_);
    crate::leanh::lean_dec_ref(v___y_2411_);
    return v_res_2414_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(
    mut v_msg_2415_: *mut crate::leanh::LeanObject,
    mut v___y_2416_: *mut crate::leanh::LeanObject,
    mut v___y_2417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2424_: u8 = 0;
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2429_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2419_ = crate::leanh::lean_ctor_get(v___y_2416_, 5);
                v___x_2420_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(v_msg_2415_, v___y_2416_, v___y_2417_);
                v_a_2421_ = crate::leanh::lean_ctor_get(v___x_2420_, 0);
                v_isSharedCheck_2429_ = (!crate::leanh::lean_is_exclusive(v___x_2420_)) as u8;
                if v_isSharedCheck_2429_ == 0 {
                    v___x_2423_ = v___x_2420_;
                    v_isShared_2424_ = v_isSharedCheck_2429_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2421_);
                    crate::leanh::lean_dec(v___x_2420_);
                    v___x_2423_ = crate::leanh::lean_box(0);
                    v_isShared_2424_ = v_isSharedCheck_2429_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_2419_);
                v___x_2425_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2425_, 0, v_ref_2419_);
                crate::leanh::lean_ctor_set(v___x_2425_, 1, v_a_2421_);
                if v_isShared_2424_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2423_, 1);
                    crate::leanh::lean_ctor_set(v___x_2423_, 0, v___x_2425_);
                    v___x_2427_ = v___x_2423_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2428_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2425_);
                    v___x_2427_ = v_reuseFailAlloc_2428_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2427_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg___boxed(
    mut v_msg_2430_: *mut crate::leanh::LeanObject,
    mut v___y_2431_: *mut crate::leanh::LeanObject,
    mut v___y_2432_: *mut crate::leanh::LeanObject,
    mut v___y_2433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2434_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v_msg_2430_, v___y_2431_, v___y_2432_);
    crate::leanh::lean_dec(v___y_2432_);
    crate::leanh::lean_dec_ref(v___y_2431_);
    return v_res_2434_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(
    mut v_ref_2435_: *mut crate::leanh::LeanObject,
    mut v_msg_2436_: *mut crate::leanh::LeanObject,
    mut v___y_2437_: *mut crate::leanh::LeanObject,
    mut v___y_2438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2452_: u8 = 0;
    let mut v_cancelTk_x3f_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2454_: u8 = 0;
    let mut v_inheritedTraceOptions_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_2440_ = crate::leanh::lean_ctor_get(v___y_2437_, 0);
    v_fileMap_2441_ = crate::leanh::lean_ctor_get(v___y_2437_, 1);
    v_options_2442_ = crate::leanh::lean_ctor_get(v___y_2437_, 2);
    v_currRecDepth_2443_ = crate::leanh::lean_ctor_get(v___y_2437_, 3);
    v_maxRecDepth_2444_ = crate::leanh::lean_ctor_get(v___y_2437_, 4);
    v_ref_2445_ = crate::leanh::lean_ctor_get(v___y_2437_, 5);
    v_currNamespace_2446_ = crate::leanh::lean_ctor_get(v___y_2437_, 6);
    v_openDecls_2447_ = crate::leanh::lean_ctor_get(v___y_2437_, 7);
    v_initHeartbeats_2448_ = crate::leanh::lean_ctor_get(v___y_2437_, 8);
    v_maxHeartbeats_2449_ = crate::leanh::lean_ctor_get(v___y_2437_, 9);
    v_quotContext_2450_ = crate::leanh::lean_ctor_get(v___y_2437_, 10);
    v_currMacroScope_2451_ = crate::leanh::lean_ctor_get(v___y_2437_, 11);
    v_diag_2452_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2437_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2453_ = crate::leanh::lean_ctor_get(v___y_2437_, 12);
    v_suppressElabErrors_2454_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2437_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2455_ = crate::leanh::lean_ctor_get(v___y_2437_, 13);
    v_ref_2456_ = l_Lean_replaceRef(v_ref_2435_, v_ref_2445_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_2455_);
    crate::leanh::lean_inc(v_cancelTk_x3f_2453_);
    crate::leanh::lean_inc(v_currMacroScope_2451_);
    crate::leanh::lean_inc(v_quotContext_2450_);
    crate::leanh::lean_inc(v_maxHeartbeats_2449_);
    crate::leanh::lean_inc(v_initHeartbeats_2448_);
    crate::leanh::lean_inc(v_openDecls_2447_);
    crate::leanh::lean_inc(v_currNamespace_2446_);
    crate::leanh::lean_inc(v_maxRecDepth_2444_);
    crate::leanh::lean_inc(v_currRecDepth_2443_);
    crate::leanh::lean_inc_ref(v_options_2442_);
    crate::leanh::lean_inc_ref(v_fileMap_2441_);
    crate::leanh::lean_inc_ref(v_fileName_2440_);
    v___x_2457_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_2457_, 0, v_fileName_2440_);
    crate::leanh::lean_ctor_set(v___x_2457_, 1, v_fileMap_2441_);
    crate::leanh::lean_ctor_set(v___x_2457_, 2, v_options_2442_);
    crate::leanh::lean_ctor_set(v___x_2457_, 3, v_currRecDepth_2443_);
    crate::leanh::lean_ctor_set(v___x_2457_, 4, v_maxRecDepth_2444_);
    crate::leanh::lean_ctor_set(v___x_2457_, 5, v_ref_2456_);
    crate::leanh::lean_ctor_set(v___x_2457_, 6, v_currNamespace_2446_);
    crate::leanh::lean_ctor_set(v___x_2457_, 7, v_openDecls_2447_);
    crate::leanh::lean_ctor_set(v___x_2457_, 8, v_initHeartbeats_2448_);
    crate::leanh::lean_ctor_set(v___x_2457_, 9, v_maxHeartbeats_2449_);
    crate::leanh::lean_ctor_set(v___x_2457_, 10, v_quotContext_2450_);
    crate::leanh::lean_ctor_set(v___x_2457_, 11, v_currMacroScope_2451_);
    crate::leanh::lean_ctor_set(v___x_2457_, 12, v_cancelTk_x3f_2453_);
    crate::leanh::lean_ctor_set(v___x_2457_, 13, v_inheritedTraceOptions_2455_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2457_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_2452_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2457_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2454_,
    );
    v___x_2458_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v_msg_2436_, v___x_2457_, v___y_2438_);
    crate::leanh::lean_dec_ref_known(v___x_2457_, 14);
    return v___x_2458_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg___boxed(
    mut v_ref_2459_: *mut crate::leanh::LeanObject,
    mut v_msg_2460_: *mut crate::leanh::LeanObject,
    mut v___y_2461_: *mut crate::leanh::LeanObject,
    mut v___y_2462_: *mut crate::leanh::LeanObject,
    mut v___y_2463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2464_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_ref_2459_, v_msg_2460_, v___y_2461_, v___y_2462_);
    crate::leanh::lean_dec(v___y_2462_);
    crate::leanh::lean_dec_ref(v___y_2461_);
    crate::leanh::lean_dec(v_ref_2459_);
    return v_res_2464_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2473_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__4;
    v___x_2474_ = l_Lean_stringToMessageData(v___x_2473_);
    return v___x_2474_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(
    mut v_x_2485_: *mut crate::leanh::LeanObject,
    mut v_a_2486_: *mut crate::leanh::LeanObject,
    mut v_a_2487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: u8 = 0;
    v___x_2489_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3;
    crate::leanh::lean_inc(v_x_2485_);
    v___x_2490_ = l_Lean_Syntax_isOfKind(v_x_2485_, v___x_2489_);
    if v___x_2490_ == 0 {
        let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2491_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5
            ),
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5_once
            ),
            _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5,
        );
        v___x_2492_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_2485_, v___x_2491_, v_a_2486_, v_a_2487_);
        crate::leanh::lean_dec(v_x_2485_);
        return v___x_2492_;
    } else {
        let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2496_: u8 = 0;
        v___x_2493_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2494_ = l_Lean_Syntax_getArg(v_x_2485_, v___x_2493_);
        v___x_2495_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7;
        crate::leanh::lean_inc(v___x_2494_);
        v___x_2496_ = l_Lean_Syntax_isOfKind(v___x_2494_, v___x_2495_);
        if v___x_2496_ == 0 {
            let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2498_: u8 = 0;
            v___x_2497_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9;
            v___x_2498_ = l_Lean_Syntax_isOfKind(v___x_2494_, v___x_2497_);
            if v___x_2498_ == 0 {
                let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2499_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5_once
                    ),
                    _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5,
                );
                v___x_2500_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_2485_, v___x_2499_, v_a_2486_, v_a_2487_);
                crate::leanh::lean_dec(v_x_2485_);
                return v___x_2500_;
            } else {
                let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_x_2485_);
                v___x_2501_ = crate::leanh::lean_box((v___x_2496_) as usize);
                v___x_2502_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2502_, 0, v___x_2501_);
                return v___x_2502_;
            }
        } else {
            let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_2494_);
            crate::leanh::lean_dec(v_x_2485_);
            v___x_2503_ = crate::leanh::lean_box((v___x_2496_) as usize);
            v___x_2504_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2504_, 0, v___x_2503_);
            return v___x_2504_;
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___boxed(
    mut v_x_2505_: *mut crate::leanh::LeanObject,
    mut v_a_2506_: *mut crate::leanh::LeanObject,
    mut v_a_2507_: *mut crate::leanh::LeanObject,
    mut v_a_2508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2509_ =
        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(v_x_2505_, v_a_2506_, v_a_2507_);
    crate::leanh::lean_dec(v_a_2507_);
    crate::leanh::lean_dec_ref(v_a_2506_);
    return v_res_2509_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0(
    mut v_00_u03b1_2510_: *mut crate::leanh::LeanObject,
    mut v_ref_2511_: *mut crate::leanh::LeanObject,
    mut v_msg_2512_: *mut crate::leanh::LeanObject,
    mut v___y_2513_: *mut crate::leanh::LeanObject,
    mut v___y_2514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2516_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_ref_2511_, v_msg_2512_, v___y_2513_, v___y_2514_);
    return v___x_2516_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___boxed(
    mut v_00_u03b1_2517_: *mut crate::leanh::LeanObject,
    mut v_ref_2518_: *mut crate::leanh::LeanObject,
    mut v_msg_2519_: *mut crate::leanh::LeanObject,
    mut v___y_2520_: *mut crate::leanh::LeanObject,
    mut v___y_2521_: *mut crate::leanh::LeanObject,
    mut v___y_2522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2523_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0(v_00_u03b1_2517_, v_ref_2518_, v_msg_2519_, v___y_2520_, v___y_2521_);
    crate::leanh::lean_dec(v___y_2521_);
    crate::leanh::lean_dec_ref(v___y_2520_);
    crate::leanh::lean_dec(v_ref_2518_);
    return v_res_2523_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0(
    mut v_00_u03b1_2524_: *mut crate::leanh::LeanObject,
    mut v_msg_2525_: *mut crate::leanh::LeanObject,
    mut v___y_2526_: *mut crate::leanh::LeanObject,
    mut v___y_2527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2529_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v_msg_2525_, v___y_2526_, v___y_2527_);
    return v___x_2529_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___boxed(
    mut v_00_u03b1_2530_: *mut crate::leanh::LeanObject,
    mut v_msg_2531_: *mut crate::leanh::LeanObject,
    mut v___y_2532_: *mut crate::leanh::LeanObject,
    mut v___y_2533_: *mut crate::leanh::LeanObject,
    mut v___y_2534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2535_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0(v_00_u03b1_2530_, v_msg_2531_, v___y_2532_, v___y_2533_);
    crate::leanh::lean_dec(v___y_2533_);
    crate::leanh::lean_dec_ref(v___y_2532_);
    return v_res_2535_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(
    mut v___x_2536_: *mut crate::leanh::LeanObject,
    mut v_s_2537_: *mut crate::leanh::LeanObject,
    mut v_a_2538_: *mut crate::leanh::LeanObject,
    mut v_b_2539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: u8 = 0;
    let mut v___x_2544_: u32 = 0;
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: u32 = 0;
    let mut v___x_2547_: u8 = 0;
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: u32 = 0;
    let mut v___x_2551_: u32 = 0;
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_2540_ = crate::leanh::lean_ctor_get(v___x_2536_, 1);
                v_endExclusive_2541_ = crate::leanh::lean_ctor_get(v___x_2536_, 2);
                v___x_2542_ = lean_nat_sub(v_endExclusive_2541_, v_startInclusive_2540_);
                v___x_2543_ = lean_nat_dec_eq(v_a_2538_, v___x_2542_);
                crate::leanh::lean_dec(v___x_2542_);
                if v___x_2543_ == 0 {
                    v___x_2544_ = lean_string_utf8_get_fast(v_s_2537_, v_a_2538_);
                    v___x_2545_ = lean_string_utf8_next_fast(v_s_2537_, v_a_2538_);
                    crate::leanh::lean_dec(v_a_2538_);
                    v___x_2546_ = 95;
                    v___x_2547_ = lean_uint32_dec_eq(v___x_2544_, v___x_2546_);
                    if v___x_2547_ == 0 {
                        v___x_2548_ = crate::leanh::lean_unsigned_to_nat(10);
                        v___x_2549_ = lean_nat_mul(v_b_2539_, v___x_2548_);
                        crate::leanh::lean_dec(v_b_2539_);
                        v___x_2550_ = 48;
                        v___x_2551_ = lean_uint32_sub(v___x_2544_, v___x_2550_);
                        v___x_2552_ = lean_uint32_to_nat(v___x_2551_);
                        v___x_2553_ = lean_nat_add(v___x_2549_, v___x_2552_);
                        crate::leanh::lean_dec(v___x_2552_);
                        crate::leanh::lean_dec(v___x_2549_);
                        v_a_2538_ = v___x_2545_;
                        v_b_2539_ = v___x_2553_;
                        state = 0;
                        continue;
                    } else {
                        v_a_2538_ = v___x_2545_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2538_);
                    return v_b_2539_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg___boxed(
    mut v___x_2556_: *mut crate::leanh::LeanObject,
    mut v_s_2557_: *mut crate::leanh::LeanObject,
    mut v_a_2558_: *mut crate::leanh::LeanObject,
    mut v_b_2559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2560_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(v___x_2556_, v_s_2557_, v_a_2558_, v_b_2559_);
    crate::leanh::lean_dec_ref(v_s_2557_);
    crate::leanh::lean_dec_ref(v___x_2556_);
    return v_res_2560_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(
    mut v_s_2561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2562_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2563_ = lean_string_utf8_byte_size(v_s_2561_);
    crate::leanh::lean_inc_ref(v_s_2561_);
    v___x_2564_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2564_, 0, v_s_2561_);
    crate::leanh::lean_ctor_set(v___x_2564_, 1, v___x_2562_);
    crate::leanh::lean_ctor_set(v___x_2564_, 2, v___x_2563_);
    v___x_2565_ = l_String_Slice_positions(v___x_2564_);
    v___x_2566_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(v___x_2564_, v_s_2561_, v___x_2565_, v___x_2562_);
    crate::leanh::lean_dec_ref(v_s_2561_);
    crate::leanh::lean_dec_ref_known(v___x_2564_, 3);
    return v___x_2566_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0(
    mut v___x_2567_: *mut crate::leanh::LeanObject,
    mut v_s_2568_: *mut crate::leanh::LeanObject,
    mut v_inst_2569_: *mut crate::leanh::LeanObject,
    mut v_R_2570_: *mut crate::leanh::LeanObject,
    mut v_a_2571_: *mut crate::leanh::LeanObject,
    mut v_b_2572_: *mut crate::leanh::LeanObject,
    mut v_c_2573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2574_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(v___x_2567_, v_s_2568_, v_a_2571_, v_b_2572_);
    return v___x_2574_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___boxed(
    mut v___x_2575_: *mut crate::leanh::LeanObject,
    mut v_s_2576_: *mut crate::leanh::LeanObject,
    mut v_inst_2577_: *mut crate::leanh::LeanObject,
    mut v_R_2578_: *mut crate::leanh::LeanObject,
    mut v_a_2579_: *mut crate::leanh::LeanObject,
    mut v_b_2580_: *mut crate::leanh::LeanObject,
    mut v_c_2581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2582_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0(v___x_2575_, v_s_2576_, v_inst_2577_, v_R_2578_, v_a_2579_, v_b_2580_, v_c_2581_);
    crate::leanh::lean_dec_ref(v_s_2576_);
    crate::leanh::lean_dec_ref(v___x_2575_);
    return v_res_2582_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeSign(
    mut v_s_2583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2585_: u32 = 0;
    let mut v___x_2586_: u32 = 0;
    let mut v___x_2587_: u8 = 0;
    let mut v___x_2588_: u32 = 0;
    let mut v___x_2589_: u8 = 0;
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: u32 = 0;
    let mut v_val_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2608_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2609_ = lean_string_utf8_byte_size(v_s_2583_);
                crate::leanh::lean_inc_ref(v_s_2583_);
                v___x_2610_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2610_, 0, v_s_2583_);
                crate::leanh::lean_ctor_set(v___x_2610_, 1, v___x_2608_);
                crate::leanh::lean_ctor_set(v___x_2610_, 2, v___x_2609_);
                v___x_2611_ = l_String_Slice_Pos_get_x3f(v___x_2610_, v___x_2608_);
                crate::leanh::lean_dec_ref_known(v___x_2610_, 3);
                if crate::leanh::lean_obj_tag(v___x_2611_) == 0 {
                    v___x_2612_ = 65;
                    v___y_2585_ = v___x_2612_;
                    state = 1;
                    continue;
                } else {
                    v_val_2613_ = crate::leanh::lean_ctor_get(v___x_2611_, 0);
                    crate::leanh::lean_inc(v_val_2613_);
                    crate::leanh::lean_dec_ref_known(v___x_2611_, 1);
                    v___x_2614_ = crate::leanh::lean_unbox_uint32(v_val_2613_);
                    crate::leanh::lean_dec(v_val_2613_);
                    v___y_2585_ = v___x_2614_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2586_ = 45;
                v___x_2587_ = lean_uint32_dec_eq(v___y_2585_, v___x_2586_);
                if v___x_2587_ == 0 {
                    v___x_2588_ = 43;
                    v___x_2589_ = lean_uint32_dec_eq(v___y_2585_, v___x_2588_);
                    if v___x_2589_ == 0 {
                        v___x_2590_ = crate::leanh::lean_box((v___x_2589_) as usize);
                        v___x_2591_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2591_, 0, v___x_2590_);
                        crate::leanh::lean_ctor_set(v___x_2591_, 1, v_s_2583_);
                        return v___x_2591_;
                    } else {
                        v___x_2592_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2593_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2594_ = lean_string_utf8_byte_size(v_s_2583_);
                        crate::leanh::lean_inc_ref(v_s_2583_);
                        v___x_2595_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2595_, 0, v_s_2583_);
                        crate::leanh::lean_ctor_set(v___x_2595_, 1, v___x_2593_);
                        crate::leanh::lean_ctor_set(v___x_2595_, 2, v___x_2594_);
                        v___x_2596_ =
                            l_String_Slice_Pos_nextn(v___x_2595_, v___x_2593_, v___x_2592_);
                        crate::leanh::lean_dec_ref_known(v___x_2595_, 3);
                        v___x_2597_ = lean_string_utf8_extract(v_s_2583_, v___x_2596_, v___x_2594_);
                        crate::leanh::lean_dec(v___x_2596_);
                        crate::leanh::lean_dec_ref(v_s_2583_);
                        v___x_2598_ = crate::leanh::lean_box((v___x_2587_) as usize);
                        v___x_2599_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2599_, 0, v___x_2598_);
                        crate::leanh::lean_ctor_set(v___x_2599_, 1, v___x_2597_);
                        return v___x_2599_;
                    }
                } else {
                    v___x_2600_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2601_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2602_ = lean_string_utf8_byte_size(v_s_2583_);
                    crate::leanh::lean_inc_ref(v_s_2583_);
                    v___x_2603_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2603_, 0, v_s_2583_);
                    crate::leanh::lean_ctor_set(v___x_2603_, 1, v___x_2601_);
                    crate::leanh::lean_ctor_set(v___x_2603_, 2, v___x_2602_);
                    v___x_2604_ = l_String_Slice_Pos_nextn(v___x_2603_, v___x_2601_, v___x_2600_);
                    crate::leanh::lean_dec_ref_known(v___x_2603_, 3);
                    v___x_2605_ = lean_string_utf8_extract(v_s_2583_, v___x_2604_, v___x_2602_);
                    crate::leanh::lean_dec(v___x_2604_);
                    crate::leanh::lean_dec_ref(v_s_2583_);
                    v___x_2606_ = crate::leanh::lean_box((v___x_2587_) as usize);
                    v___x_2607_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2607_, 0, v___x_2606_);
                    crate::leanh::lean_ctor_set(v___x_2607_, 1, v___x_2605_);
                    return v___x_2607_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(
    mut v_s_2615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2617_: u8 = 0;
    let mut v_snd_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2624_: u32 = 0;
    let mut v___x_2625_: u32 = 0;
    let mut v___x_2626_: u8 = 0;
    let mut v___x_2627_: u32 = 0;
    let mut v___x_2628_: u8 = 0;
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: u32 = 0;
    let mut v_val_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2641_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2642_ = lean_string_utf8_byte_size(v_s_2615_);
                crate::leanh::lean_inc_ref(v_s_2615_);
                v___x_2643_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2643_, 0, v_s_2615_);
                crate::leanh::lean_ctor_set(v___x_2643_, 1, v___x_2641_);
                crate::leanh::lean_ctor_set(v___x_2643_, 2, v___x_2642_);
                v___x_2644_ = l_String_Slice_Pos_get_x3f(v___x_2643_, v___x_2641_);
                crate::leanh::lean_dec_ref_known(v___x_2643_, 3);
                if crate::leanh::lean_obj_tag(v___x_2644_) == 0 {
                    v___x_2645_ = 65;
                    v___y_2624_ = v___x_2645_;
                    state = 2;
                    continue;
                } else {
                    v_val_2646_ = crate::leanh::lean_ctor_get(v___x_2644_, 0);
                    crate::leanh::lean_inc(v_val_2646_);
                    crate::leanh::lean_dec_ref_known(v___x_2644_, 1);
                    v___x_2647_ = crate::leanh::lean_unbox_uint32(v_val_2646_);
                    crate::leanh::lean_dec(v_val_2646_);
                    v___y_2624_ = v___x_2647_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v_fst_2617_ == 0 {
                    v___x_2619_ =
                        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(v_snd_2618_);
                    v___x_2620_ = lean_nat_to_int(v___x_2619_);
                    return v___x_2620_;
                } else {
                    v___x_2621_ =
                        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(v_snd_2618_);
                    v___x_2622_ = l_Int_negOfNat(v___x_2621_);
                    crate::leanh::lean_dec(v___x_2621_);
                    return v___x_2622_;
                }
            }
            2 => {
                v___x_2625_ = 45;
                v___x_2626_ = lean_uint32_dec_eq(v___y_2624_, v___x_2625_);
                if v___x_2626_ == 0 {
                    v___x_2627_ = 43;
                    v___x_2628_ = lean_uint32_dec_eq(v___y_2624_, v___x_2627_);
                    if v___x_2628_ == 0 {
                        v_fst_2617_ = v___x_2628_;
                        v_snd_2618_ = v_s_2615_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2629_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2630_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2631_ = lean_string_utf8_byte_size(v_s_2615_);
                        crate::leanh::lean_inc_ref(v_s_2615_);
                        v___x_2632_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2632_, 0, v_s_2615_);
                        crate::leanh::lean_ctor_set(v___x_2632_, 1, v___x_2630_);
                        crate::leanh::lean_ctor_set(v___x_2632_, 2, v___x_2631_);
                        v___x_2633_ =
                            l_String_Slice_Pos_nextn(v___x_2632_, v___x_2630_, v___x_2629_);
                        crate::leanh::lean_dec_ref_known(v___x_2632_, 3);
                        v___x_2634_ = lean_string_utf8_extract(v_s_2615_, v___x_2633_, v___x_2631_);
                        crate::leanh::lean_dec(v___x_2633_);
                        crate::leanh::lean_dec_ref(v_s_2615_);
                        v_fst_2617_ = v___x_2626_;
                        v_snd_2618_ = v___x_2634_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2635_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2636_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2637_ = lean_string_utf8_byte_size(v_s_2615_);
                    crate::leanh::lean_inc_ref(v_s_2615_);
                    v___x_2638_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2638_, 0, v_s_2615_);
                    crate::leanh::lean_ctor_set(v___x_2638_, 1, v___x_2636_);
                    crate::leanh::lean_ctor_set(v___x_2638_, 2, v___x_2637_);
                    v___x_2639_ = l_String_Slice_Pos_nextn(v___x_2638_, v___x_2636_, v___x_2635_);
                    crate::leanh::lean_dec_ref_known(v___x_2638_, 3);
                    v___x_2640_ = lean_string_utf8_extract(v_s_2615_, v___x_2639_, v___x_2637_);
                    crate::leanh::lean_dec(v___x_2639_);
                    crate::leanh::lean_dec_ref(v_s_2615_);
                    v_fst_2617_ = v___x_2626_;
                    v_snd_2618_ = v___x_2640_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2656_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__3;
    v___x_2657_ = l_Lean_MessageData_ofFormat(v___x_2656_);
    return v___x_2657_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(
    mut v_x_2658_: *mut crate::leanh::LeanObject,
    mut v_a_2659_: *mut crate::leanh::LeanObject,
    mut v_a_2660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2674_: u8 = 0;
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2678_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2666_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1;
                v___x_2667_ = l_Lean_Syntax_isLit_x3f(v___x_2666_, v_x_2658_);
                if crate::leanh::lean_obj_tag(v___x_2667_) == 1 {
                    v_val_2668_ = crate::leanh::lean_ctor_get(v___x_2667_, 0);
                    crate::leanh::lean_inc(v_val_2668_);
                    crate::leanh::lean_dec_ref_known(v___x_2667_, 1);
                    v_a_2663_ = v_val_2668_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2667_);
                    v___x_2669_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4_once), _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4);
                    v___x_2670_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_2658_, v___x_2669_, v_a_2659_, v_a_2660_);
                    v_a_2671_ = crate::leanh::lean_ctor_get(v___x_2670_, 0);
                    v_isSharedCheck_2678_ = (!crate::leanh::lean_is_exclusive(v___x_2670_)) as u8;
                    if v_isSharedCheck_2678_ == 0 {
                        v___x_2673_ = v___x_2670_;
                        v_isShared_2674_ = v_isSharedCheck_2678_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2671_);
                        crate::leanh::lean_dec(v___x_2670_);
                        v___x_2673_ = crate::leanh::lean_box(0);
                        v_isShared_2674_ = v_isSharedCheck_2678_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2664_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(v_a_2663_);
                v___x_2665_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2665_, 0, v___x_2664_);
                return v___x_2665_;
            }
            2 => {
                if v_isShared_2674_ == 0 {
                    v___x_2676_ = v___x_2673_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2677_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2671_);
                    v___x_2676_ = v_reuseFailAlloc_2677_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2676_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___boxed(
    mut v_x_2679_: *mut crate::leanh::LeanObject,
    mut v_a_2680_: *mut crate::leanh::LeanObject,
    mut v_a_2681_: *mut crate::leanh::LeanObject,
    mut v_a_2682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2683_ =
        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(v_x_2679_, v_a_2680_, v_a_2681_);
    crate::leanh::lean_dec(v_a_2681_);
    crate::leanh::lean_dec_ref(v_a_2680_);
    crate::leanh::lean_dec(v_x_2679_);
    return v_res_2683_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(
    mut v___x_2684_: *mut crate::leanh::LeanObject,
    mut v_s_2685_: *mut crate::leanh::LeanObject,
    mut v_a_2686_: *mut crate::leanh::LeanObject,
    mut v_b_2687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: u8 = 0;
    let mut v_fst_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: u32 = 0;
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: u32 = 0;
    let mut v___x_2697_: u8 = 0;
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2700_: u8 = 0;
    let mut v___x_2701_: u32 = 0;
    let mut v___x_2702_: u8 = 0;
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: u32 = 0;
    let mut v___x_2706_: u32 = 0;
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2720_: u8 = 0;
    let mut v_unused_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_2688_ = crate::leanh::lean_ctor_get(v___x_2684_, 1);
                v_endExclusive_2689_ = crate::leanh::lean_ctor_get(v___x_2684_, 2);
                v___x_2690_ = lean_nat_sub(v_endExclusive_2689_, v_startInclusive_2688_);
                v___x_2691_ = lean_nat_dec_eq(v_a_2686_, v___x_2690_);
                crate::leanh::lean_dec(v___x_2690_);
                if v___x_2691_ == 0 {
                    v_fst_2692_ = crate::leanh::lean_ctor_get(v_b_2687_, 0);
                    v_snd_2693_ = crate::leanh::lean_ctor_get(v_b_2687_, 1);
                    v___x_2694_ = lean_string_utf8_get_fast(v_s_2685_, v_a_2686_);
                    v___x_2695_ = lean_string_utf8_next_fast(v_s_2685_, v_a_2686_);
                    crate::leanh::lean_dec(v_a_2686_);
                    v___x_2696_ = 95;
                    v___x_2697_ = lean_uint32_dec_eq(v___x_2694_, v___x_2696_);
                    if v___x_2697_ == 0 {
                        crate::leanh::lean_inc(v_snd_2693_);
                        crate::leanh::lean_inc(v_fst_2692_);
                        v_isSharedCheck_2720_ = (!crate::leanh::lean_is_exclusive(v_b_2687_)) as u8;
                        if v_isSharedCheck_2720_ == 0 {
                            v_unused_2721_ = crate::leanh::lean_ctor_get(v_b_2687_, 1);
                            crate::leanh::lean_dec(v_unused_2721_);
                            v_unused_2722_ = crate::leanh::lean_ctor_get(v_b_2687_, 0);
                            crate::leanh::lean_dec(v_unused_2722_);
                            v___x_2699_ = v_b_2687_;
                            v_isShared_2700_ = v_isSharedCheck_2720_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_b_2687_);
                            v___x_2699_ = crate::leanh::lean_box(0);
                            v_isShared_2700_ = v_isSharedCheck_2720_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2686_ = v___x_2695_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2686_);
                    return v_b_2687_;
                }
            }
            1 => {
                v___x_2701_ = 46;
                v___x_2702_ = lean_uint32_dec_eq(v___x_2694_, v___x_2701_);
                if v___x_2702_ == 0 {
                    v___x_2703_ = crate::leanh::lean_unsigned_to_nat(10);
                    v___x_2704_ = lean_nat_mul(v_fst_2692_, v___x_2703_);
                    crate::leanh::lean_dec(v_fst_2692_);
                    v___x_2705_ = 48;
                    v___x_2706_ = lean_uint32_sub(v___x_2694_, v___x_2705_);
                    v___x_2707_ = lean_uint32_to_nat(v___x_2706_);
                    v___x_2708_ = lean_nat_add(v___x_2704_, v___x_2707_);
                    crate::leanh::lean_dec(v___x_2707_);
                    crate::leanh::lean_dec(v___x_2704_);
                    v___x_2709_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2710_ = lean_nat_add(v_snd_2693_, v___x_2709_);
                    crate::leanh::lean_dec(v_snd_2693_);
                    if v_isShared_2700_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2699_, 1, v___x_2710_);
                        crate::leanh::lean_ctor_set(v___x_2699_, 0, v___x_2708_);
                        v___x_2712_ = v___x_2699_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2714_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___x_2708_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2714_, 1, v___x_2710_);
                        v___x_2712_ = v_reuseFailAlloc_2714_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_2693_);
                    v___x_2715_ = crate::leanh::lean_unsigned_to_nat(0);
                    if v_isShared_2700_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2699_, 1, v___x_2715_);
                        v___x_2717_ = v___x_2699_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2719_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_fst_2692_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2719_, 1, v___x_2715_);
                        v___x_2717_ = v_reuseFailAlloc_2719_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_a_2686_ = v___x_2695_;
                v_b_2687_ = v___x_2712_;
                state = 0;
                continue;
            }
            3 => {
                v_a_2686_ = v___x_2695_;
                v_b_2687_ = v___x_2717_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg___boxed(
    mut v___x_2724_: *mut crate::leanh::LeanObject,
    mut v_s_2725_: *mut crate::leanh::LeanObject,
    mut v_a_2726_: *mut crate::leanh::LeanObject,
    mut v_b_2727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2728_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(v___x_2724_, v_s_2725_, v_a_2726_, v_b_2727_);
    crate::leanh::lean_dec_ref(v_s_2725_);
    crate::leanh::lean_dec_ref(v___x_2724_);
    return v_res_2728_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(
    mut v_s_2729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: u8 = 0;
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2742_: u8 = 0;
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2746_: u8 = 0;
    let mut v_unused_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2730_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2731_ = lean_string_utf8_byte_size(v_s_2729_);
                v___x_2732_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2732_, 0, v___x_2730_);
                crate::leanh::lean_ctor_set(v___x_2732_, 1, v___x_2731_);
                crate::leanh::lean_inc_ref(v_s_2729_);
                v___x_2733_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2733_, 0, v_s_2729_);
                crate::leanh::lean_ctor_set(v___x_2733_, 1, v___x_2730_);
                crate::leanh::lean_ctor_set(v___x_2733_, 2, v___x_2731_);
                v___x_2734_ = l_String_Slice_positions(v___x_2733_);
                v___x_2735_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(v___x_2733_, v_s_2729_, v___x_2734_, v___x_2732_);
                crate::leanh::lean_dec_ref_known(v___x_2733_, 3);
                v_fst_2736_ = crate::leanh::lean_ctor_get(v___x_2735_, 0);
                crate::leanh::lean_inc(v_fst_2736_);
                v_snd_2737_ = crate::leanh::lean_ctor_get(v___x_2735_, 1);
                crate::leanh::lean_inc(v_snd_2737_);
                v___x_2738_ = lean_string_length(v_s_2729_);
                crate::leanh::lean_dec_ref(v_s_2729_);
                v___x_2739_ = lean_nat_dec_le(v___x_2738_, v_snd_2737_);
                crate::leanh::lean_dec(v_snd_2737_);
                if v___x_2739_ == 0 {
                    crate::leanh::lean_dec(v_fst_2736_);
                    return v___x_2735_;
                } else {
                    v_isSharedCheck_2746_ = (!crate::leanh::lean_is_exclusive(v___x_2735_)) as u8;
                    if v_isSharedCheck_2746_ == 0 {
                        v_unused_2747_ = crate::leanh::lean_ctor_get(v___x_2735_, 1);
                        crate::leanh::lean_dec(v_unused_2747_);
                        v_unused_2748_ = crate::leanh::lean_ctor_get(v___x_2735_, 0);
                        crate::leanh::lean_dec(v_unused_2748_);
                        v___x_2741_ = v___x_2735_;
                        v_isShared_2742_ = v_isSharedCheck_2746_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2735_);
                        v___x_2741_ = crate::leanh::lean_box(0);
                        v_isShared_2742_ = v_isSharedCheck_2746_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2742_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2741_, 1, v___x_2730_);
                    v___x_2744_ = v___x_2741_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2745_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_fst_2736_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2745_, 1, v___x_2730_);
                    v___x_2744_ = v_reuseFailAlloc_2745_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2744_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0(
    mut v___x_2749_: *mut crate::leanh::LeanObject,
    mut v_s_2750_: *mut crate::leanh::LeanObject,
    mut v_inst_2751_: *mut crate::leanh::LeanObject,
    mut v_R_2752_: *mut crate::leanh::LeanObject,
    mut v_a_2753_: *mut crate::leanh::LeanObject,
    mut v_b_2754_: *mut crate::leanh::LeanObject,
    mut v_c_2755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2756_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(v___x_2749_, v_s_2750_, v_a_2753_, v_b_2754_);
    return v___x_2756_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___boxed(
    mut v___x_2757_: *mut crate::leanh::LeanObject,
    mut v_s_2758_: *mut crate::leanh::LeanObject,
    mut v_inst_2759_: *mut crate::leanh::LeanObject,
    mut v_R_2760_: *mut crate::leanh::LeanObject,
    mut v_a_2761_: *mut crate::leanh::LeanObject,
    mut v_b_2762_: *mut crate::leanh::LeanObject,
    mut v_c_2763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2764_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0(v___x_2757_, v_s_2758_, v_inst_2759_, v_R_2760_, v_a_2761_, v_b_2762_, v_c_2763_);
    crate::leanh::lean_dec_ref(v_s_2758_);
    crate::leanh::lean_dec_ref(v___x_2757_);
    return v_res_2764_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(
    mut v_s_2767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2768_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0;
    return v___x_2768_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___boxed(
    mut v_s_2769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2770_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(v_s_2769_);
    crate::leanh::lean_dec_ref(v_s_2769_);
    return v_res_2770_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(
    mut v_s_2771_: *mut crate::leanh::LeanObject,
    mut v___x_2772_: *mut crate::leanh::LeanObject,
    mut v___x_2773_: *mut crate::leanh::LeanObject,
    mut v_a_2774_: *mut crate::leanh::LeanObject,
    mut v_b_2775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2788_: u8 = 0;
    let mut v___y_2790_: u8 = 0;
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: u8 = 0;
    let mut v___x_2809_: u32 = 0;
    let mut v___x_2810_: u32 = 0;
    let mut v___x_2811_: u8 = 0;
    let mut v___x_2812_: u32 = 0;
    let mut v___x_2813_: u8 = 0;
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2815_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2774_) == 0 {
                    v_currPos_2784_ = crate::leanh::lean_ctor_get(v_a_2774_, 0);
                    v_searcher_2785_ = crate::leanh::lean_ctor_get(v_a_2774_, 1);
                    v_isSharedCheck_2815_ = (!crate::leanh::lean_is_exclusive(v_a_2774_)) as u8;
                    if v_isSharedCheck_2815_ == 0 {
                        v___x_2787_ = v_a_2774_;
                        v_isShared_2788_ = v_isSharedCheck_2815_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_2785_);
                        crate::leanh::lean_inc(v_currPos_2784_);
                        crate::leanh::lean_dec(v_a_2774_);
                        v___x_2787_ = crate::leanh::lean_box(0);
                        v_isShared_2788_ = v_isSharedCheck_2815_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2773_);
                    crate::leanh::lean_dec_ref(v_s_2771_);
                    return v_b_2775_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_s_2771_);
                v___x_2780_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2780_, 0, v_s_2771_);
                crate::leanh::lean_ctor_set(v___x_2780_, 1, v_startInclusive_2778_);
                crate::leanh::lean_ctor_set(v___x_2780_, 2, v_endExclusive_2779_);
                v___x_2781_ = l_String_Slice_toString(v___x_2780_);
                crate::leanh::lean_dec_ref_known(v___x_2780_, 3);
                v___x_2782_ = lean_array_push(v_b_2775_, v___x_2781_);
                v_a_2774_ = v_it_2777_;
                v_b_2775_ = v___x_2782_;
                state = 0;
                continue;
            }
            2 => {
                v_startInclusive_2805_ = crate::leanh::lean_ctor_get(v___x_2772_, 1);
                v_endExclusive_2806_ = crate::leanh::lean_ctor_get(v___x_2772_, 2);
                v___x_2807_ = lean_nat_sub(v_endExclusive_2806_, v_startInclusive_2805_);
                v___x_2808_ = lean_nat_dec_eq(v_searcher_2785_, v___x_2807_);
                crate::leanh::lean_dec(v___x_2807_);
                if v___x_2808_ == 0 {
                    v___x_2809_ = lean_string_utf8_get_fast(v_s_2771_, v_searcher_2785_);
                    v___x_2810_ = 69;
                    v___x_2811_ = lean_uint32_dec_eq(v___x_2809_, v___x_2810_);
                    if v___x_2811_ == 0 {
                        v___x_2812_ = 101;
                        v___x_2813_ = lean_uint32_dec_eq(v___x_2809_, v___x_2812_);
                        v___y_2790_ = v___x_2813_;
                        state = 3;
                        continue;
                    } else {
                        v___y_2790_ = v___x_2811_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2787_);
                    crate::leanh::lean_dec(v_searcher_2785_);
                    v___x_2814_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc(v___x_2773_);
                    v_it_2777_ = v___x_2814_;
                    v_startInclusive_2778_ = v_currPos_2784_;
                    v_endExclusive_2779_ = v___x_2773_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_2790_ == 0 {
                    v___x_2791_ = lean_string_utf8_next_fast(v_s_2771_, v_searcher_2785_);
                    crate::leanh::lean_dec(v_searcher_2785_);
                    if v_isShared_2788_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2787_, 1, v___x_2791_);
                        v___x_2793_ = v___x_2787_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2795_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_currPos_2784_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2795_, 1, v___x_2791_);
                        v___x_2793_ = v_reuseFailAlloc_2795_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_2796_ = lean_string_utf8_next_fast(v_s_2771_, v_searcher_2785_);
                    v___x_2797_ = lean_nat_sub(v___x_2796_, v_searcher_2785_);
                    v___x_2798_ = lean_nat_add(v_searcher_2785_, v___x_2797_);
                    crate::leanh::lean_dec(v___x_2797_);
                    v_slice_2799_ =
                        l_String_Slice_subslice_x21(v___x_2772_, v_currPos_2784_, v_searcher_2785_);
                    crate::leanh::lean_inc(v___x_2798_);
                    if v_isShared_2788_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2787_, 1, v___x_2798_);
                        crate::leanh::lean_ctor_set(v___x_2787_, 0, v___x_2798_);
                        v_nextIt_2801_ = v___x_2787_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2804_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2798_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2804_, 1, v___x_2798_);
                        v_nextIt_2801_ = v_reuseFailAlloc_2804_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v_a_2774_ = v___x_2793_;
                state = 0;
                continue;
            }
            5 => {
                v_startInclusive_2802_ = crate::leanh::lean_ctor_get(v_slice_2799_, 0);
                crate::leanh::lean_inc(v_startInclusive_2802_);
                v_endExclusive_2803_ = crate::leanh::lean_ctor_get(v_slice_2799_, 1);
                crate::leanh::lean_inc(v_endExclusive_2803_);
                crate::leanh::lean_dec_ref(v_slice_2799_);
                v_it_2777_ = v_nextIt_2801_;
                v_startInclusive_2778_ = v_startInclusive_2802_;
                v_endExclusive_2779_ = v_endExclusive_2803_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg___boxed(
    mut v_s_2816_: *mut crate::leanh::LeanObject,
    mut v___x_2817_: *mut crate::leanh::LeanObject,
    mut v___x_2818_: *mut crate::leanh::LeanObject,
    mut v_a_2819_: *mut crate::leanh::LeanObject,
    mut v_b_2820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2821_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_2816_, v___x_2817_, v___x_2818_, v_a_2819_, v_b_2820_);
    crate::leanh::lean_dec_ref(v___x_2817_);
    return v_res_2821_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2822_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2823_ = lean_nat_to_int(v___x_2822_);
    return v___x_2823_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2824_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0_once
        ),
        _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0,
    );
    v___x_2825_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2826_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2826_, 0, v___x_2825_);
    crate::leanh::lean_ctor_set(v___x_2826_, 1, v___x_2824_);
    return v___x_2826_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp(
    mut v_s_2829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2846_: u8 = 0;
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2851_: u8 = 0;
    let mut v_tail_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2860_: u8 = 0;
    let mut v_exp_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2832_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2833_ = lean_string_utf8_byte_size(v_s_2829_);
                crate::leanh::lean_inc_ref(v_s_2829_);
                v___x_2834_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2834_, 0, v_s_2829_);
                crate::leanh::lean_ctor_set(v___x_2834_, 1, v___x_2832_);
                crate::leanh::lean_ctor_set(v___x_2834_, 2, v___x_2833_);
                v___x_2835_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(v___x_2834_);
                v___x_2836_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2;
                v___x_2837_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_2829_, v___x_2834_, v___x_2833_, v___x_2835_, v___x_2836_);
                crate::leanh::lean_dec_ref_known(v___x_2834_, 3);
                v___x_2838_ = lean_array_to_list(v___x_2837_);
                if crate::leanh::lean_obj_tag(v___x_2838_) == 1 {
                    v_tail_2839_ = crate::leanh::lean_ctor_get(v___x_2838_, 1);
                    crate::leanh::lean_inc(v_tail_2839_);
                    if crate::leanh::lean_obj_tag(v_tail_2839_) == 0 {
                        v_head_2840_ = crate::leanh::lean_ctor_get(v___x_2838_, 0);
                        crate::leanh::lean_inc(v_head_2840_);
                        crate::leanh::lean_dec_ref_known(v___x_2838_, 2);
                        v___x_2841_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(
                            v_head_2840_,
                        );
                        v_fst_2842_ = crate::leanh::lean_ctor_get(v___x_2841_, 0);
                        v_snd_2843_ = crate::leanh::lean_ctor_get(v___x_2841_, 1);
                        v_isSharedCheck_2851_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2841_)) as u8;
                        if v_isSharedCheck_2851_ == 0 {
                            v___x_2845_ = v___x_2841_;
                            v_isShared_2846_ = v_isSharedCheck_2851_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_2843_);
                            crate::leanh::lean_inc(v_fst_2842_);
                            crate::leanh::lean_dec(v___x_2841_);
                            v___x_2845_ = crate::leanh::lean_box(0);
                            v_isShared_2846_ = v_isSharedCheck_2851_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_tail_2852_ = crate::leanh::lean_ctor_get(v_tail_2839_, 1);
                        if crate::leanh::lean_obj_tag(v_tail_2852_) == 0 {
                            v_head_2853_ = crate::leanh::lean_ctor_get(v___x_2838_, 0);
                            crate::leanh::lean_inc(v_head_2853_);
                            crate::leanh::lean_dec_ref_known(v___x_2838_, 2);
                            v_head_2854_ = crate::leanh::lean_ctor_get(v_tail_2839_, 0);
                            crate::leanh::lean_inc(v_head_2854_);
                            crate::leanh::lean_dec_ref_known(v_tail_2839_, 2);
                            v___x_2855_ =
                                l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(
                                    v_head_2853_,
                                );
                            v_fst_2856_ = crate::leanh::lean_ctor_get(v___x_2855_, 0);
                            v_snd_2857_ = crate::leanh::lean_ctor_get(v___x_2855_, 1);
                            v_isSharedCheck_2867_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2855_)) as u8;
                            if v_isSharedCheck_2867_ == 0 {
                                v___x_2859_ = v___x_2855_;
                                v_isShared_2860_ = v_isSharedCheck_2867_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_2857_);
                                crate::leanh::lean_inc(v_fst_2856_);
                                crate::leanh::lean_dec(v___x_2855_);
                                v___x_2859_ = crate::leanh::lean_box(0);
                                v_isShared_2860_ = v_isSharedCheck_2867_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_tail_2839_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_2838_, 2);
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2838_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2831_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1_once
                    ),
                    _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1,
                );
                return v___x_2831_;
            }
            2 => {
                v___x_2847_ = l_Int_negOfNat(v_snd_2843_);
                crate::leanh::lean_dec(v_snd_2843_);
                if v_isShared_2846_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2845_, 1, v___x_2847_);
                    v___x_2849_ = v___x_2845_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2850_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_fst_2842_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2850_, 1, v___x_2847_);
                    v___x_2849_ = v_reuseFailAlloc_2850_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2849_;
            }
            4 => {
                v_exp_2861_ =
                    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(v_head_2854_);
                v___x_2862_ = l_Int_negOfNat(v_snd_2857_);
                crate::leanh::lean_dec(v_snd_2857_);
                v___x_2863_ = lean_int_add(v___x_2862_, v_exp_2861_);
                crate::leanh::lean_dec(v_exp_2861_);
                crate::leanh::lean_dec(v___x_2862_);
                if v_isShared_2860_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2859_, 1, v___x_2863_);
                    v___x_2865_ = v___x_2859_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2866_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_fst_2856_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2866_, 1, v___x_2863_);
                    v___x_2865_ = v_reuseFailAlloc_2866_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1(
    mut v_s_2868_: *mut crate::leanh::LeanObject,
    mut v___x_2869_: *mut crate::leanh::LeanObject,
    mut v___x_2870_: *mut crate::leanh::LeanObject,
    mut v_inst_2871_: *mut crate::leanh::LeanObject,
    mut v_R_2872_: *mut crate::leanh::LeanObject,
    mut v_a_2873_: *mut crate::leanh::LeanObject,
    mut v_b_2874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2875_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_2868_, v___x_2869_, v___x_2870_, v_a_2873_, v_b_2874_);
    return v___x_2875_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___boxed(
    mut v_s_2876_: *mut crate::leanh::LeanObject,
    mut v___x_2877_: *mut crate::leanh::LeanObject,
    mut v___x_2878_: *mut crate::leanh::LeanObject,
    mut v_inst_2879_: *mut crate::leanh::LeanObject,
    mut v_R_2880_: *mut crate::leanh::LeanObject,
    mut v_a_2881_: *mut crate::leanh::LeanObject,
    mut v_b_2882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2883_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1(v_s_2876_, v___x_2877_, v___x_2878_, v_inst_2879_, v_R_2880_, v_a_2881_, v_b_2882_);
    crate::leanh::lean_dec_ref(v___x_2877_);
    return v_res_2883_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2() -> f64 {
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: f64 = 0.0;
    v___x_2886_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2887_ = lean_float_of_nat(v___x_2886_);
    return v___x_2887_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(
    mut v_s_2888_: *mut crate::leanh::LeanObject,
) -> f64 {
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: u8 = 0;
    v___x_2889_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeSign(v_s_2888_);
    v_fst_2890_ = crate::leanh::lean_ctor_get(v___x_2889_, 0);
    crate::leanh::lean_inc(v_fst_2890_);
    v_snd_2891_ = crate::leanh::lean_ctor_get(v___x_2889_, 1);
    crate::leanh::lean_inc(v_snd_2891_);
    crate::leanh::lean_dec_ref(v___x_2889_);
    v___x_2892_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0;
    v___x_2893_ = lean_string_dec_eq(v_snd_2891_, v___x_2892_);
    if v___x_2893_ == 0 {
        let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2895_: u8 = 0;
        v___x_2894_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1;
        v___x_2895_ = lean_string_dec_eq(v_snd_2891_, v___x_2894_);
        if v___x_2895_ == 0 {
            let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2900_: u8 = 0;
            let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_flt_2902_: f64 = 0.0;
            let mut v___x_2903_: u8 = 0;
            v___x_2896_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp(v_snd_2891_);
            v_fst_2897_ = crate::leanh::lean_ctor_get(v___x_2896_, 0);
            crate::leanh::lean_inc(v_fst_2897_);
            v_snd_2898_ = crate::leanh::lean_ctor_get(v___x_2896_, 1);
            crate::leanh::lean_inc(v_snd_2898_);
            crate::leanh::lean_dec_ref(v___x_2896_);
            v___x_2899_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0
                ),
                core::ptr::addr_of_mut!(
                    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0_once
                ),
                _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0,
            );
            v___x_2900_ = lean_int_dec_lt(v_snd_2898_, v___x_2899_);
            v___x_2901_ = lean_nat_abs(v_snd_2898_);
            crate::leanh::lean_dec(v_snd_2898_);
            v_flt_2902_ = l_Float_ofScientific(v_fst_2897_, v___x_2900_, v___x_2901_);
            crate::leanh::lean_dec(v_fst_2897_);
            v___x_2903_ = (crate::leanh::lean_unbox(v_fst_2890_) as u8);
            crate::leanh::lean_dec(v_fst_2890_);
            if v___x_2903_ == 0 {
                return v_flt_2902_;
            } else {
                let mut v___x_2904_: f64 = 0.0;
                v___x_2904_ = lean_float_negate(v_flt_2902_);
                return v___x_2904_;
            }
        } else {
            let mut v___x_2905_: u8 = 0;
            crate::leanh::lean_dec(v_snd_2891_);
            v___x_2905_ = (crate::leanh::lean_unbox(v_fst_2890_) as u8);
            crate::leanh::lean_dec(v_fst_2890_);
            if v___x_2905_ == 0 {
                let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2908_: f64 = 0.0;
                let mut v___x_2909_: f64 = 0.0;
                let mut v___x_2910_: f64 = 0.0;
                v___x_2906_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2907_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2908_ = l_Float_ofScientific(v___x_2906_, v___x_2895_, v___x_2907_);
                v___x_2909_ = crate::leanh::lean_float_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once
                    ),
                    _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2,
                );
                v___x_2910_ = lean_float_div(v___x_2908_, v___x_2909_);
                return v___x_2910_;
            } else {
                let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2913_: f64 = 0.0;
                let mut v___x_2914_: f64 = 0.0;
                let mut v___x_2915_: f64 = 0.0;
                let mut v___x_2916_: f64 = 0.0;
                v___x_2911_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2912_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2913_ = l_Float_ofScientific(v___x_2911_, v___x_2895_, v___x_2912_);
                v___x_2914_ = crate::leanh::lean_float_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once
                    ),
                    _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2,
                );
                v___x_2915_ = lean_float_div(v___x_2913_, v___x_2914_);
                v___x_2916_ = lean_float_negate(v___x_2915_);
                return v___x_2916_;
            }
        }
    } else {
        let mut v___x_2917_: u8 = 0;
        crate::leanh::lean_dec(v_snd_2891_);
        v___x_2917_ = (crate::leanh::lean_unbox(v_fst_2890_) as u8);
        crate::leanh::lean_dec(v_fst_2890_);
        if v___x_2917_ == 0 {
            let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2920_: f64 = 0.0;
            let mut v___x_2921_: f64 = 0.0;
            let mut v___x_2922_: f64 = 0.0;
            v___x_2918_ = crate::leanh::lean_unsigned_to_nat(10);
            v___x_2919_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_2920_ = l_Float_ofScientific(v___x_2918_, v___x_2893_, v___x_2919_);
            v___x_2921_ = crate::leanh::lean_float_once(
                core::ptr::addr_of_mut!(
                    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2
                ),
                core::ptr::addr_of_mut!(
                    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once
                ),
                _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2,
            );
            v___x_2922_ = lean_float_div(v___x_2920_, v___x_2921_);
            return v___x_2922_;
        } else {
            let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2925_: f64 = 0.0;
            let mut v___x_2926_: f64 = 0.0;
            let mut v___x_2927_: f64 = 0.0;
            let mut v___x_2928_: f64 = 0.0;
            v___x_2923_ = crate::leanh::lean_unsigned_to_nat(10);
            v___x_2924_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_2925_ = l_Float_ofScientific(v___x_2923_, v___x_2893_, v___x_2924_);
            v___x_2926_ = lean_float_negate(v___x_2925_);
            v___x_2927_ = crate::leanh::lean_float_once(
                core::ptr::addr_of_mut!(
                    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2
                ),
                core::ptr::addr_of_mut!(
                    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once
                ),
                _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2,
            );
            v___x_2928_ = lean_float_div(v___x_2926_, v___x_2927_);
            return v___x_2928_;
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___boxed(
    mut v_s_2929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2930_: f64 = 0.0;
    let mut v_r_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2930_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(v_s_2929_);
    v_r_2931_ = crate::leanh::lean_box_float(v_res_2930_);
    return v_r_2931_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2940_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__3;
    v___x_2941_ = l_Lean_MessageData_ofFormat(v___x_2940_);
    return v___x_2941_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(
    mut v_x_2942_: *mut crate::leanh::LeanObject,
    mut v_a_2943_: *mut crate::leanh::LeanObject,
    mut v_a_2944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: f64 = 0.0;
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2959_: u8 = 0;
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2963_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2951_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1;
                v___x_2952_ = l_Lean_Syntax_isLit_x3f(v___x_2951_, v_x_2942_);
                if crate::leanh::lean_obj_tag(v___x_2952_) == 1 {
                    v_val_2953_ = crate::leanh::lean_ctor_get(v___x_2952_, 0);
                    crate::leanh::lean_inc(v_val_2953_);
                    crate::leanh::lean_dec_ref_known(v___x_2952_, 1);
                    v_a_2947_ = v_val_2953_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2952_);
                    v___x_2954_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4_once), _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4);
                    v___x_2955_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_2942_, v___x_2954_, v_a_2943_, v_a_2944_);
                    v_a_2956_ = crate::leanh::lean_ctor_get(v___x_2955_, 0);
                    v_isSharedCheck_2963_ = (!crate::leanh::lean_is_exclusive(v___x_2955_)) as u8;
                    if v_isSharedCheck_2963_ == 0 {
                        v___x_2958_ = v___x_2955_;
                        v_isShared_2959_ = v_isSharedCheck_2963_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2956_);
                        crate::leanh::lean_dec(v___x_2955_);
                        v___x_2958_ = crate::leanh::lean_box(0);
                        v_isShared_2959_ = v_isSharedCheck_2963_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2948_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(v_a_2947_);
                v___x_2949_ = crate::leanh::lean_box_float(v___x_2948_);
                v___x_2950_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2950_, 0, v___x_2949_);
                return v___x_2950_;
            }
            2 => {
                if v_isShared_2959_ == 0 {
                    v___x_2961_ = v___x_2958_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2962_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
                    v___x_2961_ = v_reuseFailAlloc_2962_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2961_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___boxed(
    mut v_x_2964_: *mut crate::leanh::LeanObject,
    mut v_a_2965_: *mut crate::leanh::LeanObject,
    mut v_a_2966_: *mut crate::leanh::LeanObject,
    mut v_a_2967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2968_ =
        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(v_x_2964_, v_a_2965_, v_a_2966_);
    crate::leanh::lean_dec(v_a_2966_);
    crate::leanh::lean_dec_ref(v_a_2965_);
    crate::leanh::lean_dec(v_x_2964_);
    return v_res_2968_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(
    mut v___x_2969_: *mut crate::leanh::LeanObject,
    mut v___x_2970_: *mut crate::leanh::LeanObject,
    mut v_a_2971_: *mut crate::leanh::LeanObject,
    mut v_a_2972_: *mut crate::leanh::LeanObject,
    mut v_b_2973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: u8 = 0;
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: u32 = 0;
    let mut v___x_2982_: u32 = 0;
    let mut v___x_2983_: u8 = 0;
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: u32 = 0;
    let mut v___x_2987_: u32 = 0;
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_2974_ = crate::leanh::lean_ctor_get(v___x_2969_, 1);
                v_endExclusive_2975_ = crate::leanh::lean_ctor_get(v___x_2969_, 2);
                v___x_2976_ = lean_nat_sub(v_endExclusive_2975_, v_startInclusive_2974_);
                v___x_2977_ = lean_nat_dec_eq(v_a_2972_, v___x_2976_);
                crate::leanh::lean_dec(v___x_2976_);
                if v___x_2977_ == 0 {
                    v___x_2978_ = lean_nat_add(v___x_2970_, v_a_2972_);
                    crate::leanh::lean_dec(v_a_2972_);
                    v___x_2979_ = lean_string_utf8_next_fast(v_a_2971_, v___x_2978_);
                    v___x_2980_ = lean_nat_sub(v___x_2979_, v___x_2970_);
                    v___x_2981_ = lean_string_utf8_get_fast(v_a_2971_, v___x_2978_);
                    crate::leanh::lean_dec(v___x_2978_);
                    v___x_2982_ = 95;
                    v___x_2983_ = lean_uint32_dec_eq(v___x_2981_, v___x_2982_);
                    if v___x_2983_ == 0 {
                        v___x_2984_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_2985_ = lean_nat_mul(v_b_2973_, v___x_2984_);
                        crate::leanh::lean_dec(v_b_2973_);
                        v___x_2986_ = 48;
                        v___x_2987_ = lean_uint32_sub(v___x_2981_, v___x_2986_);
                        v___x_2988_ = lean_uint32_to_nat(v___x_2987_);
                        v___x_2989_ = lean_nat_add(v___x_2985_, v___x_2988_);
                        crate::leanh::lean_dec(v___x_2988_);
                        crate::leanh::lean_dec(v___x_2985_);
                        v_a_2972_ = v___x_2980_;
                        v_b_2973_ = v___x_2989_;
                        state = 0;
                        continue;
                    } else {
                        v_a_2972_ = v___x_2980_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2972_);
                    return v_b_2973_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg___boxed(
    mut v___x_2992_: *mut crate::leanh::LeanObject,
    mut v___x_2993_: *mut crate::leanh::LeanObject,
    mut v_a_2994_: *mut crate::leanh::LeanObject,
    mut v_a_2995_: *mut crate::leanh::LeanObject,
    mut v_b_2996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2997_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_2992_, v___x_2993_, v_a_2994_, v_a_2995_, v_b_2996_);
    crate::leanh::lean_dec_ref(v_a_2994_);
    crate::leanh::lean_dec(v___x_2993_);
    crate::leanh::lean_dec_ref(v___x_2992_);
    return v_res_2997_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3006_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__3;
    v___x_3007_ = l_Lean_MessageData_ofFormat(v___x_3006_);
    return v___x_3007_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(
    mut v_x_3008_: *mut crate::leanh::LeanObject,
    mut v_a_3009_: *mut crate::leanh::LeanObject,
    mut v_a_3010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3031_: u8 = 0;
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3035_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3023_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1;
                v___x_3024_ = l_Lean_Syntax_isLit_x3f(v___x_3023_, v_x_3008_);
                if crate::leanh::lean_obj_tag(v___x_3024_) == 1 {
                    v_val_3025_ = crate::leanh::lean_ctor_get(v___x_3024_, 0);
                    crate::leanh::lean_inc(v_val_3025_);
                    crate::leanh::lean_dec_ref_known(v___x_3024_, 1);
                    v_a_3013_ = v_val_3025_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3024_);
                    v___x_3026_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4_once), _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4);
                    v___x_3027_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_3008_, v___x_3026_, v_a_3009_, v_a_3010_);
                    v_a_3028_ = crate::leanh::lean_ctor_get(v___x_3027_, 0);
                    v_isSharedCheck_3035_ = (!crate::leanh::lean_is_exclusive(v___x_3027_)) as u8;
                    if v_isSharedCheck_3035_ == 0 {
                        v___x_3030_ = v___x_3027_;
                        v_isShared_3031_ = v_isSharedCheck_3035_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3028_);
                        crate::leanh::lean_dec(v___x_3027_);
                        v___x_3030_ = crate::leanh::lean_box(0);
                        v_isShared_3031_ = v_isSharedCheck_3035_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3014_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3015_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3016_ = lean_string_utf8_byte_size(v_a_3013_);
                crate::leanh::lean_inc_ref_n(v_a_3013_, 2);
                v___x_3017_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3017_, 0, v_a_3013_);
                crate::leanh::lean_ctor_set(v___x_3017_, 1, v___x_3014_);
                crate::leanh::lean_ctor_set(v___x_3017_, 2, v___x_3016_);
                v___x_3018_ = l_String_Slice_Pos_nextn(v___x_3017_, v___x_3014_, v___x_3015_);
                crate::leanh::lean_dec_ref_known(v___x_3017_, 3);
                crate::leanh::lean_inc(v___x_3018_);
                v___x_3019_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3019_, 0, v_a_3013_);
                crate::leanh::lean_ctor_set(v___x_3019_, 1, v___x_3018_);
                crate::leanh::lean_ctor_set(v___x_3019_, 2, v___x_3016_);
                v___x_3020_ = l_String_Slice_positions(v___x_3019_);
                v___x_3021_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_3019_, v___x_3018_, v_a_3013_, v___x_3020_, v___x_3014_);
                crate::leanh::lean_dec_ref(v_a_3013_);
                crate::leanh::lean_dec(v___x_3018_);
                crate::leanh::lean_dec_ref_known(v___x_3019_, 3);
                v___x_3022_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3022_, 0, v___x_3021_);
                return v___x_3022_;
            }
            2 => {
                if v_isShared_3031_ == 0 {
                    v___x_3033_ = v___x_3030_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3034_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
                    v___x_3033_ = v_reuseFailAlloc_3034_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3033_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___boxed(
    mut v_x_3036_: *mut crate::leanh::LeanObject,
    mut v_a_3037_: *mut crate::leanh::LeanObject,
    mut v_a_3038_: *mut crate::leanh::LeanObject,
    mut v_a_3039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3040_ =
        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(v_x_3036_, v_a_3037_, v_a_3038_);
    crate::leanh::lean_dec(v_a_3038_);
    crate::leanh::lean_dec_ref(v_a_3037_);
    crate::leanh::lean_dec(v_x_3036_);
    return v_res_3040_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0(
    mut v___x_3041_: *mut crate::leanh::LeanObject,
    mut v___x_3042_: *mut crate::leanh::LeanObject,
    mut v_a_3043_: *mut crate::leanh::LeanObject,
    mut v_inst_3044_: *mut crate::leanh::LeanObject,
    mut v_R_3045_: *mut crate::leanh::LeanObject,
    mut v_a_3046_: *mut crate::leanh::LeanObject,
    mut v_b_3047_: *mut crate::leanh::LeanObject,
    mut v_c_3048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3049_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_3041_, v___x_3042_, v_a_3043_, v_a_3046_, v_b_3047_);
    return v___x_3049_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___boxed(
    mut v___x_3050_: *mut crate::leanh::LeanObject,
    mut v___x_3051_: *mut crate::leanh::LeanObject,
    mut v_a_3052_: *mut crate::leanh::LeanObject,
    mut v_inst_3053_: *mut crate::leanh::LeanObject,
    mut v_R_3054_: *mut crate::leanh::LeanObject,
    mut v_a_3055_: *mut crate::leanh::LeanObject,
    mut v_b_3056_: *mut crate::leanh::LeanObject,
    mut v_c_3057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3058_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0(v___x_3050_, v___x_3051_, v_a_3052_, v_inst_3053_, v_R_3054_, v_a_3055_, v_b_3056_, v_c_3057_);
    crate::leanh::lean_dec_ref(v_a_3052_);
    crate::leanh::lean_dec(v___x_3051_);
    crate::leanh::lean_dec_ref(v___x_3050_);
    return v_res_3058_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(
    mut v___x_3059_: *mut crate::leanh::LeanObject,
    mut v___x_3060_: *mut crate::leanh::LeanObject,
    mut v_a_3061_: *mut crate::leanh::LeanObject,
    mut v_a_3062_: *mut crate::leanh::LeanObject,
    mut v_b_3063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: u8 = 0;
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: u32 = 0;
    let mut v___x_3072_: u32 = 0;
    let mut v___x_3073_: u8 = 0;
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: u32 = 0;
    let mut v___x_3077_: u32 = 0;
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_3064_ = crate::leanh::lean_ctor_get(v___x_3059_, 1);
                v_endExclusive_3065_ = crate::leanh::lean_ctor_get(v___x_3059_, 2);
                v___x_3066_ = lean_nat_sub(v_endExclusive_3065_, v_startInclusive_3064_);
                v___x_3067_ = lean_nat_dec_eq(v_a_3062_, v___x_3066_);
                crate::leanh::lean_dec(v___x_3066_);
                if v___x_3067_ == 0 {
                    v___x_3068_ = lean_nat_add(v___x_3060_, v_a_3062_);
                    crate::leanh::lean_dec(v_a_3062_);
                    v___x_3069_ = lean_string_utf8_next_fast(v_a_3061_, v___x_3068_);
                    v___x_3070_ = lean_nat_sub(v___x_3069_, v___x_3060_);
                    v___x_3071_ = lean_string_utf8_get_fast(v_a_3061_, v___x_3068_);
                    crate::leanh::lean_dec(v___x_3068_);
                    v___x_3072_ = 95;
                    v___x_3073_ = lean_uint32_dec_eq(v___x_3071_, v___x_3072_);
                    if v___x_3073_ == 0 {
                        v___x_3074_ = crate::leanh::lean_unsigned_to_nat(8);
                        v___x_3075_ = lean_nat_mul(v_b_3063_, v___x_3074_);
                        crate::leanh::lean_dec(v_b_3063_);
                        v___x_3076_ = 48;
                        v___x_3077_ = lean_uint32_sub(v___x_3071_, v___x_3076_);
                        v___x_3078_ = lean_uint32_to_nat(v___x_3077_);
                        v___x_3079_ = lean_nat_add(v___x_3075_, v___x_3078_);
                        crate::leanh::lean_dec(v___x_3078_);
                        crate::leanh::lean_dec(v___x_3075_);
                        v_a_3062_ = v___x_3070_;
                        v_b_3063_ = v___x_3079_;
                        state = 0;
                        continue;
                    } else {
                        v_a_3062_ = v___x_3070_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3062_);
                    return v_b_3063_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg___boxed(
    mut v___x_3082_: *mut crate::leanh::LeanObject,
    mut v___x_3083_: *mut crate::leanh::LeanObject,
    mut v_a_3084_: *mut crate::leanh::LeanObject,
    mut v_a_3085_: *mut crate::leanh::LeanObject,
    mut v_b_3086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3087_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_3082_, v___x_3083_, v_a_3084_, v_a_3085_, v_b_3086_);
    crate::leanh::lean_dec_ref(v_a_3084_);
    crate::leanh::lean_dec(v___x_3083_);
    crate::leanh::lean_dec_ref(v___x_3082_);
    return v_res_3087_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3096_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__3;
    v___x_3097_ = l_Lean_MessageData_ofFormat(v___x_3096_);
    return v___x_3097_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(
    mut v_x_3098_: *mut crate::leanh::LeanObject,
    mut v_a_3099_: *mut crate::leanh::LeanObject,
    mut v_a_3100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3121_: u8 = 0;
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3113_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1;
                v___x_3114_ = l_Lean_Syntax_isLit_x3f(v___x_3113_, v_x_3098_);
                if crate::leanh::lean_obj_tag(v___x_3114_) == 1 {
                    v_val_3115_ = crate::leanh::lean_ctor_get(v___x_3114_, 0);
                    crate::leanh::lean_inc(v_val_3115_);
                    crate::leanh::lean_dec_ref_known(v___x_3114_, 1);
                    v_a_3103_ = v_val_3115_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3114_);
                    v___x_3116_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4_once), _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4);
                    v___x_3117_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_3098_, v___x_3116_, v_a_3099_, v_a_3100_);
                    v_a_3118_ = crate::leanh::lean_ctor_get(v___x_3117_, 0);
                    v_isSharedCheck_3125_ = (!crate::leanh::lean_is_exclusive(v___x_3117_)) as u8;
                    if v_isSharedCheck_3125_ == 0 {
                        v___x_3120_ = v___x_3117_;
                        v_isShared_3121_ = v_isSharedCheck_3125_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3118_);
                        crate::leanh::lean_dec(v___x_3117_);
                        v___x_3120_ = crate::leanh::lean_box(0);
                        v_isShared_3121_ = v_isSharedCheck_3125_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3104_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3105_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3106_ = lean_string_utf8_byte_size(v_a_3103_);
                crate::leanh::lean_inc_ref_n(v_a_3103_, 2);
                v___x_3107_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3107_, 0, v_a_3103_);
                crate::leanh::lean_ctor_set(v___x_3107_, 1, v___x_3104_);
                crate::leanh::lean_ctor_set(v___x_3107_, 2, v___x_3106_);
                v___x_3108_ = l_String_Slice_Pos_nextn(v___x_3107_, v___x_3104_, v___x_3105_);
                crate::leanh::lean_dec_ref_known(v___x_3107_, 3);
                crate::leanh::lean_inc(v___x_3108_);
                v___x_3109_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3109_, 0, v_a_3103_);
                crate::leanh::lean_ctor_set(v___x_3109_, 1, v___x_3108_);
                crate::leanh::lean_ctor_set(v___x_3109_, 2, v___x_3106_);
                v___x_3110_ = l_String_Slice_positions(v___x_3109_);
                v___x_3111_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_3109_, v___x_3108_, v_a_3103_, v___x_3110_, v___x_3104_);
                crate::leanh::lean_dec_ref(v_a_3103_);
                crate::leanh::lean_dec(v___x_3108_);
                crate::leanh::lean_dec_ref_known(v___x_3109_, 3);
                v___x_3112_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3112_, 0, v___x_3111_);
                return v___x_3112_;
            }
            2 => {
                if v_isShared_3121_ == 0 {
                    v___x_3123_ = v___x_3120_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3124_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
                    v___x_3123_ = v_reuseFailAlloc_3124_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3123_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___boxed(
    mut v_x_3126_: *mut crate::leanh::LeanObject,
    mut v_a_3127_: *mut crate::leanh::LeanObject,
    mut v_a_3128_: *mut crate::leanh::LeanObject,
    mut v_a_3129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3130_ =
        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(v_x_3126_, v_a_3127_, v_a_3128_);
    crate::leanh::lean_dec(v_a_3128_);
    crate::leanh::lean_dec_ref(v_a_3127_);
    crate::leanh::lean_dec(v_x_3126_);
    return v_res_3130_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0(
    mut v___x_3131_: *mut crate::leanh::LeanObject,
    mut v___x_3132_: *mut crate::leanh::LeanObject,
    mut v_a_3133_: *mut crate::leanh::LeanObject,
    mut v_inst_3134_: *mut crate::leanh::LeanObject,
    mut v_R_3135_: *mut crate::leanh::LeanObject,
    mut v_a_3136_: *mut crate::leanh::LeanObject,
    mut v_b_3137_: *mut crate::leanh::LeanObject,
    mut v_c_3138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3139_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_3131_, v___x_3132_, v_a_3133_, v_a_3136_, v_b_3137_);
    return v___x_3139_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___boxed(
    mut v___x_3140_: *mut crate::leanh::LeanObject,
    mut v___x_3141_: *mut crate::leanh::LeanObject,
    mut v_a_3142_: *mut crate::leanh::LeanObject,
    mut v_inst_3143_: *mut crate::leanh::LeanObject,
    mut v_R_3144_: *mut crate::leanh::LeanObject,
    mut v_a_3145_: *mut crate::leanh::LeanObject,
    mut v_b_3146_: *mut crate::leanh::LeanObject,
    mut v_c_3147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3148_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0(v___x_3140_, v___x_3141_, v_a_3142_, v_inst_3143_, v_R_3144_, v_a_3145_, v_b_3146_, v_c_3147_);
    crate::leanh::lean_dec_ref(v_a_3142_);
    crate::leanh::lean_dec(v___x_3141_);
    crate::leanh::lean_dec_ref(v___x_3140_);
    return v_res_3148_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(
    mut v_c_3149_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3150_: u32 = 0;
    let mut v___x_3151_: u8 = 0;
    v___x_3150_ = 57;
    v___x_3151_ = lean_uint32_dec_le(v_c_3149_, v___x_3150_);
    if v___x_3151_ == 0 {
        let mut v___x_3152_: u32 = 0;
        let mut v___x_3153_: u8 = 0;
        v___x_3152_ = 70;
        v___x_3153_ = lean_uint32_dec_le(v_c_3149_, v___x_3152_);
        if v___x_3153_ == 0 {
            let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3155_: u32 = 0;
            let mut v___x_3156_: u32 = 0;
            let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3154_ = crate::leanh::lean_unsigned_to_nat(10);
            v___x_3155_ = 97;
            v___x_3156_ = lean_uint32_sub(v_c_3149_, v___x_3155_);
            v___x_3157_ = lean_uint32_to_nat(v___x_3156_);
            v___x_3158_ = lean_nat_add(v___x_3154_, v___x_3157_);
            crate::leanh::lean_dec(v___x_3157_);
            return v___x_3158_;
        } else {
            let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3160_: u32 = 0;
            let mut v___x_3161_: u32 = 0;
            let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3159_ = crate::leanh::lean_unsigned_to_nat(10);
            v___x_3160_ = 65;
            v___x_3161_ = lean_uint32_sub(v_c_3149_, v___x_3160_);
            v___x_3162_ = lean_uint32_to_nat(v___x_3161_);
            v___x_3163_ = lean_nat_add(v___x_3159_, v___x_3162_);
            crate::leanh::lean_dec(v___x_3162_);
            return v___x_3163_;
        }
    } else {
        let mut v___x_3164_: u32 = 0;
        let mut v___x_3165_: u32 = 0;
        let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3164_ = 48;
        v___x_3165_ = lean_uint32_sub(v_c_3149_, v___x_3164_);
        v___x_3166_ = lean_uint32_to_nat(v___x_3165_);
        return v___x_3166_;
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit___boxed(
    mut v_c_3167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_3168_: u32 = 0;
    let mut v_res_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_3168_ = crate::leanh::lean_unbox_uint32(v_c_3167_);
    crate::leanh::lean_dec(v_c_3167_);
    v_res_3169_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(v_c_boxed_3168_);
    return v_res_3169_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(
    mut v___x_3170_: *mut crate::leanh::LeanObject,
    mut v___x_3171_: *mut crate::leanh::LeanObject,
    mut v_a_3172_: *mut crate::leanh::LeanObject,
    mut v_a_3173_: *mut crate::leanh::LeanObject,
    mut v_b_3174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: u8 = 0;
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: u32 = 0;
    let mut v___x_3183_: u32 = 0;
    let mut v___x_3184_: u8 = 0;
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_3175_ = crate::leanh::lean_ctor_get(v___x_3170_, 1);
                v_endExclusive_3176_ = crate::leanh::lean_ctor_get(v___x_3170_, 2);
                v___x_3177_ = lean_nat_sub(v_endExclusive_3176_, v_startInclusive_3175_);
                v___x_3178_ = lean_nat_dec_eq(v_a_3173_, v___x_3177_);
                crate::leanh::lean_dec(v___x_3177_);
                if v___x_3178_ == 0 {
                    v___x_3179_ = lean_nat_add(v___x_3171_, v_a_3173_);
                    crate::leanh::lean_dec(v_a_3173_);
                    v___x_3180_ = lean_string_utf8_next_fast(v_a_3172_, v___x_3179_);
                    v___x_3181_ = lean_nat_sub(v___x_3180_, v___x_3171_);
                    v___x_3182_ = lean_string_utf8_get_fast(v_a_3172_, v___x_3179_);
                    crate::leanh::lean_dec(v___x_3179_);
                    v___x_3183_ = 95;
                    v___x_3184_ = lean_uint32_dec_eq(v___x_3182_, v___x_3183_);
                    if v___x_3184_ == 0 {
                        v___x_3185_ = crate::leanh::lean_unsigned_to_nat(16);
                        v___x_3186_ = lean_nat_mul(v_b_3174_, v___x_3185_);
                        crate::leanh::lean_dec(v_b_3174_);
                        v___x_3187_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(
                            v___x_3182_,
                        );
                        v___x_3188_ = lean_nat_add(v___x_3186_, v___x_3187_);
                        crate::leanh::lean_dec(v___x_3187_);
                        crate::leanh::lean_dec(v___x_3186_);
                        v_a_3173_ = v___x_3181_;
                        v_b_3174_ = v___x_3188_;
                        state = 0;
                        continue;
                    } else {
                        v_a_3173_ = v___x_3181_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3173_);
                    return v_b_3174_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg___boxed(
    mut v___x_3191_: *mut crate::leanh::LeanObject,
    mut v___x_3192_: *mut crate::leanh::LeanObject,
    mut v_a_3193_: *mut crate::leanh::LeanObject,
    mut v_a_3194_: *mut crate::leanh::LeanObject,
    mut v_b_3195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3196_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_3191_, v___x_3192_, v_a_3193_, v_a_3194_, v_b_3195_);
    crate::leanh::lean_dec_ref(v_a_3193_);
    crate::leanh::lean_dec(v___x_3192_);
    crate::leanh::lean_dec_ref(v___x_3191_);
    return v_res_3196_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3205_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__3;
    v___x_3206_ = l_Lean_MessageData_ofFormat(v___x_3205_);
    return v___x_3206_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(
    mut v_x_3207_: *mut crate::leanh::LeanObject,
    mut v_a_3208_: *mut crate::leanh::LeanObject,
    mut v_a_3209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3230_: u8 = 0;
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3234_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3222_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1;
                v___x_3223_ = l_Lean_Syntax_isLit_x3f(v___x_3222_, v_x_3207_);
                if crate::leanh::lean_obj_tag(v___x_3223_) == 1 {
                    v_val_3224_ = crate::leanh::lean_ctor_get(v___x_3223_, 0);
                    crate::leanh::lean_inc(v_val_3224_);
                    crate::leanh::lean_dec_ref_known(v___x_3223_, 1);
                    v_a_3212_ = v_val_3224_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3223_);
                    v___x_3225_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4_once), _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4);
                    v___x_3226_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_3207_, v___x_3225_, v_a_3208_, v_a_3209_);
                    v_a_3227_ = crate::leanh::lean_ctor_get(v___x_3226_, 0);
                    v_isSharedCheck_3234_ = (!crate::leanh::lean_is_exclusive(v___x_3226_)) as u8;
                    if v_isSharedCheck_3234_ == 0 {
                        v___x_3229_ = v___x_3226_;
                        v_isShared_3230_ = v_isSharedCheck_3234_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3227_);
                        crate::leanh::lean_dec(v___x_3226_);
                        v___x_3229_ = crate::leanh::lean_box(0);
                        v_isShared_3230_ = v_isSharedCheck_3234_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3213_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3214_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3215_ = lean_string_utf8_byte_size(v_a_3212_);
                crate::leanh::lean_inc_ref_n(v_a_3212_, 2);
                v___x_3216_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3216_, 0, v_a_3212_);
                crate::leanh::lean_ctor_set(v___x_3216_, 1, v___x_3213_);
                crate::leanh::lean_ctor_set(v___x_3216_, 2, v___x_3215_);
                v___x_3217_ = l_String_Slice_Pos_nextn(v___x_3216_, v___x_3213_, v___x_3214_);
                crate::leanh::lean_dec_ref_known(v___x_3216_, 3);
                crate::leanh::lean_inc(v___x_3217_);
                v___x_3218_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3218_, 0, v_a_3212_);
                crate::leanh::lean_ctor_set(v___x_3218_, 1, v___x_3217_);
                crate::leanh::lean_ctor_set(v___x_3218_, 2, v___x_3215_);
                v___x_3219_ = l_String_Slice_positions(v___x_3218_);
                v___x_3220_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_3218_, v___x_3217_, v_a_3212_, v___x_3219_, v___x_3213_);
                crate::leanh::lean_dec_ref(v_a_3212_);
                crate::leanh::lean_dec(v___x_3217_);
                crate::leanh::lean_dec_ref_known(v___x_3218_, 3);
                v___x_3221_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3221_, 0, v___x_3220_);
                return v___x_3221_;
            }
            2 => {
                if v_isShared_3230_ == 0 {
                    v___x_3232_ = v___x_3229_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3233_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3227_);
                    v___x_3232_ = v_reuseFailAlloc_3233_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3232_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___boxed(
    mut v_x_3235_: *mut crate::leanh::LeanObject,
    mut v_a_3236_: *mut crate::leanh::LeanObject,
    mut v_a_3237_: *mut crate::leanh::LeanObject,
    mut v_a_3238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3239_ =
        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(v_x_3235_, v_a_3236_, v_a_3237_);
    crate::leanh::lean_dec(v_a_3237_);
    crate::leanh::lean_dec_ref(v_a_3236_);
    crate::leanh::lean_dec(v_x_3235_);
    return v_res_3239_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0(
    mut v___x_3240_: *mut crate::leanh::LeanObject,
    mut v___x_3241_: *mut crate::leanh::LeanObject,
    mut v_a_3242_: *mut crate::leanh::LeanObject,
    mut v_inst_3243_: *mut crate::leanh::LeanObject,
    mut v_R_3244_: *mut crate::leanh::LeanObject,
    mut v_a_3245_: *mut crate::leanh::LeanObject,
    mut v_b_3246_: *mut crate::leanh::LeanObject,
    mut v_c_3247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3248_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_3240_, v___x_3241_, v_a_3242_, v_a_3245_, v_b_3246_);
    return v___x_3248_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___boxed(
    mut v___x_3249_: *mut crate::leanh::LeanObject,
    mut v___x_3250_: *mut crate::leanh::LeanObject,
    mut v_a_3251_: *mut crate::leanh::LeanObject,
    mut v_inst_3252_: *mut crate::leanh::LeanObject,
    mut v_R_3253_: *mut crate::leanh::LeanObject,
    mut v_a_3254_: *mut crate::leanh::LeanObject,
    mut v_b_3255_: *mut crate::leanh::LeanObject,
    mut v_c_3256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3257_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0(v___x_3249_, v___x_3250_, v_a_3251_, v_inst_3252_, v_R_3253_, v_a_3254_, v_b_3255_, v_c_3256_);
    crate::leanh::lean_dec_ref(v_a_3251_);
    crate::leanh::lean_dec(v___x_3250_);
    crate::leanh::lean_dec_ref(v___x_3249_);
    return v_res_3257_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3259_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0;
    v___x_3260_ = l_Lean_stringToMessageData(v___x_3259_);
    return v___x_3260_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3269_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__5;
    v___x_3270_ = l_Lean_MessageData_ofFormat(v___x_3269_);
    return v___x_3270_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(
    mut v_x_3271_: *mut crate::leanh::LeanObject,
    mut v_a_3272_: *mut crate::leanh::LeanObject,
    mut v_a_3273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3281_: u8 = 0;
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3285_: u8 = 0;
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3296_: u8 = 0;
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3300_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3288_ =
                    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3;
                v___x_3289_ = l_Lean_Syntax_isLit_x3f(v___x_3288_, v_x_3271_);
                if crate::leanh::lean_obj_tag(v___x_3289_) == 1 {
                    v_val_3290_ = crate::leanh::lean_ctor_get(v___x_3289_, 0);
                    crate::leanh::lean_inc(v_val_3290_);
                    crate::leanh::lean_dec_ref_known(v___x_3289_, 1);
                    v_a_3276_ = v_val_3290_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3289_);
                    v___x_3291_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6_once), _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6);
                    v___x_3292_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_3271_, v___x_3291_, v_a_3272_, v_a_3273_);
                    v_a_3293_ = crate::leanh::lean_ctor_get(v___x_3292_, 0);
                    v_isSharedCheck_3300_ = (!crate::leanh::lean_is_exclusive(v___x_3292_)) as u8;
                    if v_isSharedCheck_3300_ == 0 {
                        v___x_3295_ = v___x_3292_;
                        v_isShared_3296_ = v_isSharedCheck_3300_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3293_);
                        crate::leanh::lean_dec(v___x_3292_);
                        v___x_3295_ = crate::leanh::lean_box(0);
                        v_isShared_3296_ = v_isSharedCheck_3300_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3277_ = l_Lake_Toml_DateTime_ofString_x3f(v_a_3276_);
                if crate::leanh::lean_obj_tag(v___x_3277_) == 1 {
                    v_val_3278_ = crate::leanh::lean_ctor_get(v___x_3277_, 0);
                    v_isSharedCheck_3285_ = (!crate::leanh::lean_is_exclusive(v___x_3277_)) as u8;
                    if v_isSharedCheck_3285_ == 0 {
                        v___x_3280_ = v___x_3277_;
                        v_isShared_3281_ = v_isSharedCheck_3285_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3278_);
                        crate::leanh::lean_dec(v___x_3277_);
                        v___x_3280_ = crate::leanh::lean_box(0);
                        v_isShared_3281_ = v_isSharedCheck_3285_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3277_);
                    v___x_3286_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1_once), _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1);
                    v___x_3287_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_3271_, v___x_3286_, v_a_3272_, v_a_3273_);
                    return v___x_3287_;
                }
            }
            2 => {
                if v_isShared_3281_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3280_, 0);
                    v___x_3283_ = v___x_3280_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3284_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_val_3278_);
                    v___x_3283_ = v_reuseFailAlloc_3284_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3283_;
            }
            4 => {
                if v_isShared_3296_ == 0 {
                    v___x_3298_ = v___x_3295_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3299_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_a_3293_);
                    v___x_3298_ = v_reuseFailAlloc_3299_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3298_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___boxed(
    mut v_x_3301_: *mut crate::leanh::LeanObject,
    mut v_a_3302_: *mut crate::leanh::LeanObject,
    mut v_a_3303_: *mut crate::leanh::LeanObject,
    mut v_a_3304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3305_ =
        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(v_x_3301_, v_a_3302_, v_a_3303_);
    crate::leanh::lean_dec(v_a_3303_);
    crate::leanh::lean_dec_ref(v_a_3302_);
    crate::leanh::lean_dec(v_x_3301_);
    return v_res_3305_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3314_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__3;
    v___x_3315_ = l_Lean_MessageData_ofFormat(v___x_3314_);
    return v___x_3315_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(
    mut v_x_3316_: *mut crate::leanh::LeanObject,
    mut v_a_3317_: *mut crate::leanh::LeanObject,
    mut v_a_3318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3333_ =
                    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1;
                v___x_3334_ = l_Lean_Syntax_isLit_x3f(v___x_3333_, v_x_3316_);
                if crate::leanh::lean_obj_tag(v___x_3334_) == 1 {
                    v_val_3335_ = crate::leanh::lean_ctor_get(v___x_3334_, 0);
                    crate::leanh::lean_inc(v_val_3335_);
                    crate::leanh::lean_dec_ref_known(v___x_3334_, 1);
                    v_a_3321_ = v_val_3335_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3334_);
                    v___x_3336_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4_once), _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4);
                    v___x_3337_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_3316_, v___x_3336_, v_a_3317_, v_a_3318_);
                    return v___x_3337_;
                }
            }
            1 => {
                v___x_3322_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3323_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3324_ = lean_string_utf8_byte_size(v_a_3321_);
                crate::leanh::lean_inc_ref_n(v_a_3321_, 2);
                v___x_3325_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3325_, 0, v_a_3321_);
                crate::leanh::lean_ctor_set(v___x_3325_, 1, v___x_3323_);
                crate::leanh::lean_ctor_set(v___x_3325_, 2, v___x_3324_);
                v___x_3326_ = l_String_Slice_Pos_nextn(v___x_3325_, v___x_3323_, v___x_3322_);
                crate::leanh::lean_dec_ref_known(v___x_3325_, 3);
                crate::leanh::lean_inc(v___x_3326_);
                v___x_3327_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3327_, 0, v_a_3321_);
                crate::leanh::lean_ctor_set(v___x_3327_, 1, v___x_3326_);
                crate::leanh::lean_ctor_set(v___x_3327_, 2, v___x_3324_);
                v___x_3328_ = lean_nat_sub(v___x_3324_, v___x_3326_);
                v___x_3329_ = l_String_Slice_Pos_prevn(v___x_3327_, v___x_3328_, v___x_3322_);
                crate::leanh::lean_dec_ref_known(v___x_3327_, 3);
                v___x_3330_ = lean_nat_add(v___x_3326_, v___x_3329_);
                crate::leanh::lean_dec(v___x_3329_);
                v___x_3331_ = lean_string_utf8_extract(v_a_3321_, v___x_3326_, v___x_3330_);
                crate::leanh::lean_dec(v___x_3330_);
                crate::leanh::lean_dec(v___x_3326_);
                crate::leanh::lean_dec_ref(v_a_3321_);
                v___x_3332_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3332_, 0, v___x_3331_);
                return v___x_3332_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___boxed(
    mut v_x_3338_: *mut crate::leanh::LeanObject,
    mut v_a_3339_: *mut crate::leanh::LeanObject,
    mut v_a_3340_: *mut crate::leanh::LeanObject,
    mut v_a_3341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3342_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(
        v_x_3338_, v_a_3339_, v_a_3340_,
    );
    crate::leanh::lean_dec(v_a_3340_);
    crate::leanh::lean_dec_ref(v_a_3339_);
    crate::leanh::lean_dec(v_x_3338_);
    return v_res_3342_;
}
pub unsafe fn l_panic___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__1(
    mut v_msg_3343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3344_ = l_String_instInhabitedSlice;
    v___x_3345_ = lean_panic_fn_borrowed(v___x_3344_, v_msg_3343_);
    return v___x_3345_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(
    mut v___y_3346_: *mut crate::leanh::LeanObject,
    mut v_a_3347_: *mut crate::leanh::LeanObject,
    mut v_b_3348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: u8 = 0;
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: u32 = 0;
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_3349_ = crate::leanh::lean_ctor_get(v___y_3346_, 0);
                v_startInclusive_3350_ = crate::leanh::lean_ctor_get(v___y_3346_, 1);
                v_endExclusive_3351_ = crate::leanh::lean_ctor_get(v___y_3346_, 2);
                v___x_3352_ = lean_nat_sub(v_endExclusive_3351_, v_startInclusive_3350_);
                v___x_3353_ = lean_nat_dec_eq(v_a_3347_, v___x_3352_);
                crate::leanh::lean_dec(v___x_3352_);
                if v___x_3353_ == 0 {
                    v___x_3354_ = lean_nat_add(v_startInclusive_3350_, v_a_3347_);
                    crate::leanh::lean_dec(v_a_3347_);
                    v___x_3355_ = lean_string_utf8_get_fast(v_str_3349_, v___x_3354_);
                    v___x_3356_ = lean_string_utf8_next_fast(v_str_3349_, v___x_3354_);
                    crate::leanh::lean_dec(v___x_3354_);
                    v___x_3357_ = lean_nat_sub(v___x_3356_, v_startInclusive_3350_);
                    v___x_3358_ = crate::leanh::lean_unsigned_to_nat(16);
                    v___x_3359_ = lean_nat_mul(v_b_3348_, v___x_3358_);
                    crate::leanh::lean_dec(v_b_3348_);
                    v___x_3360_ =
                        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(v___x_3355_);
                    v___x_3361_ = lean_nat_add(v___x_3359_, v___x_3360_);
                    crate::leanh::lean_dec(v___x_3360_);
                    crate::leanh::lean_dec(v___x_3359_);
                    v_a_3347_ = v___x_3357_;
                    v_b_3348_ = v___x_3361_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_3347_);
                    return v_b_3348_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg___boxed(
    mut v___y_3363_: *mut crate::leanh::LeanObject,
    mut v_a_3364_: *mut crate::leanh::LeanObject,
    mut v_b_3365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3366_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_3363_, v_a_3364_, v_b_3365_);
    crate::leanh::lean_dec_ref(v___y_3363_);
    return v_res_3366_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3370_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2;
    v___x_3371_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_3372_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_3373_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1;
    v___x_3374_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0;
    v___x_3375_ = l_mkPanicMessageWithDecl(
        v___x_3374_,
        v___x_3373_,
        v___x_3372_,
        v___x_3371_,
        v___x_3370_,
    );
    return v___x_3375_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits(
    mut v_s_3376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3382_: u8 = 0;
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: u8 = 0;
    let mut v___x_3392_: u8 = 0;
    let mut v___x_3393_: u8 = 0;
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3397_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_3377_ = crate::leanh::lean_ctor_get(v_s_3376_, 0);
                v_startPos_3378_ = crate::leanh::lean_ctor_get(v_s_3376_, 1);
                v_stopPos_3379_ = crate::leanh::lean_ctor_get(v_s_3376_, 2);
                v_isSharedCheck_3397_ = (!crate::leanh::lean_is_exclusive(v_s_3376_)) as u8;
                if v_isSharedCheck_3397_ == 0 {
                    v___x_3381_ = v_s_3376_;
                    v_isShared_3382_ = v_isSharedCheck_3397_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_3379_);
                    crate::leanh::lean_inc(v_startPos_3378_);
                    crate::leanh::lean_inc(v_str_3377_);
                    crate::leanh::lean_dec(v_s_3376_);
                    v___x_3381_ = crate::leanh::lean_box(0);
                    v_isShared_3382_ = v_isSharedCheck_3397_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3383_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3391_ = lean_string_is_valid_pos(v_str_3377_, v_startPos_3378_);
                if v___x_3391_ == 0 {
                    crate::leanh::lean_del_object(v___x_3381_);
                    crate::leanh::lean_dec(v_stopPos_3379_);
                    crate::leanh::lean_dec(v_startPos_3378_);
                    crate::leanh::lean_dec_ref(v_str_3377_);
                    state = 3;
                    continue;
                } else {
                    v___x_3392_ = lean_string_is_valid_pos(v_str_3377_, v_stopPos_3379_);
                    if v___x_3392_ == 0 {
                        crate::leanh::lean_del_object(v___x_3381_);
                        crate::leanh::lean_dec(v_stopPos_3379_);
                        crate::leanh::lean_dec(v_startPos_3378_);
                        crate::leanh::lean_dec_ref(v_str_3377_);
                        state = 3;
                        continue;
                    } else {
                        v___x_3393_ = lean_nat_dec_le(v_startPos_3378_, v_stopPos_3379_);
                        if v___x_3393_ == 0 {
                            crate::leanh::lean_del_object(v___x_3381_);
                            crate::leanh::lean_dec(v_stopPos_3379_);
                            crate::leanh::lean_dec(v_startPos_3378_);
                            crate::leanh::lean_dec_ref(v_str_3377_);
                            state = 3;
                            continue;
                        } else {
                            if v_isShared_3382_ == 0 {
                                v___x_3395_ = v___x_3381_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_3396_ =
                                    crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_str_3377_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3396_,
                                    1,
                                    v_startPos_3378_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3396_,
                                    2,
                                    v_stopPos_3379_,
                                );
                                v___x_3395_ = v_reuseFailAlloc_3396_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_3386_ = l_String_Slice_positions(v___y_3385_);
                v___x_3387_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_3385_, v___x_3386_, v___x_3383_);
                crate::leanh::lean_dec_ref(v___y_3385_);
                return v___x_3387_;
            }
            3 => {
                v___x_3389_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3_once), _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3);
                v___x_3390_ = l_panic___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__1(v___x_3389_);
                v___y_3385_ = v___x_3390_;
                state = 2;
                continue;
            }
            4 => {
                v___y_3385_ = v___x_3395_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0(
    mut v___y_3398_: *mut crate::leanh::LeanObject,
    mut v_inst_3399_: *mut crate::leanh::LeanObject,
    mut v_R_3400_: *mut crate::leanh::LeanObject,
    mut v_a_3401_: *mut crate::leanh::LeanObject,
    mut v_b_3402_: *mut crate::leanh::LeanObject,
    mut v_c_3403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3404_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_3398_, v_a_3401_, v_b_3402_);
    return v___x_3404_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___boxed(
    mut v___y_3405_: *mut crate::leanh::LeanObject,
    mut v_inst_3406_: *mut crate::leanh::LeanObject,
    mut v_R_3407_: *mut crate::leanh::LeanObject,
    mut v_a_3408_: *mut crate::leanh::LeanObject,
    mut v_b_3409_: *mut crate::leanh::LeanObject,
    mut v_c_3410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3411_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0(v___y_3405_, v_inst_3406_, v_R_3407_, v_a_3408_, v_b_3409_, v_c_3410_);
    crate::leanh::lean_dec_ref(v___y_3405_);
    return v_res_3411_;
}
pub unsafe fn l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(
    mut v_s_3412_: *mut crate::leanh::LeanObject,
    mut v_stopPos_3413_: *mut crate::leanh::LeanObject,
    mut v_i_3414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3419_: u8 = 0;
    let mut v___x_3420_: u8 = 0;
    let mut v___x_3421_: u32 = 0;
    let mut v___y_3423_: u8 = 0;
    let mut v___x_3424_: u32 = 0;
    let mut v___x_3425_: u8 = 0;
    let mut v___x_3426_: u32 = 0;
    let mut v___x_3427_: u8 = 0;
    let mut v___x_3428_: u32 = 0;
    let mut v___x_3429_: u8 = 0;
    let mut v___x_3430_: u32 = 0;
    let mut v___x_3431_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3420_ = lean_nat_dec_lt(v_i_3414_, v_stopPos_3413_);
                if v___x_3420_ == 0 {
                    return v_i_3414_;
                } else {
                    v___x_3421_ = lean_string_utf8_get(v_s_3412_, v_i_3414_);
                    v___x_3428_ = 32;
                    v___x_3429_ = lean_uint32_dec_eq(v___x_3421_, v___x_3428_);
                    if v___x_3429_ == 0 {
                        v___x_3430_ = 9;
                        v___x_3431_ = lean_uint32_dec_eq(v___x_3421_, v___x_3430_);
                        v___y_3423_ = v___x_3431_;
                        state = 3;
                        continue;
                    } else {
                        v___y_3423_ = v___x_3429_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3416_ = lean_string_utf8_next(v_s_3412_, v_i_3414_);
                crate::leanh::lean_dec(v_i_3414_);
                v_i_3414_ = v___x_3416_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_3419_ == 0 {
                    return v_i_3414_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_3423_ == 0 {
                    v___x_3424_ = 13;
                    v___x_3425_ = lean_uint32_dec_eq(v___x_3421_, v___x_3424_);
                    if v___x_3425_ == 0 {
                        v___x_3426_ = 10;
                        v___x_3427_ = lean_uint32_dec_eq(v___x_3421_, v___x_3426_);
                        v___y_3419_ = v___x_3427_;
                        state = 2;
                        continue;
                    } else {
                        v___y_3419_ = v___x_3425_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0___boxed(
    mut v_s_3432_: *mut crate::leanh::LeanObject,
    mut v_stopPos_3433_: *mut crate::leanh::LeanObject,
    mut v_i_3434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3435_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(v_s_3432_, v_stopPos_3433_, v_i_3434_);
    crate::leanh::lean_dec(v_stopPos_3433_);
    crate::leanh::lean_dec_ref(v_s_3432_);
    return v_res_3435_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3437_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0;
    v___x_3438_ = l_Lean_stringToMessageData(v___x_3437_);
    return v___x_3438_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3440_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2;
    v___x_3441_ = l_Lean_stringToMessageData(v___x_3440_);
    return v___x_3441_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(
    mut v_lit_3442_: *mut crate::leanh::LeanObject,
    mut v_i_3443_: *mut crate::leanh::LeanObject,
    mut v_out_3444_: *mut crate::leanh::LeanObject,
    mut v_a_3445_: *mut crate::leanh::LeanObject,
    mut v_a_3446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ch_3466_: u32 = 0;
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_escape_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: u8 = 0;
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: u8 = 0;
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: u8 = 0;
    let mut v___x_3480_: u8 = 0;
    let mut v_curr_3481_: u32 = 0;
    let mut v_i_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: u32 = 0;
    let mut v___x_3484_: u8 = 0;
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: u8 = 0;
    let mut v_curr_3488_: u32 = 0;
    let mut v_next_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: u32 = 0;
    let mut v___x_3491_: u8 = 0;
    let mut v___x_3492_: u32 = 0;
    let mut v___x_3493_: u8 = 0;
    let mut v___x_3494_: u32 = 0;
    let mut v___x_3495_: u8 = 0;
    let mut v___x_3496_: u32 = 0;
    let mut v___x_3497_: u8 = 0;
    let mut v___x_3498_: u32 = 0;
    let mut v___x_3499_: u8 = 0;
    let mut v___x_3500_: u32 = 0;
    let mut v___x_3501_: u8 = 0;
    let mut v___x_3502_: u8 = 0;
    let mut v___x_3503_: u32 = 0;
    let mut v___x_3504_: u8 = 0;
    let mut v___x_3505_: u32 = 0;
    let mut v___x_3506_: u8 = 0;
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: u32 = 0;
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: u32 = 0;
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: u32 = 0;
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: u32 = 0;
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: u32 = 0;
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3480_ = lean_string_utf8_at_end(v_lit_3442_, v_i_3443_);
                if v___x_3480_ == 0 {
                    v_curr_3481_ = lean_string_utf8_get_fast(v_lit_3442_, v_i_3443_);
                    v_i_3482_ = lean_string_utf8_next_fast(v_lit_3442_, v_i_3443_);
                    crate::leanh::lean_dec(v_i_3443_);
                    v___x_3483_ = 92;
                    v___x_3484_ = lean_uint32_dec_eq(v_curr_3481_, v___x_3483_);
                    if v___x_3484_ == 0 {
                        v___x_3485_ = lean_string_push(v_out_3444_, v_curr_3481_);
                        v_i_3443_ = v_i_3482_;
                        v_out_3444_ = v___x_3485_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3487_ = lean_string_utf8_at_end(v_lit_3442_, v_i_3482_);
                        if v___x_3487_ == 0 {
                            v_curr_3488_ = lean_string_utf8_get_fast(v_lit_3442_, v_i_3482_);
                            v_next_3489_ = lean_string_utf8_next_fast(v_lit_3442_, v_i_3482_);
                            v___x_3490_ = 98;
                            v___x_3491_ = lean_uint32_dec_eq(v_curr_3488_, v___x_3490_);
                            if v___x_3491_ == 0 {
                                v___x_3492_ = 116;
                                v___x_3493_ = lean_uint32_dec_eq(v_curr_3488_, v___x_3492_);
                                if v___x_3493_ == 0 {
                                    v___x_3494_ = 110;
                                    v___x_3495_ = lean_uint32_dec_eq(v_curr_3488_, v___x_3494_);
                                    if v___x_3495_ == 0 {
                                        v___x_3496_ = 102;
                                        v___x_3497_ = lean_uint32_dec_eq(v_curr_3488_, v___x_3496_);
                                        if v___x_3497_ == 0 {
                                            v___x_3498_ = 114;
                                            v___x_3499_ =
                                                lean_uint32_dec_eq(v_curr_3488_, v___x_3498_);
                                            if v___x_3499_ == 0 {
                                                v___x_3500_ = 34;
                                                v___x_3501_ =
                                                    lean_uint32_dec_eq(v_curr_3488_, v___x_3500_);
                                                if v___x_3501_ == 0 {
                                                    v___x_3502_ = lean_uint32_dec_eq(
                                                        v_curr_3488_,
                                                        v___x_3483_,
                                                    );
                                                    if v___x_3502_ == 0 {
                                                        v___x_3503_ = 117;
                                                        v___x_3504_ = lean_uint32_dec_eq(
                                                            v_curr_3488_,
                                                            v___x_3503_,
                                                        );
                                                        if v___x_3504_ == 0 {
                                                            v___x_3505_ = 85;
                                                            v___x_3506_ = lean_uint32_dec_eq(
                                                                v_curr_3488_,
                                                                v___x_3505_,
                                                            );
                                                            if v___x_3506_ == 0 {
                                                                v___x_3507_ =
                                                                    lean_string_utf8_byte_size(
                                                                        v_lit_3442_,
                                                                    );
                                                                v_b_3508_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(v_lit_3442_, v___x_3507_, v_i_3482_);
                                                                v_i_3443_ = v_b_3508_;
                                                                state = 0;
                                                                continue;
                                                            } else {
                                                                v___x_3510_ =
                                                                    lean_string_utf8_byte_size(
                                                                        v_lit_3442_,
                                                                    );
                                                                crate::leanh::lean_inc_ref_n(
                                                                    v_lit_3442_,
                                                                    2,
                                                                );
                                                                v___x_3511_ =
                                                                    crate::leanh::lean_alloc_ctor(
                                                                        0,
                                                                        3,
                                                                        (0) as u32,
                                                                    );
                                                                crate::leanh::lean_ctor_set(
                                                                    v___x_3511_,
                                                                    0,
                                                                    v_lit_3442_,
                                                                );
                                                                crate::leanh::lean_ctor_set(
                                                                    v___x_3511_,
                                                                    1,
                                                                    v_next_3489_,
                                                                );
                                                                crate::leanh::lean_ctor_set(
                                                                    v___x_3511_,
                                                                    2,
                                                                    v___x_3510_,
                                                                );
                                                                v___x_3512_ = crate::leanh::lean_unsigned_to_nat(8);
                                                                v___x_3513_ = crate::leanh::lean_unsigned_to_nat(0);
                                                                v___x_3514_ = l_Substring_Raw_nextn(
                                                                    v___x_3511_,
                                                                    v___x_3512_,
                                                                    v___x_3513_,
                                                                );
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_3511_,
                                                                    3,
                                                                );
                                                                v___x_3515_ = lean_nat_add(
                                                                    v_next_3489_,
                                                                    v___x_3514_,
                                                                );
                                                                crate::leanh::lean_dec(v___x_3514_);
                                                                v___x_3516_ =
                                                                    crate::leanh::lean_alloc_ctor(
                                                                        0,
                                                                        3,
                                                                        (0) as u32,
                                                                    );
                                                                crate::leanh::lean_ctor_set(
                                                                    v___x_3516_,
                                                                    0,
                                                                    v_lit_3442_,
                                                                );
                                                                crate::leanh::lean_ctor_set(
                                                                    v___x_3516_,
                                                                    1,
                                                                    v_next_3489_,
                                                                );
                                                                crate::leanh::lean_ctor_set(
                                                                    v___x_3516_,
                                                                    2,
                                                                    v___x_3515_,
                                                                );
                                                                v_escape_3470_ = v___x_3516_;
                                                                v___y_3471_ = v_a_3445_;
                                                                v___y_3472_ = v_a_3446_;
                                                                state = 3;
                                                                continue;
                                                            }
                                                        } else {
                                                            v___x_3517_ =
                                                                lean_string_utf8_byte_size(
                                                                    v_lit_3442_,
                                                                );
                                                            crate::leanh::lean_inc_ref_n(
                                                                v_lit_3442_,
                                                                2,
                                                            );
                                                            v___x_3518_ =
                                                                crate::leanh::lean_alloc_ctor(
                                                                    0,
                                                                    3,
                                                                    (0) as u32,
                                                                );
                                                            crate::leanh::lean_ctor_set(
                                                                v___x_3518_,
                                                                0,
                                                                v_lit_3442_,
                                                            );
                                                            crate::leanh::lean_ctor_set(
                                                                v___x_3518_,
                                                                1,
                                                                v_next_3489_,
                                                            );
                                                            crate::leanh::lean_ctor_set(
                                                                v___x_3518_,
                                                                2,
                                                                v___x_3517_,
                                                            );
                                                            v___x_3519_ =
                                                                crate::leanh::lean_unsigned_to_nat(
                                                                    4,
                                                                );
                                                            v___x_3520_ =
                                                                crate::leanh::lean_unsigned_to_nat(
                                                                    0,
                                                                );
                                                            v___x_3521_ = l_Substring_Raw_nextn(
                                                                v___x_3518_,
                                                                v___x_3519_,
                                                                v___x_3520_,
                                                            );
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_3518_,
                                                                3,
                                                            );
                                                            v___x_3522_ = lean_nat_add(
                                                                v_next_3489_,
                                                                v___x_3521_,
                                                            );
                                                            crate::leanh::lean_dec(v___x_3521_);
                                                            v___x_3523_ =
                                                                crate::leanh::lean_alloc_ctor(
                                                                    0,
                                                                    3,
                                                                    (0) as u32,
                                                                );
                                                            crate::leanh::lean_ctor_set(
                                                                v___x_3523_,
                                                                0,
                                                                v_lit_3442_,
                                                            );
                                                            crate::leanh::lean_ctor_set(
                                                                v___x_3523_,
                                                                1,
                                                                v_next_3489_,
                                                            );
                                                            crate::leanh::lean_ctor_set(
                                                                v___x_3523_,
                                                                2,
                                                                v___x_3522_,
                                                            );
                                                            v_escape_3470_ = v___x_3523_;
                                                            v___y_3471_ = v_a_3445_;
                                                            v___y_3472_ = v_a_3446_;
                                                            state = 3;
                                                            continue;
                                                        }
                                                    } else {
                                                        v___x_3524_ = lean_string_push(
                                                            v_out_3444_,
                                                            v___x_3483_,
                                                        );
                                                        v_i_3443_ = v_next_3489_;
                                                        v_out_3444_ = v___x_3524_;
                                                        state = 0;
                                                        continue;
                                                    }
                                                } else {
                                                    v___x_3526_ =
                                                        lean_string_push(v_out_3444_, v___x_3500_);
                                                    v_i_3443_ = v_next_3489_;
                                                    v_out_3444_ = v___x_3526_;
                                                    state = 0;
                                                    continue;
                                                }
                                            } else {
                                                v___x_3528_ = 13;
                                                v___x_3529_ =
                                                    lean_string_push(v_out_3444_, v___x_3528_);
                                                v_i_3443_ = v_next_3489_;
                                                v_out_3444_ = v___x_3529_;
                                                state = 0;
                                                continue;
                                            }
                                        } else {
                                            v___x_3531_ = 12;
                                            v___x_3532_ =
                                                lean_string_push(v_out_3444_, v___x_3531_);
                                            v_i_3443_ = v_next_3489_;
                                            v_out_3444_ = v___x_3532_;
                                            state = 0;
                                            continue;
                                        }
                                    } else {
                                        v___x_3534_ = 10;
                                        v___x_3535_ = lean_string_push(v_out_3444_, v___x_3534_);
                                        v_i_3443_ = v_next_3489_;
                                        v_out_3444_ = v___x_3535_;
                                        state = 0;
                                        continue;
                                    }
                                } else {
                                    v___x_3537_ = 9;
                                    v___x_3538_ = lean_string_push(v_out_3444_, v___x_3537_);
                                    v_i_3443_ = v_next_3489_;
                                    v_out_3444_ = v___x_3538_;
                                    state = 0;
                                    continue;
                                }
                            } else {
                                v___x_3540_ = 8;
                                v___x_3541_ = lean_string_push(v_out_3444_, v___x_3540_);
                                v_i_3443_ = v_next_3489_;
                                v_out_3444_ = v___x_3541_;
                                state = 0;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_lit_3442_);
                            v___x_3543_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3543_, 0, v_out_3444_);
                            return v___x_3543_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_i_3443_);
                    crate::leanh::lean_dec_ref(v_lit_3442_);
                    v___x_3544_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3544_, 0, v_out_3444_);
                    return v___x_3544_;
                }
            }
            1 => {
                v___x_3452_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1_once), _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1);
                v___x_3453_ = lean_substring_tostring(v___y_3451_);
                v___x_3454_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3454_, 0, v___x_3453_);
                v___x_3455_ = l_Lean_MessageData_ofFormat(v___x_3454_);
                v___x_3456_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3456_, 0, v___x_3452_);
                crate::leanh::lean_ctor_set(v___x_3456_, 1, v___x_3455_);
                v___x_3457_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once), _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
                v___x_3458_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3458_, 0, v___x_3456_);
                crate::leanh::lean_ctor_set(v___x_3458_, 1, v___x_3457_);
                v___x_3459_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v___x_3458_, v___y_3449_, v___y_3450_);
                return v___x_3459_;
            }
            2 => {
                v_stopPos_3465_ = crate::leanh::lean_ctor_get(v___y_3464_, 2);
                crate::leanh::lean_inc(v_stopPos_3465_);
                crate::leanh::lean_dec_ref(v___y_3464_);
                v_ch_3466_ = lean_uint32_of_nat(v___y_3461_);
                crate::leanh::lean_dec(v___y_3461_);
                v___x_3467_ = lean_string_push(v_out_3444_, v_ch_3466_);
                v_i_3443_ = v_stopPos_3465_;
                v_out_3444_ = v___x_3467_;
                v_a_3445_ = v___y_3462_;
                v_a_3446_ = v___y_3463_;
                state = 0;
                continue;
            }
            3 => {
                crate::leanh::lean_inc_ref(v_escape_3470_);
                v_val_3473_ =
                    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits(v_escape_3470_);
                v___x_3474_ = crate::leanh::lean_unsigned_to_nat(55296);
                v___x_3475_ = lean_nat_dec_lt(v_val_3473_, v___x_3474_);
                if v___x_3475_ == 0 {
                    v___x_3476_ = crate::leanh::lean_unsigned_to_nat(57343);
                    v___x_3477_ = lean_nat_dec_lt(v___x_3476_, v_val_3473_);
                    if v___x_3477_ == 0 {
                        crate::leanh::lean_dec(v_val_3473_);
                        crate::leanh::lean_dec_ref(v_out_3444_);
                        crate::leanh::lean_dec_ref(v_lit_3442_);
                        v___y_3449_ = v___y_3471_;
                        v___y_3450_ = v___y_3472_;
                        v___y_3451_ = v_escape_3470_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3478_ = crate::leanh::lean_unsigned_to_nat(1114112);
                        v___x_3479_ = lean_nat_dec_lt(v_val_3473_, v___x_3478_);
                        if v___x_3479_ == 0 {
                            crate::leanh::lean_dec(v_val_3473_);
                            crate::leanh::lean_dec_ref(v_out_3444_);
                            crate::leanh::lean_dec_ref(v_lit_3442_);
                            v___y_3449_ = v___y_3471_;
                            v___y_3450_ = v___y_3472_;
                            v___y_3451_ = v_escape_3470_;
                            state = 1;
                            continue;
                        } else {
                            v___y_3461_ = v_val_3473_;
                            v___y_3462_ = v___y_3471_;
                            v___y_3463_ = v___y_3472_;
                            v___y_3464_ = v_escape_3470_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___y_3461_ = v_val_3473_;
                    v___y_3462_ = v___y_3471_;
                    v___y_3463_ = v___y_3472_;
                    v___y_3464_ = v_escape_3470_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___boxed(
    mut v_lit_3545_: *mut crate::leanh::LeanObject,
    mut v_i_3546_: *mut crate::leanh::LeanObject,
    mut v_out_3547_: *mut crate::leanh::LeanObject,
    mut v_a_3548_: *mut crate::leanh::LeanObject,
    mut v_a_3549_: *mut crate::leanh::LeanObject,
    mut v_a_3550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3551_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(
        v_lit_3545_,
        v_i_3546_,
        v_out_3547_,
        v_a_3548_,
        v_a_3549_,
    );
    crate::leanh::lean_dec(v_a_3549_);
    crate::leanh::lean_dec_ref(v_a_3548_);
    return v_res_3551_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3561_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__4;
    v___x_3562_ = l_Lean_MessageData_ofFormat(v___x_3561_);
    return v___x_3562_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(
    mut v_x_3563_: *mut crate::leanh::LeanObject,
    mut v_a_3564_: *mut crate::leanh::LeanObject,
    mut v_a_3565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3584_: u8 = 0;
    let mut v_cancelTk_x3f_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3586_: u8 = 0;
    let mut v_inheritedTraceOptions_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3599_ =
                    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2;
                v___x_3600_ = l_Lean_Syntax_isLit_x3f(v___x_3599_, v_x_3563_);
                if crate::leanh::lean_obj_tag(v___x_3600_) == 1 {
                    v_val_3601_ = crate::leanh::lean_ctor_get(v___x_3600_, 0);
                    crate::leanh::lean_inc(v_val_3601_);
                    crate::leanh::lean_dec_ref_known(v___x_3600_, 1);
                    v_a_3568_ = v_val_3601_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3600_);
                    v___x_3602_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5_once), _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5);
                    v___x_3603_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_3563_, v___x_3602_, v_a_3564_, v_a_3565_);
                    return v___x_3603_;
                }
            }
            1 => {
                v___x_3569_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3570_ = lean_string_utf8_byte_size(v_a_3568_);
                crate::leanh::lean_inc_ref_n(v_a_3568_, 2);
                v___x_3571_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3571_, 0, v_a_3568_);
                crate::leanh::lean_ctor_set(v___x_3571_, 1, v___x_3569_);
                crate::leanh::lean_ctor_set(v___x_3571_, 2, v___x_3570_);
                v_fileName_3572_ = crate::leanh::lean_ctor_get(v_a_3564_, 0);
                v_fileMap_3573_ = crate::leanh::lean_ctor_get(v_a_3564_, 1);
                v_options_3574_ = crate::leanh::lean_ctor_get(v_a_3564_, 2);
                v_currRecDepth_3575_ = crate::leanh::lean_ctor_get(v_a_3564_, 3);
                v_maxRecDepth_3576_ = crate::leanh::lean_ctor_get(v_a_3564_, 4);
                v_ref_3577_ = crate::leanh::lean_ctor_get(v_a_3564_, 5);
                v_currNamespace_3578_ = crate::leanh::lean_ctor_get(v_a_3564_, 6);
                v_openDecls_3579_ = crate::leanh::lean_ctor_get(v_a_3564_, 7);
                v_initHeartbeats_3580_ = crate::leanh::lean_ctor_get(v_a_3564_, 8);
                v_maxHeartbeats_3581_ = crate::leanh::lean_ctor_get(v_a_3564_, 9);
                v_quotContext_3582_ = crate::leanh::lean_ctor_get(v_a_3564_, 10);
                v_currMacroScope_3583_ = crate::leanh::lean_ctor_get(v_a_3564_, 11);
                v_diag_3584_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3564_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_3585_ = crate::leanh::lean_ctor_get(v_a_3564_, 12);
                v_suppressElabErrors_3586_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3564_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_3587_ = crate::leanh::lean_ctor_get(v_a_3564_, 13);
                v___x_3588_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3589_ = l_String_Slice_Pos_nextn(v___x_3571_, v___x_3569_, v___x_3588_);
                crate::leanh::lean_dec_ref_known(v___x_3571_, 3);
                crate::leanh::lean_inc(v___x_3589_);
                v___x_3590_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3590_, 0, v_a_3568_);
                crate::leanh::lean_ctor_set(v___x_3590_, 1, v___x_3589_);
                crate::leanh::lean_ctor_set(v___x_3590_, 2, v___x_3570_);
                v___x_3591_ = lean_nat_sub(v___x_3570_, v___x_3589_);
                v___x_3592_ = l_String_Slice_Pos_prevn(v___x_3590_, v___x_3591_, v___x_3588_);
                crate::leanh::lean_dec_ref_known(v___x_3590_, 3);
                v___x_3593_ = lean_nat_add(v___x_3589_, v___x_3592_);
                crate::leanh::lean_dec(v___x_3592_);
                v___x_3594_ = lean_string_utf8_extract(v_a_3568_, v___x_3589_, v___x_3593_);
                crate::leanh::lean_dec(v___x_3593_);
                crate::leanh::lean_dec(v___x_3589_);
                crate::leanh::lean_dec_ref(v_a_3568_);
                v___x_3595_ =
                    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0;
                v_ref_3596_ = l_Lean_replaceRef(v_x_3563_, v_ref_3577_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_3587_);
                crate::leanh::lean_inc(v_cancelTk_x3f_3585_);
                crate::leanh::lean_inc(v_currMacroScope_3583_);
                crate::leanh::lean_inc(v_quotContext_3582_);
                crate::leanh::lean_inc(v_maxHeartbeats_3581_);
                crate::leanh::lean_inc(v_initHeartbeats_3580_);
                crate::leanh::lean_inc(v_openDecls_3579_);
                crate::leanh::lean_inc(v_currNamespace_3578_);
                crate::leanh::lean_inc(v_maxRecDepth_3576_);
                crate::leanh::lean_inc(v_currRecDepth_3575_);
                crate::leanh::lean_inc_ref(v_options_3574_);
                crate::leanh::lean_inc_ref(v_fileMap_3573_);
                crate::leanh::lean_inc_ref(v_fileName_3572_);
                v___x_3597_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_3597_, 0, v_fileName_3572_);
                crate::leanh::lean_ctor_set(v___x_3597_, 1, v_fileMap_3573_);
                crate::leanh::lean_ctor_set(v___x_3597_, 2, v_options_3574_);
                crate::leanh::lean_ctor_set(v___x_3597_, 3, v_currRecDepth_3575_);
                crate::leanh::lean_ctor_set(v___x_3597_, 4, v_maxRecDepth_3576_);
                crate::leanh::lean_ctor_set(v___x_3597_, 5, v_ref_3596_);
                crate::leanh::lean_ctor_set(v___x_3597_, 6, v_currNamespace_3578_);
                crate::leanh::lean_ctor_set(v___x_3597_, 7, v_openDecls_3579_);
                crate::leanh::lean_ctor_set(v___x_3597_, 8, v_initHeartbeats_3580_);
                crate::leanh::lean_ctor_set(v___x_3597_, 9, v_maxHeartbeats_3581_);
                crate::leanh::lean_ctor_set(v___x_3597_, 10, v_quotContext_3582_);
                crate::leanh::lean_ctor_set(v___x_3597_, 11, v_currMacroScope_3583_);
                crate::leanh::lean_ctor_set(v___x_3597_, 12, v_cancelTk_x3f_3585_);
                crate::leanh::lean_ctor_set(v___x_3597_, 13, v_inheritedTraceOptions_3587_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3597_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_3584_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3597_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_3586_,
                );
                v___x_3598_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(
                    v___x_3594_,
                    v___x_3569_,
                    v___x_3595_,
                    v___x_3597_,
                    v_a_3565_,
                );
                crate::leanh::lean_dec_ref_known(v___x_3597_, 14);
                return v___x_3598_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___boxed(
    mut v_x_3604_: *mut crate::leanh::LeanObject,
    mut v_a_3605_: *mut crate::leanh::LeanObject,
    mut v_a_3606_: *mut crate::leanh::LeanObject,
    mut v_a_3607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3608_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(
        v_x_3604_, v_a_3605_, v_a_3606_,
    );
    crate::leanh::lean_dec(v_a_3606_);
    crate::leanh::lean_dec_ref(v_a_3605_);
    crate::leanh::lean_dec(v_x_3604_);
    return v_res_3608_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(
    mut v_s_3609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3611_: u32 = 0;
    let mut v___x_3612_: u32 = 0;
    let mut v___x_3613_: u8 = 0;
    let mut v___x_3614_: u32 = 0;
    let mut v___x_3615_: u8 = 0;
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: u32 = 0;
    let mut v_val_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3628_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3629_ = lean_string_utf8_byte_size(v_s_3609_);
                crate::leanh::lean_inc_ref(v_s_3609_);
                v___x_3630_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3630_, 0, v_s_3609_);
                crate::leanh::lean_ctor_set(v___x_3630_, 1, v___x_3628_);
                crate::leanh::lean_ctor_set(v___x_3630_, 2, v___x_3629_);
                v___x_3631_ = l_String_Slice_Pos_get_x3f(v___x_3630_, v___x_3628_);
                crate::leanh::lean_dec_ref_known(v___x_3630_, 3);
                if crate::leanh::lean_obj_tag(v___x_3631_) == 0 {
                    v___x_3632_ = 65;
                    v___y_3611_ = v___x_3632_;
                    state = 1;
                    continue;
                } else {
                    v_val_3633_ = crate::leanh::lean_ctor_get(v___x_3631_, 0);
                    crate::leanh::lean_inc(v_val_3633_);
                    crate::leanh::lean_dec_ref_known(v___x_3631_, 1);
                    v___x_3634_ = crate::leanh::lean_unbox_uint32(v_val_3633_);
                    crate::leanh::lean_dec(v_val_3633_);
                    v___y_3611_ = v___x_3634_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3612_ = 13;
                v___x_3613_ = lean_uint32_dec_eq(v___y_3611_, v___x_3612_);
                if v___x_3613_ == 0 {
                    v___x_3614_ = 10;
                    v___x_3615_ = lean_uint32_dec_eq(v___y_3611_, v___x_3614_);
                    if v___x_3615_ == 0 {
                        return v_s_3609_;
                    } else {
                        v___x_3616_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3617_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_3618_ = lean_string_utf8_byte_size(v_s_3609_);
                        crate::leanh::lean_inc_ref(v_s_3609_);
                        v___x_3619_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3619_, 0, v_s_3609_);
                        crate::leanh::lean_ctor_set(v___x_3619_, 1, v___x_3617_);
                        crate::leanh::lean_ctor_set(v___x_3619_, 2, v___x_3618_);
                        v___x_3620_ =
                            l_String_Slice_Pos_nextn(v___x_3619_, v___x_3617_, v___x_3616_);
                        crate::leanh::lean_dec_ref_known(v___x_3619_, 3);
                        v___x_3621_ = lean_string_utf8_extract(v_s_3609_, v___x_3620_, v___x_3618_);
                        crate::leanh::lean_dec(v___x_3620_);
                        crate::leanh::lean_dec_ref(v_s_3609_);
                        return v___x_3621_;
                    }
                } else {
                    v___x_3622_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_3623_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3624_ = lean_string_utf8_byte_size(v_s_3609_);
                    crate::leanh::lean_inc_ref(v_s_3609_);
                    v___x_3625_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3625_, 0, v_s_3609_);
                    crate::leanh::lean_ctor_set(v___x_3625_, 1, v___x_3623_);
                    crate::leanh::lean_ctor_set(v___x_3625_, 2, v___x_3624_);
                    v___x_3626_ = l_String_Slice_Pos_nextn(v___x_3625_, v___x_3623_, v___x_3622_);
                    crate::leanh::lean_dec_ref_known(v___x_3625_, 3);
                    v___x_3627_ = lean_string_utf8_extract(v_s_3609_, v___x_3626_, v___x_3624_);
                    crate::leanh::lean_dec(v___x_3626_);
                    crate::leanh::lean_dec_ref(v_s_3609_);
                    return v___x_3627_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3643_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__3;
    v___x_3644_ = l_Lean_MessageData_ofFormat(v___x_3643_);
    return v___x_3644_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(
    mut v_x_3645_: *mut crate::leanh::LeanObject,
    mut v_a_3646_: *mut crate::leanh::LeanObject,
    mut v_a_3647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3663_ =
                    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1;
                v___x_3664_ = l_Lean_Syntax_isLit_x3f(v___x_3663_, v_x_3645_);
                if crate::leanh::lean_obj_tag(v___x_3664_) == 1 {
                    v_val_3665_ = crate::leanh::lean_ctor_get(v___x_3664_, 0);
                    crate::leanh::lean_inc(v_val_3665_);
                    crate::leanh::lean_dec_ref_known(v___x_3664_, 1);
                    v_a_3650_ = v_val_3665_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3664_);
                    v___x_3666_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4_once), _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4);
                    v___x_3667_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_3645_, v___x_3666_, v_a_3646_, v_a_3647_);
                    return v___x_3667_;
                }
            }
            1 => {
                v___x_3651_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3652_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3653_ = lean_string_utf8_byte_size(v_a_3650_);
                crate::leanh::lean_inc_ref_n(v_a_3650_, 2);
                v___x_3654_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3654_, 0, v_a_3650_);
                crate::leanh::lean_ctor_set(v___x_3654_, 1, v___x_3652_);
                crate::leanh::lean_ctor_set(v___x_3654_, 2, v___x_3653_);
                v___x_3655_ = l_String_Slice_Pos_nextn(v___x_3654_, v___x_3652_, v___x_3651_);
                crate::leanh::lean_dec_ref_known(v___x_3654_, 3);
                crate::leanh::lean_inc(v___x_3655_);
                v___x_3656_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3656_, 0, v_a_3650_);
                crate::leanh::lean_ctor_set(v___x_3656_, 1, v___x_3655_);
                crate::leanh::lean_ctor_set(v___x_3656_, 2, v___x_3653_);
                v___x_3657_ = lean_nat_sub(v___x_3653_, v___x_3655_);
                v___x_3658_ = l_String_Slice_Pos_prevn(v___x_3656_, v___x_3657_, v___x_3651_);
                crate::leanh::lean_dec_ref_known(v___x_3656_, 3);
                v___x_3659_ = lean_nat_add(v___x_3655_, v___x_3658_);
                crate::leanh::lean_dec(v___x_3658_);
                v___x_3660_ = lean_string_utf8_extract(v_a_3650_, v___x_3655_, v___x_3659_);
                crate::leanh::lean_dec(v___x_3659_);
                crate::leanh::lean_dec(v___x_3655_);
                crate::leanh::lean_dec_ref(v_a_3650_);
                v___x_3661_ =
                    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(v___x_3660_);
                v___x_3662_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3662_, 0, v___x_3661_);
                return v___x_3662_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___boxed(
    mut v_x_3668_: *mut crate::leanh::LeanObject,
    mut v_a_3669_: *mut crate::leanh::LeanObject,
    mut v_a_3670_: *mut crate::leanh::LeanObject,
    mut v_a_3671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3672_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(
        v_x_3668_, v_a_3669_, v_a_3670_,
    );
    crate::leanh::lean_dec(v_a_3670_);
    crate::leanh::lean_dec_ref(v_a_3669_);
    crate::leanh::lean_dec(v_x_3668_);
    return v_res_3672_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3681_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__3;
    v___x_3682_ = l_Lean_MessageData_ofFormat(v___x_3681_);
    return v___x_3682_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(
    mut v_x_3683_: *mut crate::leanh::LeanObject,
    mut v_a_3684_: *mut crate::leanh::LeanObject,
    mut v_a_3685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3704_: u8 = 0;
    let mut v_cancelTk_x3f_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3706_: u8 = 0;
    let mut v_inheritedTraceOptions_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3720_ =
                    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1;
                v___x_3721_ = l_Lean_Syntax_isLit_x3f(v___x_3720_, v_x_3683_);
                if crate::leanh::lean_obj_tag(v___x_3721_) == 1 {
                    v_val_3722_ = crate::leanh::lean_ctor_get(v___x_3721_, 0);
                    crate::leanh::lean_inc(v_val_3722_);
                    crate::leanh::lean_dec_ref_known(v___x_3721_, 1);
                    v_a_3688_ = v_val_3722_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3721_);
                    v___x_3723_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4_once), _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4);
                    v___x_3724_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_3683_, v___x_3723_, v_a_3684_, v_a_3685_);
                    return v___x_3724_;
                }
            }
            1 => {
                v___x_3689_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3690_ = lean_string_utf8_byte_size(v_a_3688_);
                crate::leanh::lean_inc_ref_n(v_a_3688_, 2);
                v___x_3691_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3691_, 0, v_a_3688_);
                crate::leanh::lean_ctor_set(v___x_3691_, 1, v___x_3689_);
                crate::leanh::lean_ctor_set(v___x_3691_, 2, v___x_3690_);
                v_fileName_3692_ = crate::leanh::lean_ctor_get(v_a_3684_, 0);
                v_fileMap_3693_ = crate::leanh::lean_ctor_get(v_a_3684_, 1);
                v_options_3694_ = crate::leanh::lean_ctor_get(v_a_3684_, 2);
                v_currRecDepth_3695_ = crate::leanh::lean_ctor_get(v_a_3684_, 3);
                v_maxRecDepth_3696_ = crate::leanh::lean_ctor_get(v_a_3684_, 4);
                v_ref_3697_ = crate::leanh::lean_ctor_get(v_a_3684_, 5);
                v_currNamespace_3698_ = crate::leanh::lean_ctor_get(v_a_3684_, 6);
                v_openDecls_3699_ = crate::leanh::lean_ctor_get(v_a_3684_, 7);
                v_initHeartbeats_3700_ = crate::leanh::lean_ctor_get(v_a_3684_, 8);
                v_maxHeartbeats_3701_ = crate::leanh::lean_ctor_get(v_a_3684_, 9);
                v_quotContext_3702_ = crate::leanh::lean_ctor_get(v_a_3684_, 10);
                v_currMacroScope_3703_ = crate::leanh::lean_ctor_get(v_a_3684_, 11);
                v_diag_3704_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3684_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_3705_ = crate::leanh::lean_ctor_get(v_a_3684_, 12);
                v_suppressElabErrors_3706_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3684_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_3707_ = crate::leanh::lean_ctor_get(v_a_3684_, 13);
                v___x_3708_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3709_ = l_String_Slice_Pos_nextn(v___x_3691_, v___x_3689_, v___x_3708_);
                crate::leanh::lean_dec_ref_known(v___x_3691_, 3);
                crate::leanh::lean_inc(v___x_3709_);
                v___x_3710_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3710_, 0, v_a_3688_);
                crate::leanh::lean_ctor_set(v___x_3710_, 1, v___x_3709_);
                crate::leanh::lean_ctor_set(v___x_3710_, 2, v___x_3690_);
                v___x_3711_ = lean_nat_sub(v___x_3690_, v___x_3709_);
                v___x_3712_ = l_String_Slice_Pos_prevn(v___x_3710_, v___x_3711_, v___x_3708_);
                crate::leanh::lean_dec_ref_known(v___x_3710_, 3);
                v___x_3713_ = lean_nat_add(v___x_3709_, v___x_3712_);
                crate::leanh::lean_dec(v___x_3712_);
                v___x_3714_ = lean_string_utf8_extract(v_a_3688_, v___x_3709_, v___x_3713_);
                crate::leanh::lean_dec(v___x_3713_);
                crate::leanh::lean_dec(v___x_3709_);
                crate::leanh::lean_dec_ref(v_a_3688_);
                v___x_3715_ =
                    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(v___x_3714_);
                v___x_3716_ =
                    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0;
                v_ref_3717_ = l_Lean_replaceRef(v_x_3683_, v_ref_3697_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_3707_);
                crate::leanh::lean_inc(v_cancelTk_x3f_3705_);
                crate::leanh::lean_inc(v_currMacroScope_3703_);
                crate::leanh::lean_inc(v_quotContext_3702_);
                crate::leanh::lean_inc(v_maxHeartbeats_3701_);
                crate::leanh::lean_inc(v_initHeartbeats_3700_);
                crate::leanh::lean_inc(v_openDecls_3699_);
                crate::leanh::lean_inc(v_currNamespace_3698_);
                crate::leanh::lean_inc(v_maxRecDepth_3696_);
                crate::leanh::lean_inc(v_currRecDepth_3695_);
                crate::leanh::lean_inc_ref(v_options_3694_);
                crate::leanh::lean_inc_ref(v_fileMap_3693_);
                crate::leanh::lean_inc_ref(v_fileName_3692_);
                v___x_3718_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_3718_, 0, v_fileName_3692_);
                crate::leanh::lean_ctor_set(v___x_3718_, 1, v_fileMap_3693_);
                crate::leanh::lean_ctor_set(v___x_3718_, 2, v_options_3694_);
                crate::leanh::lean_ctor_set(v___x_3718_, 3, v_currRecDepth_3695_);
                crate::leanh::lean_ctor_set(v___x_3718_, 4, v_maxRecDepth_3696_);
                crate::leanh::lean_ctor_set(v___x_3718_, 5, v_ref_3717_);
                crate::leanh::lean_ctor_set(v___x_3718_, 6, v_currNamespace_3698_);
                crate::leanh::lean_ctor_set(v___x_3718_, 7, v_openDecls_3699_);
                crate::leanh::lean_ctor_set(v___x_3718_, 8, v_initHeartbeats_3700_);
                crate::leanh::lean_ctor_set(v___x_3718_, 9, v_maxHeartbeats_3701_);
                crate::leanh::lean_ctor_set(v___x_3718_, 10, v_quotContext_3702_);
                crate::leanh::lean_ctor_set(v___x_3718_, 11, v_currMacroScope_3703_);
                crate::leanh::lean_ctor_set(v___x_3718_, 12, v_cancelTk_x3f_3705_);
                crate::leanh::lean_ctor_set(v___x_3718_, 13, v_inheritedTraceOptions_3707_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3718_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_3704_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3718_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_3706_,
                );
                v___x_3719_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(
                    v___x_3715_,
                    v___x_3689_,
                    v___x_3716_,
                    v___x_3718_,
                    v_a_3685_,
                );
                crate::leanh::lean_dec_ref_known(v___x_3718_, 14);
                return v___x_3719_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___boxed(
    mut v_x_3725_: *mut crate::leanh::LeanObject,
    mut v_a_3726_: *mut crate::leanh::LeanObject,
    mut v_a_3727_: *mut crate::leanh::LeanObject,
    mut v_a_3728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3729_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(
        v_x_3725_, v_a_3726_, v_a_3727_,
    );
    crate::leanh::lean_dec(v_a_3727_);
    crate::leanh::lean_dec_ref(v_a_3726_);
    crate::leanh::lean_dec(v_x_3725_);
    return v_res_3729_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3736_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__2;
    v___x_3737_ = l_Lean_stringToMessageData(v___x_3736_);
    return v___x_3737_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(
    mut v_x_3738_: *mut crate::leanh::LeanObject,
    mut v_a_3739_: *mut crate::leanh::LeanObject,
    mut v_a_3740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: u8 = 0;
    v___x_3742_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1;
    crate::leanh::lean_inc(v_x_3738_);
    v___x_3743_ = l_Lean_Syntax_isOfKind(v_x_3738_, v___x_3742_);
    if v___x_3743_ == 0 {
        let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3744_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3
            ),
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3_once
            ),
            _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3,
        );
        v___x_3745_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_3738_, v___x_3744_, v_a_3739_, v_a_3740_);
        crate::leanh::lean_dec(v_x_3738_);
        return v___x_3745_;
    } else {
        let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3749_: u8 = 0;
        v___x_3746_ = crate::leanh::lean_unsigned_to_nat(0);
        v_x_3747_ = l_Lean_Syntax_getArg(v_x_3738_, v___x_3746_);
        v___x_3748_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1;
        crate::leanh::lean_inc(v_x_3747_);
        v___x_3749_ = l_Lean_Syntax_isOfKind(v_x_3747_, v___x_3748_);
        if v___x_3749_ == 0 {
            let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3751_: u8 = 0;
            v___x_3750_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2;
            crate::leanh::lean_inc(v_x_3747_);
            v___x_3751_ = l_Lean_Syntax_isOfKind(v_x_3747_, v___x_3750_);
            if v___x_3751_ == 0 {
                let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3753_: u8 = 0;
                v___x_3752_ =
                    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1;
                crate::leanh::lean_inc(v_x_3747_);
                v___x_3753_ = l_Lean_Syntax_isOfKind(v_x_3747_, v___x_3752_);
                if v___x_3753_ == 0 {
                    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3755_: u8 = 0;
                    v___x_3754_ =
                        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1;
                    crate::leanh::lean_inc(v_x_3747_);
                    v___x_3755_ = l_Lean_Syntax_isOfKind(v_x_3747_, v___x_3754_);
                    if v___x_3755_ == 0 {
                        let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v_x_3747_);
                        v___x_3756_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3_once), _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3);
                        v___x_3757_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_3738_, v___x_3756_, v_a_3739_, v_a_3740_);
                        crate::leanh::lean_dec(v_x_3738_);
                        return v___x_3757_;
                    } else {
                        let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v_x_3738_);
                        v___x_3758_ =
                            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(
                                v_x_3747_, v_a_3739_, v_a_3740_,
                            );
                        crate::leanh::lean_dec(v_x_3747_);
                        return v___x_3758_;
                    }
                } else {
                    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_x_3738_);
                    v___x_3759_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(
                        v_x_3747_, v_a_3739_, v_a_3740_,
                    );
                    crate::leanh::lean_dec(v_x_3747_);
                    return v___x_3759_;
                }
            } else {
                let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_x_3738_);
                v___x_3760_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(
                    v_x_3747_, v_a_3739_, v_a_3740_,
                );
                crate::leanh::lean_dec(v_x_3747_);
                return v___x_3760_;
            }
        } else {
            let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_3738_);
            v___x_3761_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(
                v_x_3747_, v_a_3739_, v_a_3740_,
            );
            crate::leanh::lean_dec(v_x_3747_);
            return v___x_3761_;
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___boxed(
    mut v_x_3762_: *mut crate::leanh::LeanObject,
    mut v_a_3763_: *mut crate::leanh::LeanObject,
    mut v_a_3764_: *mut crate::leanh::LeanObject,
    mut v_a_3765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3766_ =
        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(v_x_3762_, v_a_3763_, v_a_3764_);
    crate::leanh::lean_dec(v_a_3764_);
    crate::leanh::lean_dec_ref(v_a_3763_);
    return v_res_3766_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3775_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__3;
    v___x_3776_ = l_Lean_MessageData_ofFormat(v___x_3775_);
    return v___x_3776_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey(
    mut v_x_3777_: *mut crate::leanh::LeanObject,
    mut v_a_3778_: *mut crate::leanh::LeanObject,
    mut v_a_3779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3807_: u8 = 0;
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3811_: u8 = 0;
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_25__overap_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3781_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1_once
                    ),
                    _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1,
                );
                v_toApplicative_3782_ = crate::leanh::lean_ctor_get(v___x_3781_, 0);
                v_toFunctor_3783_ = crate::leanh::lean_ctor_get(v_toApplicative_3782_, 0);
                v_toSeq_3784_ = crate::leanh::lean_ctor_get(v_toApplicative_3782_, 2);
                v_toSeqLeft_3785_ = crate::leanh::lean_ctor_get(v_toApplicative_3782_, 3);
                v_toSeqRight_3786_ = crate::leanh::lean_ctor_get(v_toApplicative_3782_, 4);
                v___x_3787_ =
                    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1;
                v___f_3788_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2;
                v___f_3789_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_3783_, 2);
                v___f_3790_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3790_, 0, v_toFunctor_3783_);
                v___f_3791_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3791_, 0, v_toFunctor_3783_);
                v___x_3792_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3792_, 0, v___f_3790_);
                crate::leanh::lean_ctor_set(v___x_3792_, 1, v___f_3791_);
                crate::leanh::lean_inc(v_toSeqRight_3786_);
                v___f_3793_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3793_, 0, v_toSeqRight_3786_);
                crate::leanh::lean_inc(v_toSeqLeft_3785_);
                v___f_3794_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3794_, 0, v_toSeqLeft_3785_);
                crate::leanh::lean_inc(v_toSeq_3784_);
                v___f_3795_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3795_, 0, v_toSeq_3784_);
                v___x_3796_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3796_, 0, v___x_3792_);
                crate::leanh::lean_ctor_set(v___x_3796_, 1, v___f_3788_);
                crate::leanh::lean_ctor_set(v___x_3796_, 2, v___f_3795_);
                crate::leanh::lean_ctor_set(v___x_3796_, 3, v___f_3794_);
                crate::leanh::lean_ctor_set(v___x_3796_, 4, v___f_3793_);
                v___x_3797_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3797_, 0, v___x_3796_);
                crate::leanh::lean_ctor_set(v___x_3797_, 1, v___f_3789_);
                v___x_3798_ = l_Lean_instMonadExceptOfExceptionCoreM;
                v___x_3799_ = l_Lean_Core_instMonadRefCoreM;
                v___x_3800_ = l_Lean_Core_instAddMessageContextCoreM;
                crate::leanh::lean_inc_ref(v___x_3797_);
                v___x_3801_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___x_3800_,
                    v___x_3797_,
                );
                v___x_3802_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3802_, 0, v___x_3798_);
                crate::leanh::lean_ctor_set(v___x_3802_, 1, v___x_3799_);
                crate::leanh::lean_ctor_set(v___x_3802_, 2, v___x_3801_);
                v___x_3803_ = l_Lean_Syntax_isLit_x3f(v___x_3787_, v_x_3777_);
                if crate::leanh::lean_obj_tag(v___x_3803_) == 1 {
                    crate::leanh::lean_dec_ref_known(v___x_3802_, 3);
                    crate::leanh::lean_dec_ref_known(v___x_3797_, 2);
                    crate::leanh::lean_dec(v_x_3777_);
                    v_val_3804_ = crate::leanh::lean_ctor_get(v___x_3803_, 0);
                    v_isSharedCheck_3811_ = (!crate::leanh::lean_is_exclusive(v___x_3803_)) as u8;
                    if v_isSharedCheck_3811_ == 0 {
                        v___x_3806_ = v___x_3803_;
                        v_isShared_3807_ = v_isSharedCheck_3811_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3804_);
                        crate::leanh::lean_dec(v___x_3803_);
                        v___x_3806_ = crate::leanh::lean_box(0);
                        v_isShared_3807_ = v_isSharedCheck_3811_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3803_);
                    v___x_3812_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4_once), _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4);
                    v___x_25__overap_3813_ = l_Lean_throwErrorAt___redArg(
                        v___x_3797_,
                        v___x_3802_,
                        v_x_3777_,
                        v___x_3812_,
                    );
                    crate::leanh::lean_inc(v_a_3779_);
                    crate::leanh::lean_inc_ref(v_a_3778_);
                    v___x_3814_ = crate::leanh::lean_apply_3(
                        v___x_25__overap_3813_,
                        v_a_3778_,
                        v_a_3779_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3814_;
                }
            }
            1 => {
                if v_isShared_3807_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3806_, 0);
                    v___x_3809_ = v___x_3806_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3810_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_val_3804_);
                    v___x_3809_ = v_reuseFailAlloc_3810_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3809_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___boxed(
    mut v_x_3815_: *mut crate::leanh::LeanObject,
    mut v_a_3816_: *mut crate::leanh::LeanObject,
    mut v_a_3817_: *mut crate::leanh::LeanObject,
    mut v_a_3818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3819_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey(
        v_x_3815_, v_a_3816_, v_a_3817_,
    );
    crate::leanh::lean_dec(v_a_3817_);
    crate::leanh::lean_dec_ref(v_a_3816_);
    return v_res_3819_;
}
pub unsafe fn _init_l_Lake_Toml_elabSimpleKey___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3826_ = l_Lake_Toml_elabSimpleKey___closed__2;
    v___x_3827_ = l_Lean_stringToMessageData(v___x_3826_);
    return v___x_3827_;
}
pub unsafe fn l_Lake_Toml_elabSimpleKey(
    mut v_x_3828_: *mut crate::leanh::LeanObject,
    mut v_a_3829_: *mut crate::leanh::LeanObject,
    mut v_a_3830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: u8 = 0;
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: u8 = 0;
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: u8 = 0;
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: u8 = 0;
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3852_: u8 = 0;
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3856_: u8 = 0;
    let mut v___x_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3832_ = l_Lake_Toml_elabSimpleKey___closed__1;
                crate::leanh::lean_inc(v_x_3828_);
                v___x_3833_ = l_Lean_Syntax_isOfKind(v_x_3828_, v___x_3832_);
                if v___x_3833_ == 0 {
                    v___x_3834_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_Toml_elabSimpleKey___closed__3),
                        core::ptr::addr_of_mut!(l_Lake_Toml_elabSimpleKey___closed__3_once),
                        _init_l_Lake_Toml_elabSimpleKey___closed__3,
                    );
                    v___x_3835_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_3828_, v___x_3834_, v_a_3829_, v_a_3830_);
                    crate::leanh::lean_dec(v_x_3828_);
                    return v___x_3835_;
                } else {
                    v___x_3836_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_x_3837_ = l_Lean_Syntax_getArg(v_x_3828_, v___x_3836_);
                    v___x_3838_ =
                        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1;
                    crate::leanh::lean_inc(v_x_3837_);
                    v___x_3839_ = l_Lean_Syntax_isOfKind(v_x_3837_, v___x_3838_);
                    if v___x_3839_ == 0 {
                        v___x_3840_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1;
                        crate::leanh::lean_inc(v_x_3837_);
                        v___x_3841_ = l_Lean_Syntax_isOfKind(v_x_3837_, v___x_3840_);
                        if v___x_3841_ == 0 {
                            v___x_3842_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2;
                            crate::leanh::lean_inc(v_x_3837_);
                            v___x_3843_ = l_Lean_Syntax_isOfKind(v_x_3837_, v___x_3842_);
                            if v___x_3843_ == 0 {
                                crate::leanh::lean_dec(v_x_3837_);
                                v___x_3844_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(l_Lake_Toml_elabSimpleKey___closed__3),
                                    core::ptr::addr_of_mut!(
                                        l_Lake_Toml_elabSimpleKey___closed__3_once
                                    ),
                                    _init_l_Lake_Toml_elabSimpleKey___closed__3,
                                );
                                v___x_3845_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_3828_, v___x_3844_, v_a_3829_, v_a_3830_);
                                crate::leanh::lean_dec(v_x_3828_);
                                return v___x_3845_;
                            } else {
                                crate::leanh::lean_dec(v_x_3828_);
                                v___x_3846_ =
                                    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(
                                        v_x_3837_, v_a_3829_, v_a_3830_,
                                    );
                                crate::leanh::lean_dec(v_x_3837_);
                                return v___x_3846_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_x_3828_);
                            v___x_3847_ =
                                l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(
                                    v_x_3837_, v_a_3829_, v_a_3830_,
                                );
                            crate::leanh::lean_dec(v_x_3837_);
                            return v___x_3847_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_x_3828_);
                        v___x_3848_ = l_Lean_Syntax_isLit_x3f(v___x_3838_, v_x_3837_);
                        if crate::leanh::lean_obj_tag(v___x_3848_) == 1 {
                            crate::leanh::lean_dec(v_x_3837_);
                            v_val_3849_ = crate::leanh::lean_ctor_get(v___x_3848_, 0);
                            v_isSharedCheck_3856_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3848_)) as u8;
                            if v_isSharedCheck_3856_ == 0 {
                                v___x_3851_ = v___x_3848_;
                                v_isShared_3852_ = v_isSharedCheck_3856_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_3849_);
                                crate::leanh::lean_dec(v___x_3848_);
                                v___x_3851_ = crate::leanh::lean_box(0);
                                v_isShared_3852_ = v_isSharedCheck_3856_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_3848_);
                            v___x_3857_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4_once), _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4);
                            v___x_3858_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_3837_, v___x_3857_, v_a_3829_, v_a_3830_);
                            crate::leanh::lean_dec(v_x_3837_);
                            return v___x_3858_;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3852_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3851_, 0);
                    v___x_3854_ = v___x_3851_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3855_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_val_3849_);
                    v___x_3854_ = v_reuseFailAlloc_3855_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3854_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_elabSimpleKey___boxed(
    mut v_x_3859_: *mut crate::leanh::LeanObject,
    mut v_a_3860_: *mut crate::leanh::LeanObject,
    mut v_a_3861_: *mut crate::leanh::LeanObject,
    mut v_a_3862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3863_ = l_Lake_Toml_elabSimpleKey(v_x_3859_, v_a_3860_, v_a_3861_);
    crate::leanh::lean_dec(v_a_3861_);
    crate::leanh::lean_dec_ref(v_a_3860_);
    return v_res_3863_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(
    mut v_elabVal_3864_: *mut crate::leanh::LeanObject,
    mut v_sz_3865_: usize,
    mut v_i_3866_: usize,
    mut v_bs_3867_: *mut crate::leanh::LeanObject,
    mut v___y_3868_: *mut crate::leanh::LeanObject,
    mut v___y_3869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3871_: u8 = 0;
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: usize = 0;
    let mut v___x_3879_: usize = 0;
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3885_: u8 = 0;
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3889_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3871_ = lean_usize_dec_lt(v_i_3866_, v_sz_3865_);
                if v___x_3871_ == 0 {
                    crate::leanh::lean_dec_ref(v_elabVal_3864_);
                    v___x_3872_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3872_, 0, v_bs_3867_);
                    return v___x_3872_;
                } else {
                    v_v_3873_ = lean_array_uget_borrowed(v_bs_3867_, v_i_3866_);
                    crate::leanh::lean_inc_ref(v_elabVal_3864_);
                    crate::leanh::lean_inc(v___y_3869_);
                    crate::leanh::lean_inc_ref(v___y_3868_);
                    crate::leanh::lean_inc(v_v_3873_);
                    v___x_3874_ = crate::leanh::lean_apply_4(
                        v_elabVal_3864_,
                        v_v_3873_,
                        v___y_3868_,
                        v___y_3869_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3874_) == 0 {
                        v_a_3875_ = crate::leanh::lean_ctor_get(v___x_3874_, 0);
                        crate::leanh::lean_inc(v_a_3875_);
                        crate::leanh::lean_dec_ref_known(v___x_3874_, 1);
                        v___x_3876_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3877_ = lean_array_uset(v_bs_3867_, v_i_3866_, v___x_3876_);
                        v___x_3878_ = 1usize;
                        v___x_3879_ = lean_usize_add(v_i_3866_, v___x_3878_);
                        v___x_3880_ = lean_array_uset(v_bs_x27_3877_, v_i_3866_, v_a_3875_);
                        v_i_3866_ = v___x_3879_;
                        v_bs_3867_ = v___x_3880_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_3867_);
                        crate::leanh::lean_dec_ref(v_elabVal_3864_);
                        v_a_3882_ = crate::leanh::lean_ctor_get(v___x_3874_, 0);
                        v_isSharedCheck_3889_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3874_)) as u8;
                        if v_isSharedCheck_3889_ == 0 {
                            v___x_3884_ = v___x_3874_;
                            v_isShared_3885_ = v_isSharedCheck_3889_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3882_);
                            crate::leanh::lean_dec(v___x_3874_);
                            v___x_3884_ = crate::leanh::lean_box(0);
                            v_isShared_3885_ = v_isSharedCheck_3889_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3885_ == 0 {
                    v___x_3887_ = v___x_3884_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3888_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_a_3882_);
                    v___x_3887_ = v_reuseFailAlloc_3888_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3887_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg___boxed(
    mut v_elabVal_3890_: *mut crate::leanh::LeanObject,
    mut v_sz_3891_: *mut crate::leanh::LeanObject,
    mut v_i_3892_: *mut crate::leanh::LeanObject,
    mut v_bs_3893_: *mut crate::leanh::LeanObject,
    mut v___y_3894_: *mut crate::leanh::LeanObject,
    mut v___y_3895_: *mut crate::leanh::LeanObject,
    mut v___y_3896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3897_: usize = 0;
    let mut v_i_boxed_3898_: usize = 0;
    let mut v_res_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3897_ = crate::leanh::lean_unbox_usize(v_sz_3891_);
    crate::leanh::lean_dec(v_sz_3891_);
    v_i_boxed_3898_ = crate::leanh::lean_unbox_usize(v_i_3892_);
    crate::leanh::lean_dec(v_i_3892_);
    v_res_3899_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_3890_, v_sz_boxed_3897_, v_i_boxed_3898_, v_bs_3893_, v___y_3894_, v___y_3895_);
    crate::leanh::lean_dec(v___y_3895_);
    crate::leanh::lean_dec_ref(v___y_3894_);
    return v_res_3899_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3906_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__2;
    v___x_3907_ = l_Lean_stringToMessageData(v___x_3906_);
    return v___x_3907_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(
    mut v_x_3908_: *mut crate::leanh::LeanObject,
    mut v_elabVal_3909_: *mut crate::leanh::LeanObject,
    mut v_a_3910_: *mut crate::leanh::LeanObject,
    mut v_a_3911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: u8 = 0;
    v___x_3913_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1;
    crate::leanh::lean_inc(v_x_3908_);
    v___x_3914_ = l_Lean_Syntax_isOfKind(v_x_3908_, v___x_3913_);
    if v___x_3914_ == 0 {
        let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_elabVal_3909_);
        v___x_3915_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3
            ),
            core::ptr::addr_of_mut!(
                l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3_once
            ),
            _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3,
        );
        v___x_3916_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_3908_, v___x_3915_, v_a_3910_, v_a_3911_);
        crate::leanh::lean_dec(v_x_3908_);
        return v___x_3916_;
    } else {
        let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_xs_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_3921_: usize = 0;
        let mut v___x_3922_: usize = 0;
        let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3917_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_3918_ = l_Lean_Syntax_getArg(v_x_3908_, v___x_3917_);
        crate::leanh::lean_dec(v_x_3908_);
        v_xs_3919_ = l_Lean_Syntax_getArgs(v___x_3918_);
        crate::leanh::lean_dec(v___x_3918_);
        v___x_3920_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_xs_3919_);
        crate::leanh::lean_dec_ref(v_xs_3919_);
        v_sz_3921_ = lean_array_size(v___x_3920_);
        v___x_3922_ = 0usize;
        v___x_3923_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_3909_, v_sz_3921_, v___x_3922_, v___x_3920_, v_a_3910_, v_a_3911_);
        return v___x_3923_;
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___boxed(
    mut v_x_3924_: *mut crate::leanh::LeanObject,
    mut v_elabVal_3925_: *mut crate::leanh::LeanObject,
    mut v_a_3926_: *mut crate::leanh::LeanObject,
    mut v_a_3927_: *mut crate::leanh::LeanObject,
    mut v_a_3928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3929_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(
        v_x_3924_,
        v_elabVal_3925_,
        v_a_3926_,
        v_a_3927_,
    );
    crate::leanh::lean_dec(v_a_3927_);
    crate::leanh::lean_dec_ref(v_a_3926_);
    return v_res_3929_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray(
    mut v_00_u03b1_3930_: *mut crate::leanh::LeanObject,
    mut v_x_3931_: *mut crate::leanh::LeanObject,
    mut v_elabVal_3932_: *mut crate::leanh::LeanObject,
    mut v_a_3933_: *mut crate::leanh::LeanObject,
    mut v_a_3934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3936_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(
        v_x_3931_,
        v_elabVal_3932_,
        v_a_3933_,
        v_a_3934_,
    );
    return v___x_3936_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___boxed(
    mut v_00_u03b1_3937_: *mut crate::leanh::LeanObject,
    mut v_x_3938_: *mut crate::leanh::LeanObject,
    mut v_elabVal_3939_: *mut crate::leanh::LeanObject,
    mut v_a_3940_: *mut crate::leanh::LeanObject,
    mut v_a_3941_: *mut crate::leanh::LeanObject,
    mut v_a_3942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3943_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray(
        v_00_u03b1_3937_,
        v_x_3938_,
        v_elabVal_3939_,
        v_a_3940_,
        v_a_3941_,
    );
    crate::leanh::lean_dec(v_a_3941_);
    crate::leanh::lean_dec_ref(v_a_3940_);
    return v_res_3943_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0(
    mut v_00_u03b1_3944_: *mut crate::leanh::LeanObject,
    mut v_elabVal_3945_: *mut crate::leanh::LeanObject,
    mut v_sz_3946_: usize,
    mut v_i_3947_: usize,
    mut v_bs_3948_: *mut crate::leanh::LeanObject,
    mut v___y_3949_: *mut crate::leanh::LeanObject,
    mut v___y_3950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3952_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_3945_, v_sz_3946_, v_i_3947_, v_bs_3948_, v___y_3949_, v___y_3950_);
    return v___x_3952_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___boxed(
    mut v_00_u03b1_3953_: *mut crate::leanh::LeanObject,
    mut v_elabVal_3954_: *mut crate::leanh::LeanObject,
    mut v_sz_3955_: *mut crate::leanh::LeanObject,
    mut v_i_3956_: *mut crate::leanh::LeanObject,
    mut v_bs_3957_: *mut crate::leanh::LeanObject,
    mut v___y_3958_: *mut crate::leanh::LeanObject,
    mut v___y_3959_: *mut crate::leanh::LeanObject,
    mut v___y_3960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3961_: usize = 0;
    let mut v_i_boxed_3962_: usize = 0;
    let mut v_res_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3961_ = crate::leanh::lean_unbox_usize(v_sz_3955_);
    crate::leanh::lean_dec(v_sz_3955_);
    v_i_boxed_3962_ = crate::leanh::lean_unbox_usize(v_i_3956_);
    crate::leanh::lean_dec(v_i_3956_);
    v_res_3963_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0(v_00_u03b1_3953_, v_elabVal_3954_, v_sz_boxed_3961_, v_i_boxed_3962_, v_bs_3957_, v___y_3958_, v___y_3959_);
    crate::leanh::lean_dec(v___y_3959_);
    crate::leanh::lean_dec_ref(v___y_3958_);
    return v_res_3963_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg(
    mut v_msg_3964_: *mut crate::leanh::LeanObject,
    mut v___y_3965_: *mut crate::leanh::LeanObject,
    mut v___y_3966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3973_: u8 = 0;
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3978_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3968_ = crate::leanh::lean_ctor_get(v___y_3965_, 5);
                v___x_3969_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(v_msg_3964_, v___y_3965_, v___y_3966_);
                v_a_3970_ = crate::leanh::lean_ctor_get(v___x_3969_, 0);
                v_isSharedCheck_3978_ = (!crate::leanh::lean_is_exclusive(v___x_3969_)) as u8;
                if v_isSharedCheck_3978_ == 0 {
                    v___x_3972_ = v___x_3969_;
                    v_isShared_3973_ = v_isSharedCheck_3978_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3970_);
                    crate::leanh::lean_dec(v___x_3969_);
                    v___x_3972_ = crate::leanh::lean_box(0);
                    v_isShared_3973_ = v_isSharedCheck_3978_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3968_);
                v___x_3974_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3974_, 0, v_ref_3968_);
                crate::leanh::lean_ctor_set(v___x_3974_, 1, v_a_3970_);
                if v_isShared_3973_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3972_, 1);
                    crate::leanh::lean_ctor_set(v___x_3972_, 0, v___x_3974_);
                    v___x_3976_ = v___x_3972_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3977_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3974_);
                    v___x_3976_ = v_reuseFailAlloc_3977_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3976_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg___boxed(
    mut v_msg_3979_: *mut crate::leanh::LeanObject,
    mut v___y_3980_: *mut crate::leanh::LeanObject,
    mut v___y_3981_: *mut crate::leanh::LeanObject,
    mut v___y_3982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3983_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg(v_msg_3979_, v___y_3980_, v___y_3981_);
    crate::leanh::lean_dec(v___y_3981_);
    crate::leanh::lean_dec_ref(v___y_3980_);
    return v_res_3983_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg(
    mut v_ref_3984_: *mut crate::leanh::LeanObject,
    mut v_msg_3985_: *mut crate::leanh::LeanObject,
    mut v___y_3986_: *mut crate::leanh::LeanObject,
    mut v___y_3987_: *mut crate::leanh::LeanObject,
    mut v___y_3988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4002_: u8 = 0;
    let mut v_cancelTk_x3f_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4004_: u8 = 0;
    let mut v_inheritedTraceOptions_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3990_ = crate::leanh::lean_ctor_get(v___y_3987_, 0);
    v_fileMap_3991_ = crate::leanh::lean_ctor_get(v___y_3987_, 1);
    v_options_3992_ = crate::leanh::lean_ctor_get(v___y_3987_, 2);
    v_currRecDepth_3993_ = crate::leanh::lean_ctor_get(v___y_3987_, 3);
    v_maxRecDepth_3994_ = crate::leanh::lean_ctor_get(v___y_3987_, 4);
    v_ref_3995_ = crate::leanh::lean_ctor_get(v___y_3987_, 5);
    v_currNamespace_3996_ = crate::leanh::lean_ctor_get(v___y_3987_, 6);
    v_openDecls_3997_ = crate::leanh::lean_ctor_get(v___y_3987_, 7);
    v_initHeartbeats_3998_ = crate::leanh::lean_ctor_get(v___y_3987_, 8);
    v_maxHeartbeats_3999_ = crate::leanh::lean_ctor_get(v___y_3987_, 9);
    v_quotContext_4000_ = crate::leanh::lean_ctor_get(v___y_3987_, 10);
    v_currMacroScope_4001_ = crate::leanh::lean_ctor_get(v___y_3987_, 11);
    v_diag_4002_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3987_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_4003_ = crate::leanh::lean_ctor_get(v___y_3987_, 12);
    v_suppressElabErrors_4004_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3987_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_4005_ = crate::leanh::lean_ctor_get(v___y_3987_, 13);
    v_ref_4006_ = l_Lean_replaceRef(v_ref_3984_, v_ref_3995_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_4005_);
    crate::leanh::lean_inc(v_cancelTk_x3f_4003_);
    crate::leanh::lean_inc(v_currMacroScope_4001_);
    crate::leanh::lean_inc(v_quotContext_4000_);
    crate::leanh::lean_inc(v_maxHeartbeats_3999_);
    crate::leanh::lean_inc(v_initHeartbeats_3998_);
    crate::leanh::lean_inc(v_openDecls_3997_);
    crate::leanh::lean_inc(v_currNamespace_3996_);
    crate::leanh::lean_inc(v_maxRecDepth_3994_);
    crate::leanh::lean_inc(v_currRecDepth_3993_);
    crate::leanh::lean_inc_ref(v_options_3992_);
    crate::leanh::lean_inc_ref(v_fileMap_3991_);
    crate::leanh::lean_inc_ref(v_fileName_3990_);
    v___x_4007_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_4007_, 0, v_fileName_3990_);
    crate::leanh::lean_ctor_set(v___x_4007_, 1, v_fileMap_3991_);
    crate::leanh::lean_ctor_set(v___x_4007_, 2, v_options_3992_);
    crate::leanh::lean_ctor_set(v___x_4007_, 3, v_currRecDepth_3993_);
    crate::leanh::lean_ctor_set(v___x_4007_, 4, v_maxRecDepth_3994_);
    crate::leanh::lean_ctor_set(v___x_4007_, 5, v_ref_4006_);
    crate::leanh::lean_ctor_set(v___x_4007_, 6, v_currNamespace_3996_);
    crate::leanh::lean_ctor_set(v___x_4007_, 7, v_openDecls_3997_);
    crate::leanh::lean_ctor_set(v___x_4007_, 8, v_initHeartbeats_3998_);
    crate::leanh::lean_ctor_set(v___x_4007_, 9, v_maxHeartbeats_3999_);
    crate::leanh::lean_ctor_set(v___x_4007_, 10, v_quotContext_4000_);
    crate::leanh::lean_ctor_set(v___x_4007_, 11, v_currMacroScope_4001_);
    crate::leanh::lean_ctor_set(v___x_4007_, 12, v_cancelTk_x3f_4003_);
    crate::leanh::lean_ctor_set(v___x_4007_, 13, v_inheritedTraceOptions_4005_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4007_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_4002_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_4007_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_4004_,
    );
    v___x_4008_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg(v_msg_3985_, v___x_4007_, v___y_3988_);
    crate::leanh::lean_dec_ref_known(v___x_4007_, 14);
    return v___x_4008_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg___boxed(
    mut v_ref_4009_: *mut crate::leanh::LeanObject,
    mut v_msg_4010_: *mut crate::leanh::LeanObject,
    mut v___y_4011_: *mut crate::leanh::LeanObject,
    mut v___y_4012_: *mut crate::leanh::LeanObject,
    mut v___y_4013_: *mut crate::leanh::LeanObject,
    mut v___y_4014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4015_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg(v_ref_4009_, v_msg_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
    crate::leanh::lean_dec(v___y_4013_);
    crate::leanh::lean_dec_ref(v___y_4012_);
    crate::leanh::lean_dec_ref(v___y_4011_);
    crate::leanh::lean_dec(v_ref_4009_);
    return v_res_4015_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1;
    v___x_4019_ = l_Lean_stringToMessageData(v___x_4018_);
    return v___x_4019_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(
    mut v_t_4020_: *mut crate::leanh::LeanObject,
    mut v___x_4021_: u8,
    mut v_as_4022_: *mut crate::leanh::LeanObject,
    mut v_i_4023_: usize,
    mut v_stop_4024_: usize,
    mut v_b_4025_: *mut crate::leanh::LeanObject,
    mut v___y_4026_: *mut crate::leanh::LeanObject,
    mut v___y_4027_: *mut crate::leanh::LeanObject,
    mut v___y_4028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: usize = 0;
    let mut v___x_4034_: usize = 0;
    let mut v___x_4036_: u8 = 0;
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4054_: u8 = 0;
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4058_: u8 = 0;
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4067_: u8 = 0;
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4071_: u8 = 0;
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4036_ = lean_usize_dec_eq(v_i_4023_, v_stop_4024_);
                if v___x_4036_ == 0 {
                    v___x_4037_ = lean_array_uget_borrowed(v_as_4022_, v_i_4023_);
                    crate::leanh::lean_inc(v___x_4037_);
                    v___x_4038_ = l_Lake_Toml_elabSimpleKey(v___x_4037_, v___y_4027_, v___y_4028_);
                    if crate::leanh::lean_obj_tag(v___x_4038_) == 0 {
                        v_a_4039_ = crate::leanh::lean_ctor_get(v___x_4038_, 0);
                        crate::leanh::lean_inc(v_a_4039_);
                        crate::leanh::lean_dec_ref_known(v___x_4038_, 1);
                        v___x_4040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0;
                        v___x_4041_ = l_Lean_Name_str___override(v_b_4025_, v_a_4039_);
                        crate::leanh::lean_inc_ref(v_t_4020_);
                        crate::leanh::lean_inc(v___x_4041_);
                        v___x_4059_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(
                            v___x_4040_,
                            v___x_4041_,
                            v_t_4020_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4059_) == 0 {
                            v___x_4060_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v___x_4041_);
                            v___x_4061_ = l_Lake_Toml_RBDict_push___redArg(
                                v___x_4040_,
                                v___x_4041_,
                                v___x_4060_,
                                v___y_4026_,
                            );
                            v_fst_4031_ = v___x_4041_;
                            v_snd_4032_ = v___x_4061_;
                            state = 1;
                            continue;
                        } else {
                            v_val_4062_ = crate::leanh::lean_ctor_get(v___x_4059_, 0);
                            crate::leanh::lean_inc(v_val_4062_);
                            crate::leanh::lean_dec_ref_known(v___x_4059_, 1);
                            v_snd_4063_ = crate::leanh::lean_ctor_get(v_val_4062_, 1);
                            crate::leanh::lean_inc(v_snd_4063_);
                            crate::leanh::lean_dec(v_val_4062_);
                            if crate::leanh::lean_obj_tag(v_snd_4063_) == 0 {
                                if v___x_4021_ == 0 {
                                    state = 2;
                                    continue;
                                } else {
                                    v_fst_4031_ = v___x_4041_;
                                    v_snd_4032_ = v___y_4026_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_snd_4063_, 1);
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_4026_);
                        crate::leanh::lean_dec(v_b_4025_);
                        crate::leanh::lean_dec_ref(v_t_4020_);
                        v_a_4064_ = crate::leanh::lean_ctor_get(v___x_4038_, 0);
                        v_isSharedCheck_4071_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4038_)) as u8;
                        if v_isSharedCheck_4071_ == 0 {
                            v___x_4066_ = v___x_4038_;
                            v_isShared_4067_ = v_isSharedCheck_4071_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4064_);
                            crate::leanh::lean_dec(v___x_4038_);
                            v___x_4066_ = crate::leanh::lean_box(0);
                            v_isShared_4067_ = v_isSharedCheck_4071_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_t_4020_);
                    v___x_4072_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4072_, 0, v_b_4025_);
                    crate::leanh::lean_ctor_set(v___x_4072_, 1, v___y_4026_);
                    v___x_4073_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4073_, 0, v___x_4072_);
                    return v___x_4073_;
                }
            }
            1 => {
                v___x_4033_ = 1usize;
                v___x_4034_ = lean_usize_add(v_i_4023_, v___x_4033_);
                v_i_4023_ = v___x_4034_;
                v_b_4025_ = v_fst_4031_;
                v___y_4026_ = v_snd_4032_;
                state = 0;
                continue;
            }
            2 => {
                v___x_4043_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2);
                crate::leanh::lean_inc(v___x_4041_);
                v___x_4044_ = l_Lean_MessageData_ofName(v___x_4041_);
                v___x_4045_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4045_, 0, v___x_4043_);
                crate::leanh::lean_ctor_set(v___x_4045_, 1, v___x_4044_);
                v___x_4046_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once), _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
                v___x_4047_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4047_, 0, v___x_4045_);
                crate::leanh::lean_ctor_set(v___x_4047_, 1, v___x_4046_);
                v___x_4048_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg(v___x_4037_, v___x_4047_, v___y_4026_, v___y_4027_, v___y_4028_);
                crate::leanh::lean_dec_ref(v___y_4026_);
                if crate::leanh::lean_obj_tag(v___x_4048_) == 0 {
                    v_a_4049_ = crate::leanh::lean_ctor_get(v___x_4048_, 0);
                    crate::leanh::lean_inc(v_a_4049_);
                    crate::leanh::lean_dec_ref_known(v___x_4048_, 1);
                    v_snd_4050_ = crate::leanh::lean_ctor_get(v_a_4049_, 1);
                    crate::leanh::lean_inc(v_snd_4050_);
                    crate::leanh::lean_dec(v_a_4049_);
                    v_fst_4031_ = v___x_4041_;
                    v_snd_4032_ = v_snd_4050_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_4041_);
                    crate::leanh::lean_dec_ref(v_t_4020_);
                    v_a_4051_ = crate::leanh::lean_ctor_get(v___x_4048_, 0);
                    v_isSharedCheck_4058_ = (!crate::leanh::lean_is_exclusive(v___x_4048_)) as u8;
                    if v_isSharedCheck_4058_ == 0 {
                        v___x_4053_ = v___x_4048_;
                        v_isShared_4054_ = v_isSharedCheck_4058_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4051_);
                        crate::leanh::lean_dec(v___x_4048_);
                        v___x_4053_ = crate::leanh::lean_box(0);
                        v_isShared_4054_ = v_isSharedCheck_4058_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4054_ == 0 {
                    v___x_4056_ = v___x_4053_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4057_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_a_4051_);
                    v___x_4056_ = v_reuseFailAlloc_4057_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4056_;
            }
            5 => {
                if v_isShared_4067_ == 0 {
                    v___x_4069_ = v___x_4066_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4070_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
                    v___x_4069_ = v_reuseFailAlloc_4070_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4069_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___boxed(
    mut v_t_4074_: *mut crate::leanh::LeanObject,
    mut v___x_4075_: *mut crate::leanh::LeanObject,
    mut v_as_4076_: *mut crate::leanh::LeanObject,
    mut v_i_4077_: *mut crate::leanh::LeanObject,
    mut v_stop_4078_: *mut crate::leanh::LeanObject,
    mut v_b_4079_: *mut crate::leanh::LeanObject,
    mut v___y_4080_: *mut crate::leanh::LeanObject,
    mut v___y_4081_: *mut crate::leanh::LeanObject,
    mut v___y_4082_: *mut crate::leanh::LeanObject,
    mut v___y_4083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9546__boxed_4084_: u8 = 0;
    let mut v_i_boxed_4085_: usize = 0;
    let mut v_stop_boxed_4086_: usize = 0;
    let mut v_res_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9546__boxed_4084_ = (crate::leanh::lean_unbox(v___x_4075_) as u8);
    v_i_boxed_4085_ = crate::leanh::lean_unbox_usize(v_i_4077_);
    crate::leanh::lean_dec(v_i_4077_);
    v_stop_boxed_4086_ = crate::leanh::lean_unbox_usize(v_stop_4078_);
    crate::leanh::lean_dec(v_stop_4078_);
    v_res_4087_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_t_4074_, v___x_9546__boxed_4084_, v_as_4076_, v_i_boxed_4085_, v_stop_boxed_4086_, v_b_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
    crate::leanh::lean_dec(v___y_4082_);
    crate::leanh::lean_dec_ref(v___y_4081_);
    crate::leanh::lean_dec_ref(v_as_4076_);
    return v_res_4087_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(
    mut v_sz_4088_: usize,
    mut v_i_4089_: usize,
    mut v_bs_4090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4091_: u8 = 0;
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: usize = 0;
    let mut v___x_4097_: usize = 0;
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4091_ = lean_usize_dec_lt(v_i_4089_, v_sz_4088_);
                if v___x_4091_ == 0 {
                    v___x_4092_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4092_, 0, v_bs_4090_);
                    return v___x_4092_;
                } else {
                    v_v_4093_ = lean_array_uget(v_bs_4090_, v_i_4089_);
                    v___x_4094_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4095_ = lean_array_uset(v_bs_4090_, v_i_4089_, v___x_4094_);
                    v___x_4096_ = 1usize;
                    v___x_4097_ = lean_usize_add(v_i_4089_, v___x_4096_);
                    v___x_4098_ = lean_array_uset(v_bs_x27_4095_, v_i_4089_, v_v_4093_);
                    v_i_4089_ = v___x_4097_;
                    v_bs_4090_ = v___x_4098_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___boxed(
    mut v_sz_4100_: *mut crate::leanh::LeanObject,
    mut v_i_4101_: *mut crate::leanh::LeanObject,
    mut v_bs_4102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4103_: usize = 0;
    let mut v_i_boxed_4104_: usize = 0;
    let mut v_res_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4103_ = crate::leanh::lean_unbox_usize(v_sz_4100_);
    crate::leanh::lean_dec(v_sz_4100_);
    v_i_boxed_4104_ = crate::leanh::lean_unbox_usize(v_i_4101_);
    crate::leanh::lean_dec(v_i_4101_);
    v_res_4105_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(v_sz_boxed_4103_, v_i_boxed_4104_, v_bs_4102_);
    return v_res_4105_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(
    mut v___x_4106_: u8,
    mut v_as_4107_: *mut crate::leanh::LeanObject,
    mut v_i_4108_: usize,
    mut v_stop_4109_: usize,
    mut v_b_4110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: usize = 0;
    let mut v___x_4114_: usize = 0;
    let mut v___x_4116_: u8 = 0;
    let mut v_fst_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: u8 = 0;
    let mut v_snd_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4122_: u8 = 0;
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4127_: u8 = 0;
    let mut v_unused_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4132_: u8 = 0;
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4139_: u8 = 0;
    let mut v_unused_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4116_ = lean_usize_dec_eq(v_i_4108_, v_stop_4109_);
                if v___x_4116_ == 0 {
                    v_fst_4117_ = crate::leanh::lean_ctor_get(v_b_4110_, 0);
                    v___x_4118_ = (crate::leanh::lean_unbox(v_fst_4117_) as u8);
                    if v___x_4118_ == 0 {
                        v_snd_4119_ = crate::leanh::lean_ctor_get(v_b_4110_, 1);
                        v_isSharedCheck_4127_ = (!crate::leanh::lean_is_exclusive(v_b_4110_)) as u8;
                        if v_isSharedCheck_4127_ == 0 {
                            v_unused_4128_ = crate::leanh::lean_ctor_get(v_b_4110_, 0);
                            crate::leanh::lean_dec(v_unused_4128_);
                            v___x_4121_ = v_b_4110_;
                            v_isShared_4122_ = v_isSharedCheck_4127_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_4119_);
                            crate::leanh::lean_dec(v_b_4110_);
                            v___x_4121_ = crate::leanh::lean_box(0);
                            v_isShared_4122_ = v_isSharedCheck_4127_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_snd_4129_ = crate::leanh::lean_ctor_get(v_b_4110_, 1);
                        v_isSharedCheck_4139_ = (!crate::leanh::lean_is_exclusive(v_b_4110_)) as u8;
                        if v_isSharedCheck_4139_ == 0 {
                            v_unused_4140_ = crate::leanh::lean_ctor_get(v_b_4110_, 0);
                            crate::leanh::lean_dec(v_unused_4140_);
                            v___x_4131_ = v_b_4110_;
                            v_isShared_4132_ = v_isSharedCheck_4139_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_4129_);
                            crate::leanh::lean_dec(v_b_4110_);
                            v___x_4131_ = crate::leanh::lean_box(0);
                            v_isShared_4132_ = v_isSharedCheck_4139_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    return v_b_4110_;
                }
            }
            1 => {
                v___x_4113_ = 1usize;
                v___x_4114_ = lean_usize_add(v_i_4108_, v___x_4113_);
                v_i_4108_ = v___x_4114_;
                v_b_4110_ = v___y_4112_;
                state = 0;
                continue;
            }
            2 => {
                v___x_4123_ = crate::leanh::lean_box((v___x_4106_) as usize);
                if v_isShared_4122_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4121_, 0, v___x_4123_);
                    v___x_4125_ = v___x_4121_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4126_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_4123_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4126_, 1, v_snd_4119_);
                    v___x_4125_ = v_reuseFailAlloc_4126_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_4112_ = v___x_4125_;
                state = 1;
                continue;
            }
            4 => {
                v___x_4133_ = lean_array_uget_borrowed(v_as_4107_, v_i_4108_);
                crate::leanh::lean_inc(v___x_4133_);
                v___x_4134_ = lean_array_push(v_snd_4129_, v___x_4133_);
                v___x_4135_ = crate::leanh::lean_box((v___x_4116_) as usize);
                if v_isShared_4132_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4131_, 1, v___x_4134_);
                    crate::leanh::lean_ctor_set(v___x_4131_, 0, v___x_4135_);
                    v___x_4137_ = v___x_4131_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4138_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4138_, 0, v___x_4135_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4138_, 1, v___x_4134_);
                    v___x_4137_ = v_reuseFailAlloc_4138_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_4112_ = v___x_4137_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3___boxed(
    mut v___x_4141_: *mut crate::leanh::LeanObject,
    mut v_as_4142_: *mut crate::leanh::LeanObject,
    mut v_i_4143_: *mut crate::leanh::LeanObject,
    mut v_stop_4144_: *mut crate::leanh::LeanObject,
    mut v_b_4145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9667__boxed_4146_: u8 = 0;
    let mut v_i_boxed_4147_: usize = 0;
    let mut v_stop_boxed_4148_: usize = 0;
    let mut v_res_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9667__boxed_4146_ = (crate::leanh::lean_unbox(v___x_4141_) as u8);
    v_i_boxed_4147_ = crate::leanh::lean_unbox_usize(v_i_4143_);
    crate::leanh::lean_dec(v_i_4143_);
    v_stop_boxed_4148_ = crate::leanh::lean_unbox_usize(v_stop_4144_);
    crate::leanh::lean_dec(v_stop_4144_);
    v_res_4149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(v___x_9667__boxed_4146_, v_as_4142_, v_i_boxed_4147_, v_stop_boxed_4148_, v_b_4145_);
    crate::leanh::lean_dec_ref(v_as_4142_);
    return v_res_4149_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__2;
    v___x_4157_ = l_Lean_stringToMessageData(v___x_4156_);
    return v___x_4157_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6;
    v___x_4165_ = l_Lean_stringToMessageData(v___x_4164_);
    return v___x_4165_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(
    mut v_elabVal_4168_: *mut crate::leanh::LeanObject,
    mut v_as_4169_: *mut crate::leanh::LeanObject,
    mut v_i_4170_: usize,
    mut v_stop_4171_: usize,
    mut v_b_4172_: *mut crate::leanh::LeanObject,
    mut v___y_4173_: *mut crate::leanh::LeanObject,
    mut v___y_4174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: usize = 0;
    let mut v___x_4179_: usize = 0;
    let mut v___y_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: u8 = 0;
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: u8 = 0;
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: u8 = 0;
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: u8 = 0;
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4214_: u8 = 0;
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4218_: u8 = 0;
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4228_: u8 = 0;
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4232_: u8 = 0;
    let mut v___y_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4242_: u8 = 0;
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4246_: u8 = 0;
    let mut v___y_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4249_: usize = 0;
    let mut v___x_4250_: usize = 0;
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tailKey_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: u8 = 0;
    let mut v___x_4264_: u8 = 0;
    let mut v___x_4265_: usize = 0;
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: usize = 0;
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: u8 = 0;
    let mut v___x_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: u8 = 0;
    let mut v___x_4277_: usize = 0;
    let mut v___x_4278_: usize = 0;
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: usize = 0;
    let mut v___x_4282_: usize = 0;
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4184_ = lean_usize_dec_eq(v_i_4170_, v_stop_4171_);
                if v___x_4184_ == 0 {
                    v___x_4185_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1;
                    v___x_4186_ = lean_array_uget_borrowed(v_as_4169_, v_i_4170_);
                    crate::leanh::lean_inc(v___x_4186_);
                    v___x_4187_ = l_Lean_Syntax_isOfKind(v___x_4186_, v___x_4185_);
                    if v___x_4187_ == 0 {
                        crate::leanh::lean_dec_ref(v_b_4172_);
                        v___x_4188_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3);
                        v___x_4189_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_4186_, v___x_4188_, v___y_4173_, v___y_4174_);
                        v___y_4182_ = v___x_4189_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4190_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4191_ = l_Lean_Syntax_getArg(v___x_4186_, v___x_4190_);
                        v___x_4192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5;
                        crate::leanh::lean_inc(v___x_4191_);
                        v___x_4193_ = l_Lean_Syntax_isOfKind(v___x_4191_, v___x_4192_);
                        if v___x_4193_ == 0 {
                            crate::leanh::lean_dec_ref(v_b_4172_);
                            v___x_4194_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7);
                            v___x_4195_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_4191_, v___x_4194_, v___y_4173_, v___y_4174_);
                            crate::leanh::lean_dec(v___x_4191_);
                            v___y_4182_ = v___x_4195_;
                            state = 2;
                            continue;
                        } else {
                            v___x_4196_ = crate::leanh::lean_unsigned_to_nat(2);
                            v___x_4197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0;
                            v_v_4198_ = l_Lean_Syntax_getArg(v___x_4186_, v___x_4196_);
                            v___x_4269_ = l_Lean_Syntax_getArg(v___x_4191_, v___x_4190_);
                            v___x_4270_ = l_Lean_Syntax_getArgs(v___x_4269_);
                            crate::leanh::lean_dec(v___x_4269_);
                            v___x_4271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8;
                            v___x_4272_ = lean_array_get_size(v___x_4270_);
                            v___x_4273_ = lean_nat_dec_lt(v___x_4190_, v___x_4272_);
                            if v___x_4273_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_4270_);
                                v___y_4248_ = v___x_4271_;
                                state = 11;
                                continue;
                            } else {
                                v___x_4274_ = crate::leanh::lean_box((v___x_4193_) as usize);
                                v___x_4275_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4275_, 0, v___x_4274_);
                                crate::leanh::lean_ctor_set(v___x_4275_, 1, v___x_4271_);
                                v___x_4276_ = lean_nat_dec_le(v___x_4272_, v___x_4272_);
                                if v___x_4276_ == 0 {
                                    if v___x_4273_ == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_4275_, 2);
                                        crate::leanh::lean_dec_ref(v___x_4270_);
                                        v___y_4248_ = v___x_4271_;
                                        state = 11;
                                        continue;
                                    } else {
                                        v___x_4277_ = 0usize;
                                        v___x_4278_ = lean_usize_of_nat(v___x_4272_);
                                        v___x_4279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(v___x_4193_, v___x_4270_, v___x_4277_, v___x_4278_, v___x_4275_);
                                        crate::leanh::lean_dec_ref(v___x_4270_);
                                        v_snd_4280_ = crate::leanh::lean_ctor_get(v___x_4279_, 1);
                                        crate::leanh::lean_inc(v_snd_4280_);
                                        crate::leanh::lean_dec_ref(v___x_4279_);
                                        v___y_4248_ = v_snd_4280_;
                                        state = 11;
                                        continue;
                                    }
                                } else {
                                    v___x_4281_ = 0usize;
                                    v___x_4282_ = lean_usize_of_nat(v___x_4272_);
                                    v___x_4283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(v___x_4193_, v___x_4270_, v___x_4281_, v___x_4282_, v___x_4275_);
                                    crate::leanh::lean_dec_ref(v___x_4270_);
                                    v_snd_4284_ = crate::leanh::lean_ctor_get(v___x_4283_, 1);
                                    crate::leanh::lean_inc(v_snd_4284_);
                                    crate::leanh::lean_dec_ref(v___x_4283_);
                                    v___y_4248_ = v_snd_4284_;
                                    state = 11;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_elabVal_4168_);
                    v___x_4285_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4285_, 0, v_b_4172_);
                    return v___x_4285_;
                }
            }
            1 => {
                v___x_4178_ = 1usize;
                v___x_4179_ = lean_usize_add(v_i_4170_, v___x_4178_);
                v_i_4170_ = v___x_4179_;
                v_b_4172_ = v_a_4177_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_4182_) == 0 {
                    v_a_4183_ = crate::leanh::lean_ctor_get(v___y_4182_, 0);
                    crate::leanh::lean_inc(v_a_4183_);
                    crate::leanh::lean_dec_ref_known(v___y_4182_, 1);
                    v_a_4177_ = v_a_4183_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_elabVal_4168_);
                    return v___y_4182_;
                }
            }
            3 => {
                crate::leanh::lean_inc(v___y_4200_);
                v___x_4203_ = l_Lake_Toml_elabSimpleKey(v___y_4200_, v___y_4173_, v___y_4174_);
                if crate::leanh::lean_obj_tag(v___x_4203_) == 0 {
                    v_a_4204_ = crate::leanh::lean_ctor_get(v___x_4203_, 0);
                    crate::leanh::lean_inc(v_a_4204_);
                    crate::leanh::lean_dec_ref_known(v___x_4203_, 1);
                    v___x_4205_ = l_Lean_Name_str___override(v_fst_4201_, v_a_4204_);
                    crate::leanh::lean_inc_ref(v_snd_4202_);
                    crate::leanh::lean_inc(v___x_4205_);
                    v___x_4206_ =
                        l_Lake_Toml_RBDict_contains___redArg(v___x_4197_, v___x_4205_, v_snd_4202_);
                    if v___x_4206_ == 0 {
                        crate::leanh::lean_dec(v___y_4200_);
                        crate::leanh::lean_inc_ref(v_elabVal_4168_);
                        crate::leanh::lean_inc(v___y_4174_);
                        crate::leanh::lean_inc_ref(v___y_4173_);
                        v___x_4207_ = crate::leanh::lean_apply_4(
                            v_elabVal_4168_,
                            v_v_4198_,
                            v___y_4173_,
                            v___y_4174_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_4207_) == 0 {
                            v_a_4208_ = crate::leanh::lean_ctor_get(v___x_4207_, 0);
                            crate::leanh::lean_inc(v_a_4208_);
                            crate::leanh::lean_dec_ref_known(v___x_4207_, 1);
                            v___x_4209_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4209_, 0, v_a_4208_);
                            v___x_4210_ = l_Lake_Toml_RBDict_push___redArg(
                                v___x_4197_,
                                v___x_4205_,
                                v___x_4209_,
                                v_snd_4202_,
                            );
                            v_a_4177_ = v___x_4210_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4205_);
                            crate::leanh::lean_dec_ref(v_snd_4202_);
                            crate::leanh::lean_dec_ref(v_elabVal_4168_);
                            v_a_4211_ = crate::leanh::lean_ctor_get(v___x_4207_, 0);
                            v_isSharedCheck_4218_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4207_)) as u8;
                            if v_isSharedCheck_4218_ == 0 {
                                v___x_4213_ = v___x_4207_;
                                v_isShared_4214_ = v_isSharedCheck_4218_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4211_);
                                crate::leanh::lean_dec(v___x_4207_);
                                v___x_4213_ = crate::leanh::lean_box(0);
                                v_isShared_4214_ = v_isSharedCheck_4218_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_snd_4202_);
                        crate::leanh::lean_dec(v_v_4198_);
                        v___x_4219_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2);
                        v___x_4220_ = l_Lean_MessageData_ofName(v___x_4205_);
                        v___x_4221_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4221_, 0, v___x_4219_);
                        crate::leanh::lean_ctor_set(v___x_4221_, 1, v___x_4220_);
                        v___x_4222_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once), _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
                        v___x_4223_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4223_, 0, v___x_4221_);
                        crate::leanh::lean_ctor_set(v___x_4223_, 1, v___x_4222_);
                        v___x_4224_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___y_4200_, v___x_4223_, v___y_4173_, v___y_4174_);
                        crate::leanh::lean_dec(v___y_4200_);
                        v___y_4182_ = v___x_4224_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_snd_4202_);
                    crate::leanh::lean_dec(v_fst_4201_);
                    crate::leanh::lean_dec(v___y_4200_);
                    crate::leanh::lean_dec(v_v_4198_);
                    crate::leanh::lean_dec_ref(v_elabVal_4168_);
                    v_a_4225_ = crate::leanh::lean_ctor_get(v___x_4203_, 0);
                    v_isSharedCheck_4232_ = (!crate::leanh::lean_is_exclusive(v___x_4203_)) as u8;
                    if v_isSharedCheck_4232_ == 0 {
                        v___x_4227_ = v___x_4203_;
                        v_isShared_4228_ = v_isSharedCheck_4232_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4225_);
                        crate::leanh::lean_dec(v___x_4203_);
                        v___x_4227_ = crate::leanh::lean_box(0);
                        v_isShared_4228_ = v_isSharedCheck_4232_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4214_ == 0 {
                    v___x_4216_ = v___x_4213_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4217_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_a_4211_);
                    v___x_4216_ = v_reuseFailAlloc_4217_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4216_;
            }
            6 => {
                if v_isShared_4228_ == 0 {
                    v___x_4230_ = v___x_4227_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4231_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_a_4225_);
                    v___x_4230_ = v_reuseFailAlloc_4231_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4230_;
            }
            8 => {
                if crate::leanh::lean_obj_tag(v___y_4235_) == 0 {
                    v_a_4236_ = crate::leanh::lean_ctor_get(v___y_4235_, 0);
                    crate::leanh::lean_inc(v_a_4236_);
                    crate::leanh::lean_dec_ref_known(v___y_4235_, 1);
                    v_fst_4237_ = crate::leanh::lean_ctor_get(v_a_4236_, 0);
                    crate::leanh::lean_inc(v_fst_4237_);
                    v_snd_4238_ = crate::leanh::lean_ctor_get(v_a_4236_, 1);
                    crate::leanh::lean_inc(v_snd_4238_);
                    crate::leanh::lean_dec(v_a_4236_);
                    v___y_4200_ = v___y_4234_;
                    v_fst_4201_ = v_fst_4237_;
                    v_snd_4202_ = v_snd_4238_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_4234_);
                    crate::leanh::lean_dec(v_v_4198_);
                    crate::leanh::lean_dec_ref(v_elabVal_4168_);
                    v_a_4239_ = crate::leanh::lean_ctor_get(v___y_4235_, 0);
                    v_isSharedCheck_4246_ = (!crate::leanh::lean_is_exclusive(v___y_4235_)) as u8;
                    if v_isSharedCheck_4246_ == 0 {
                        v___x_4241_ = v___y_4235_;
                        v_isShared_4242_ = v_isSharedCheck_4246_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4239_);
                        crate::leanh::lean_dec(v___y_4235_);
                        v___x_4241_ = crate::leanh::lean_box(0);
                        v_isShared_4242_ = v_isSharedCheck_4246_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_4242_ == 0 {
                    v___x_4244_ = v___x_4241_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4245_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_a_4239_);
                    v___x_4244_ = v_reuseFailAlloc_4245_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4244_;
            }
            11 => {
                v_sz_4249_ = lean_array_size(v___y_4248_);
                v___x_4250_ = 0usize;
                v___x_4251_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(v_sz_4249_, v___x_4250_, v___y_4248_);
                if crate::leanh::lean_obj_tag(v___x_4251_) == 0 {
                    crate::leanh::lean_dec(v_v_4198_);
                    crate::leanh::lean_dec_ref(v_b_4172_);
                    v___x_4252_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7);
                    v___x_4253_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_4191_, v___x_4252_, v___y_4173_, v___y_4174_);
                    crate::leanh::lean_dec(v___x_4191_);
                    v___y_4182_ = v___x_4253_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_4191_);
                    v_val_4254_ = crate::leanh::lean_ctor_get(v___x_4251_, 0);
                    crate::leanh::lean_inc(v_val_4254_);
                    crate::leanh::lean_dec_ref_known(v___x_4251_, 1);
                    v___x_4255_ = crate::leanh::lean_box(0);
                    v___x_4256_ = lean_array_get_size(v_val_4254_);
                    v___x_4257_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4258_ = lean_nat_sub(v___x_4256_, v___x_4257_);
                    v_tailKey_4259_ = lean_array_get(v___x_4255_, v_val_4254_, v___x_4258_);
                    crate::leanh::lean_dec(v___x_4258_);
                    v___x_4260_ = crate::leanh::lean_box(0);
                    v___x_4261_ = lean_array_pop(v_val_4254_);
                    v___x_4262_ = lean_array_get_size(v___x_4261_);
                    v___x_4263_ = lean_nat_dec_lt(v___x_4190_, v___x_4262_);
                    if v___x_4263_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_4261_);
                        v___y_4200_ = v_tailKey_4259_;
                        v_fst_4201_ = v___x_4260_;
                        v_snd_4202_ = v_b_4172_;
                        state = 3;
                        continue;
                    } else {
                        v___x_4264_ = lean_nat_dec_le(v___x_4262_, v___x_4262_);
                        if v___x_4264_ == 0 {
                            if v___x_4263_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_4261_);
                                v___y_4200_ = v_tailKey_4259_;
                                v_fst_4201_ = v___x_4260_;
                                v_snd_4202_ = v_b_4172_;
                                state = 3;
                                continue;
                            } else {
                                v___x_4265_ = lean_usize_of_nat(v___x_4262_);
                                crate::leanh::lean_inc_ref(v_b_4172_);
                                v___x_4266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_b_4172_, v___x_4193_, v___x_4261_, v___x_4250_, v___x_4265_, v___x_4260_, v_b_4172_, v___y_4173_, v___y_4174_);
                                crate::leanh::lean_dec_ref(v___x_4261_);
                                v___y_4234_ = v_tailKey_4259_;
                                v___y_4235_ = v___x_4266_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v___x_4267_ = lean_usize_of_nat(v___x_4262_);
                            crate::leanh::lean_inc_ref(v_b_4172_);
                            v___x_4268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_b_4172_, v___x_4193_, v___x_4261_, v___x_4250_, v___x_4267_, v___x_4260_, v_b_4172_, v___y_4173_, v___y_4174_);
                            crate::leanh::lean_dec_ref(v___x_4261_);
                            v___y_4234_ = v_tailKey_4259_;
                            v___y_4235_ = v___x_4268_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___boxed(
    mut v_elabVal_4286_: *mut crate::leanh::LeanObject,
    mut v_as_4287_: *mut crate::leanh::LeanObject,
    mut v_i_4288_: *mut crate::leanh::LeanObject,
    mut v_stop_4289_: *mut crate::leanh::LeanObject,
    mut v_b_4290_: *mut crate::leanh::LeanObject,
    mut v___y_4291_: *mut crate::leanh::LeanObject,
    mut v___y_4292_: *mut crate::leanh::LeanObject,
    mut v___y_4293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4294_: usize = 0;
    let mut v_stop_boxed_4295_: usize = 0;
    let mut v_res_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4294_ = crate::leanh::lean_unbox_usize(v_i_4288_);
    crate::leanh::lean_dec(v_i_4288_);
    v_stop_boxed_4295_ = crate::leanh::lean_unbox_usize(v_stop_4289_);
    crate::leanh::lean_dec(v_stop_4289_);
    v_res_4296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_4286_, v_as_4287_, v_i_boxed_4294_, v_stop_boxed_4295_, v_b_4290_, v___y_4291_, v___y_4292_);
    crate::leanh::lean_dec(v___y_4292_);
    crate::leanh::lean_dec_ref(v___y_4291_);
    crate::leanh::lean_dec_ref(v_as_4287_);
    return v_res_4296_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(
    mut v_as_4297_: *mut crate::leanh::LeanObject,
    mut v_i_4298_: usize,
    mut v_stop_4299_: usize,
    mut v_b_4300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: usize = 0;
    let mut v___x_4304_: usize = 0;
    let mut v___x_4306_: u8 = 0;
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4306_ = lean_usize_dec_eq(v_i_4298_, v_stop_4299_);
                if v___x_4306_ == 0 {
                    v___x_4307_ = lean_array_uget_borrowed(v_as_4297_, v_i_4298_);
                    v_snd_4308_ = crate::leanh::lean_ctor_get(v___x_4307_, 1);
                    if crate::leanh::lean_obj_tag(v_snd_4308_) == 1 {
                        v_fst_4309_ = crate::leanh::lean_ctor_get(v___x_4307_, 0);
                        v_val_4310_ = crate::leanh::lean_ctor_get(v_snd_4308_, 0);
                        v___x_4311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0;
                        crate::leanh::lean_inc(v_val_4310_);
                        crate::leanh::lean_inc(v_fst_4309_);
                        v___x_4312_ = l_Lake_Toml_RBDict_push___redArg(
                            v___x_4311_,
                            v_fst_4309_,
                            v_val_4310_,
                            v_b_4300_,
                        );
                        v___y_4302_ = v___x_4312_;
                        state = 1;
                        continue;
                    } else {
                        v___y_4302_ = v_b_4300_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_4300_;
                }
            }
            1 => {
                v___x_4303_ = 1usize;
                v___x_4304_ = lean_usize_add(v_i_4298_, v___x_4303_);
                v_i_4298_ = v___x_4304_;
                v_b_4300_ = v___y_4302_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4___boxed(
    mut v_as_4313_: *mut crate::leanh::LeanObject,
    mut v_i_4314_: *mut crate::leanh::LeanObject,
    mut v_stop_4315_: *mut crate::leanh::LeanObject,
    mut v_b_4316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4317_: usize = 0;
    let mut v_stop_boxed_4318_: usize = 0;
    let mut v_res_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4317_ = crate::leanh::lean_unbox_usize(v_i_4314_);
    crate::leanh::lean_dec(v_i_4314_);
    v_stop_boxed_4318_ = crate::leanh::lean_unbox_usize(v_stop_4315_);
    crate::leanh::lean_dec(v_stop_4315_);
    v_res_4319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(v_as_4313_, v_i_boxed_4317_, v_stop_boxed_4318_, v_b_4316_);
    crate::leanh::lean_dec_ref(v_as_4313_);
    return v_res_4319_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4326_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__2;
    v___x_4327_ = l_Lean_stringToMessageData(v___x_4326_);
    return v___x_4327_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0;
    v___x_4329_ = l_Lake_Toml_RBDict_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4328_,
    );
    return v___x_4329_;
}
pub unsafe fn _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0;
    v_t_4331_ = l_Lake_Toml_RBDict_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4330_,
    );
    return v_t_4331_;
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(
    mut v_x_4332_: *mut crate::leanh::LeanObject,
    mut v_elabVal_4333_: *mut crate::leanh::LeanObject,
    mut v_a_4334_: *mut crate::leanh::LeanObject,
    mut v_a_4335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: u8 = 0;
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kvs_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: u8 = 0;
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: u8 = 0;
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: usize = 0;
    let mut v___x_4355_: usize = 0;
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: usize = 0;
    let mut v___x_4359_: usize = 0;
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4368_: u8 = 0;
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4372_: u8 = 0;
    let mut v_t_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: u8 = 0;
    let mut v___x_4377_: u8 = 0;
    let mut v___x_4378_: usize = 0;
    let mut v___x_4379_: usize = 0;
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: usize = 0;
    let mut v___x_4382_: usize = 0;
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4337_ =
                    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1;
                crate::leanh::lean_inc(v_x_4332_);
                v___x_4338_ = l_Lean_Syntax_isOfKind(v_x_4332_, v___x_4337_);
                if v___x_4338_ == 0 {
                    crate::leanh::lean_dec_ref(v_elabVal_4333_);
                    v___x_4339_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3_once), _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3);
                    v___x_4340_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_4332_, v___x_4339_, v_a_4334_, v_a_4335_);
                    crate::leanh::lean_dec(v_x_4332_);
                    return v___x_4340_;
                } else {
                    v___x_4341_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4342_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4343_ = l_Lean_Syntax_getArg(v_x_4332_, v___x_4342_);
                    crate::leanh::lean_dec(v_x_4332_);
                    v_kvs_4344_ = l_Lean_Syntax_getArgs(v___x_4343_);
                    crate::leanh::lean_dec(v___x_4343_);
                    v_t_4373_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5_once), _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5);
                    v___x_4374_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_kvs_4344_);
                    crate::leanh::lean_dec_ref(v_kvs_4344_);
                    v___x_4375_ = lean_array_get_size(v___x_4374_);
                    v___x_4376_ = lean_nat_dec_lt(v___x_4341_, v___x_4375_);
                    if v___x_4376_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_4374_);
                        crate::leanh::lean_dec_ref(v_elabVal_4333_);
                        v_a_4346_ = v_t_4373_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4377_ = lean_nat_dec_le(v___x_4375_, v___x_4375_);
                        if v___x_4377_ == 0 {
                            if v___x_4376_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_4374_);
                                crate::leanh::lean_dec_ref(v_elabVal_4333_);
                                v_a_4346_ = v_t_4373_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4378_ = 0usize;
                                v___x_4379_ = lean_usize_of_nat(v___x_4375_);
                                v___x_4380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_4333_, v___x_4374_, v___x_4378_, v___x_4379_, v_t_4373_, v_a_4334_, v_a_4335_);
                                crate::leanh::lean_dec_ref(v___x_4374_);
                                v___y_4363_ = v___x_4380_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_4381_ = 0usize;
                            v___x_4382_ = lean_usize_of_nat(v___x_4375_);
                            v___x_4383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_4333_, v___x_4374_, v___x_4381_, v___x_4382_, v_t_4373_, v_a_4334_, v_a_4335_);
                            crate::leanh::lean_dec_ref(v___x_4374_);
                            v___y_4363_ = v___x_4383_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_items_4347_ = crate::leanh::lean_ctor_get(v_a_4346_, 0);
                crate::leanh::lean_inc_ref(v_items_4347_);
                crate::leanh::lean_dec_ref(v_a_4346_);
                v___x_4348_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4_once), _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4);
                v___x_4349_ = lean_array_get_size(v_items_4347_);
                v___x_4350_ = lean_nat_dec_lt(v___x_4341_, v___x_4349_);
                if v___x_4350_ == 0 {
                    crate::leanh::lean_dec_ref(v_items_4347_);
                    v___x_4351_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4351_, 0, v___x_4348_);
                    return v___x_4351_;
                } else {
                    v___x_4352_ = lean_nat_dec_le(v___x_4349_, v___x_4349_);
                    if v___x_4352_ == 0 {
                        if v___x_4350_ == 0 {
                            crate::leanh::lean_dec_ref(v_items_4347_);
                            v___x_4353_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4353_, 0, v___x_4348_);
                            return v___x_4353_;
                        } else {
                            v___x_4354_ = 0usize;
                            v___x_4355_ = lean_usize_of_nat(v___x_4349_);
                            v___x_4356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(v_items_4347_, v___x_4354_, v___x_4355_, v___x_4348_);
                            crate::leanh::lean_dec_ref(v_items_4347_);
                            v___x_4357_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4357_, 0, v___x_4356_);
                            return v___x_4357_;
                        }
                    } else {
                        v___x_4358_ = 0usize;
                        v___x_4359_ = lean_usize_of_nat(v___x_4349_);
                        v___x_4360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(v_items_4347_, v___x_4358_, v___x_4359_, v___x_4348_);
                        crate::leanh::lean_dec_ref(v_items_4347_);
                        v___x_4361_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4361_, 0, v___x_4360_);
                        return v___x_4361_;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_4363_) == 0 {
                    v_a_4364_ = crate::leanh::lean_ctor_get(v___y_4363_, 0);
                    crate::leanh::lean_inc(v_a_4364_);
                    crate::leanh::lean_dec_ref_known(v___y_4363_, 1);
                    v_a_4346_ = v_a_4364_;
                    state = 1;
                    continue;
                } else {
                    v_a_4365_ = crate::leanh::lean_ctor_get(v___y_4363_, 0);
                    v_isSharedCheck_4372_ = (!crate::leanh::lean_is_exclusive(v___y_4363_)) as u8;
                    if v_isSharedCheck_4372_ == 0 {
                        v___x_4367_ = v___y_4363_;
                        v_isShared_4368_ = v_isSharedCheck_4372_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4365_);
                        crate::leanh::lean_dec(v___y_4363_);
                        v___x_4367_ = crate::leanh::lean_box(0);
                        v_isShared_4368_ = v_isSharedCheck_4372_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4368_ == 0 {
                    v___x_4370_ = v___x_4367_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4371_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_a_4365_);
                    v___x_4370_ = v_reuseFailAlloc_4371_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4370_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___boxed(
    mut v_x_4384_: *mut crate::leanh::LeanObject,
    mut v_elabVal_4385_: *mut crate::leanh::LeanObject,
    mut v_a_4386_: *mut crate::leanh::LeanObject,
    mut v_a_4387_: *mut crate::leanh::LeanObject,
    mut v_a_4388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4389_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(
        v_x_4384_,
        v_elabVal_4385_,
        v_a_4386_,
        v_a_4387_,
    );
    crate::leanh::lean_dec(v_a_4387_);
    crate::leanh::lean_dec_ref(v_a_4386_);
    return v_res_4389_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(
    mut v_00_u03b1_4390_: *mut crate::leanh::LeanObject,
    mut v_ref_4391_: *mut crate::leanh::LeanObject,
    mut v_msg_4392_: *mut crate::leanh::LeanObject,
    mut v___y_4393_: *mut crate::leanh::LeanObject,
    mut v___y_4394_: *mut crate::leanh::LeanObject,
    mut v___y_4395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4397_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg(v_ref_4391_, v_msg_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
    return v___x_4397_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___boxed(
    mut v_00_u03b1_4398_: *mut crate::leanh::LeanObject,
    mut v_ref_4399_: *mut crate::leanh::LeanObject,
    mut v_msg_4400_: *mut crate::leanh::LeanObject,
    mut v___y_4401_: *mut crate::leanh::LeanObject,
    mut v___y_4402_: *mut crate::leanh::LeanObject,
    mut v___y_4403_: *mut crate::leanh::LeanObject,
    mut v___y_4404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4405_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(v_00_u03b1_4398_, v_ref_4399_, v_msg_4400_, v___y_4401_, v___y_4402_, v___y_4403_);
    crate::leanh::lean_dec(v___y_4403_);
    crate::leanh::lean_dec_ref(v___y_4402_);
    crate::leanh::lean_dec_ref(v___y_4401_);
    crate::leanh::lean_dec(v_ref_4399_);
    return v_res_4405_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1(
    mut v_00_u03b1_4406_: *mut crate::leanh::LeanObject,
    mut v_msg_4407_: *mut crate::leanh::LeanObject,
    mut v___y_4408_: *mut crate::leanh::LeanObject,
    mut v___y_4409_: *mut crate::leanh::LeanObject,
    mut v___y_4410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4412_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg(v_msg_4407_, v___y_4409_, v___y_4410_);
    return v___x_4412_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___boxed(
    mut v_00_u03b1_4413_: *mut crate::leanh::LeanObject,
    mut v_msg_4414_: *mut crate::leanh::LeanObject,
    mut v___y_4415_: *mut crate::leanh::LeanObject,
    mut v___y_4416_: *mut crate::leanh::LeanObject,
    mut v___y_4417_: *mut crate::leanh::LeanObject,
    mut v___y_4418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4419_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1(v_00_u03b1_4413_, v_msg_4414_, v___y_4415_, v___y_4416_, v___y_4417_);
    crate::leanh::lean_dec(v___y_4417_);
    crate::leanh::lean_dec_ref(v___y_4416_);
    crate::leanh::lean_dec_ref(v___y_4415_);
    return v_res_4419_;
}
pub unsafe fn _init_l_Lake_Toml_elabVal___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4421_ = l_Lake_Toml_elabVal___closed__0;
    v___x_4422_ = l_Lean_stringToMessageData(v___x_4421_);
    return v___x_4422_;
}
pub unsafe fn l_Lake_Toml_elabVal___boxed(
    mut v_x_4423_: *mut crate::leanh::LeanObject,
    mut v_a_4424_: *mut crate::leanh::LeanObject,
    mut v_a_4425_: *mut crate::leanh::LeanObject,
    mut v_a_4426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4427_ = l_Lake_Toml_elabVal(v_x_4423_, v_a_4424_, v_a_4425_);
    crate::leanh::lean_dec(v_a_4425_);
    crate::leanh::lean_dec_ref(v_a_4424_);
    return v_res_4427_;
}
pub unsafe fn l_Lake_Toml_elabVal(
    mut v_x_4428_: *mut crate::leanh::LeanObject,
    mut v_a_4429_: *mut crate::leanh::LeanObject,
    mut v_a_4430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: u8 = 0;
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: u8 = 0;
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: u8 = 0;
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: u8 = 0;
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: u8 = 0;
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: u8 = 0;
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: u8 = 0;
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: u8 = 0;
    let mut v___x_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: u8 = 0;
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: u8 = 0;
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4459_: u8 = 0;
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4464_: u8 = 0;
    let mut v_a_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4468_: u8 = 0;
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4472_: u8 = 0;
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4478_: u8 = 0;
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4483_: u8 = 0;
    let mut v_a_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4487_: u8 = 0;
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4491_: u8 = 0;
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4496_: u8 = 0;
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: u8 = 0;
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4502_: u8 = 0;
    let mut v_a_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4506_: u8 = 0;
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4510_: u8 = 0;
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4515_: u8 = 0;
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4520_: u8 = 0;
    let mut v_a_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4524_: u8 = 0;
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4528_: u8 = 0;
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4533_: u8 = 0;
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4538_: u8 = 0;
    let mut v_a_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4542_: u8 = 0;
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4546_: u8 = 0;
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4551_: u8 = 0;
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4557_: u8 = 0;
    let mut v_a_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4561_: u8 = 0;
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4565_: u8 = 0;
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4570_: u8 = 0;
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4576_: u8 = 0;
    let mut v_a_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4580_: u8 = 0;
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4584_: u8 = 0;
    let mut v___x_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4589_: u8 = 0;
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4595_: u8 = 0;
    let mut v_a_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4599_: u8 = 0;
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4603_: u8 = 0;
    let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4608_: u8 = 0;
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4613_: u8 = 0;
    let mut v_a_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4617_: u8 = 0;
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4621_: u8 = 0;
    let mut v___x_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4626_: u8 = 0;
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: f64 = 0.0;
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4632_: u8 = 0;
    let mut v_a_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4636_: u8 = 0;
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4640_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4432_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1;
                crate::leanh::lean_inc(v_x_4428_);
                v___x_4433_ = l_Lean_Syntax_isOfKind(v_x_4428_, v___x_4432_);
                if v___x_4433_ == 0 {
                    v___x_4434_ =
                        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1;
                    crate::leanh::lean_inc(v_x_4428_);
                    v___x_4435_ = l_Lean_Syntax_isOfKind(v_x_4428_, v___x_4434_);
                    if v___x_4435_ == 0 {
                        v___x_4436_ =
                            l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1;
                        crate::leanh::lean_inc(v_x_4428_);
                        v___x_4437_ = l_Lean_Syntax_isOfKind(v_x_4428_, v___x_4436_);
                        if v___x_4437_ == 0 {
                            v___x_4438_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1;
                            crate::leanh::lean_inc(v_x_4428_);
                            v___x_4439_ = l_Lean_Syntax_isOfKind(v_x_4428_, v___x_4438_);
                            if v___x_4439_ == 0 {
                                v___x_4440_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1;
                                crate::leanh::lean_inc(v_x_4428_);
                                v___x_4441_ = l_Lean_Syntax_isOfKind(v_x_4428_, v___x_4440_);
                                if v___x_4441_ == 0 {
                                    v___x_4442_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3;
                                    crate::leanh::lean_inc(v_x_4428_);
                                    v___x_4443_ = l_Lean_Syntax_isOfKind(v_x_4428_, v___x_4442_);
                                    if v___x_4443_ == 0 {
                                        v___x_4444_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1;
                                        crate::leanh::lean_inc(v_x_4428_);
                                        v___x_4445_ =
                                            l_Lean_Syntax_isOfKind(v_x_4428_, v___x_4444_);
                                        if v___x_4445_ == 0 {
                                            v___x_4446_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3;
                                            crate::leanh::lean_inc(v_x_4428_);
                                            v___x_4447_ =
                                                l_Lean_Syntax_isOfKind(v_x_4428_, v___x_4446_);
                                            if v___x_4447_ == 0 {
                                                v___x_4448_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1;
                                                crate::leanh::lean_inc(v_x_4428_);
                                                v___x_4449_ =
                                                    l_Lean_Syntax_isOfKind(v_x_4428_, v___x_4448_);
                                                if v___x_4449_ == 0 {
                                                    v___x_4450_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1;
                                                    crate::leanh::lean_inc(v_x_4428_);
                                                    v___x_4451_ = l_Lean_Syntax_isOfKind(
                                                        v_x_4428_,
                                                        v___x_4450_,
                                                    );
                                                    if v___x_4451_ == 0 {
                                                        v___x_4452_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_Toml_elabVal___closed__1), core::ptr::addr_of_mut!(l_Lake_Toml_elabVal___closed__1_once), _init_l_Lake_Toml_elabVal___closed__1);
                                                        v___x_4453_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_4428_, v___x_4452_, v_a_4429_, v_a_4430_);
                                                        crate::leanh::lean_dec(v_x_4428_);
                                                        return v___x_4453_;
                                                    } else {
                                                        v___x_4454_ =
                                                            crate::leanh::lean_alloc_closure(
                                                                l_Lake_Toml_elabVal___boxed
                                                                    as *mut core::ffi::c_void,
                                                                4,
                                                                0,
                                                            );
                                                        crate::leanh::lean_inc(v_x_4428_);
                                                        v___x_4455_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(v_x_4428_, v___x_4454_, v_a_4429_, v_a_4430_);
                                                        if crate::leanh::lean_obj_tag(v___x_4455_)
                                                            == 0
                                                        {
                                                            v_a_4456_ = crate::leanh::lean_ctor_get(
                                                                v___x_4455_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_4464_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_4455_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_4464_ == 0 {
                                                                v___x_4458_ = v___x_4455_;
                                                                v_isShared_4459_ =
                                                                    v_isSharedCheck_4464_;
                                                                state = 1;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_4456_);
                                                                crate::leanh::lean_dec(v___x_4455_);
                                                                v___x_4458_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_4459_ =
                                                                    v_isSharedCheck_4464_;
                                                                state = 1;
                                                                continue;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec(v_x_4428_);
                                                            v_a_4465_ = crate::leanh::lean_ctor_get(
                                                                v___x_4455_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_4472_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_4455_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_4472_ == 0 {
                                                                v___x_4467_ = v___x_4455_;
                                                                v_isShared_4468_ =
                                                                    v_isSharedCheck_4472_;
                                                                state = 3;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_4465_);
                                                                crate::leanh::lean_dec(v___x_4455_);
                                                                v___x_4467_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_4468_ =
                                                                    v_isSharedCheck_4472_;
                                                                state = 3;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    v___x_4473_ = crate::leanh::lean_alloc_closure(
                                                        l_Lake_Toml_elabVal___boxed
                                                            as *mut core::ffi::c_void,
                                                        4,
                                                        0,
                                                    );
                                                    crate::leanh::lean_inc(v_x_4428_);
                                                    v___x_4474_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(v_x_4428_, v___x_4473_, v_a_4429_, v_a_4430_);
                                                    if crate::leanh::lean_obj_tag(v___x_4474_) == 0
                                                    {
                                                        v_a_4475_ = crate::leanh::lean_ctor_get(
                                                            v___x_4474_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_4483_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_4474_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_4483_ == 0 {
                                                            v___x_4477_ = v___x_4474_;
                                                            v_isShared_4478_ =
                                                                v_isSharedCheck_4483_;
                                                            state = 5;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_4475_);
                                                            crate::leanh::lean_dec(v___x_4474_);
                                                            v___x_4477_ = crate::leanh::lean_box(0);
                                                            v_isShared_4478_ =
                                                                v_isSharedCheck_4483_;
                                                            state = 5;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec(v_x_4428_);
                                                        v_a_4484_ = crate::leanh::lean_ctor_get(
                                                            v___x_4474_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_4491_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_4474_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_4491_ == 0 {
                                                            v___x_4486_ = v___x_4474_;
                                                            v_isShared_4487_ =
                                                                v_isSharedCheck_4491_;
                                                            state = 7;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_4484_);
                                                            crate::leanh::lean_dec(v___x_4474_);
                                                            v___x_4486_ = crate::leanh::lean_box(0);
                                                            v_isShared_4487_ =
                                                                v_isSharedCheck_4491_;
                                                            state = 7;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_inc(v_x_4428_);
                                                v___x_4492_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(v_x_4428_, v_a_4429_, v_a_4430_);
                                                if crate::leanh::lean_obj_tag(v___x_4492_) == 0 {
                                                    v_a_4493_ =
                                                        crate::leanh::lean_ctor_get(v___x_4492_, 0);
                                                    v_isSharedCheck_4502_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_4492_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_4502_ == 0 {
                                                        v___x_4495_ = v___x_4492_;
                                                        v_isShared_4496_ = v_isSharedCheck_4502_;
                                                        state = 9;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_4493_);
                                                        crate::leanh::lean_dec(v___x_4492_);
                                                        v___x_4495_ = crate::leanh::lean_box(0);
                                                        v_isShared_4496_ = v_isSharedCheck_4502_;
                                                        state = 9;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_x_4428_);
                                                    v_a_4503_ =
                                                        crate::leanh::lean_ctor_get(v___x_4492_, 0);
                                                    v_isSharedCheck_4510_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_4492_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_4510_ == 0 {
                                                        v___x_4505_ = v___x_4492_;
                                                        v_isShared_4506_ = v_isSharedCheck_4510_;
                                                        state = 11;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_4503_);
                                                        crate::leanh::lean_dec(v___x_4492_);
                                                        v___x_4505_ = crate::leanh::lean_box(0);
                                                        v_isShared_4506_ = v_isSharedCheck_4510_;
                                                        state = 11;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_inc(v_x_4428_);
                                            v___x_4511_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(v_x_4428_, v_a_4429_, v_a_4430_);
                                            if crate::leanh::lean_obj_tag(v___x_4511_) == 0 {
                                                v_a_4512_ =
                                                    crate::leanh::lean_ctor_get(v___x_4511_, 0);
                                                v_isSharedCheck_4520_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_4511_))
                                                        as u8;
                                                if v_isSharedCheck_4520_ == 0 {
                                                    v___x_4514_ = v___x_4511_;
                                                    v_isShared_4515_ = v_isSharedCheck_4520_;
                                                    state = 13;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_4512_);
                                                    crate::leanh::lean_dec(v___x_4511_);
                                                    v___x_4514_ = crate::leanh::lean_box(0);
                                                    v_isShared_4515_ = v_isSharedCheck_4520_;
                                                    state = 13;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_x_4428_);
                                                v_a_4521_ =
                                                    crate::leanh::lean_ctor_get(v___x_4511_, 0);
                                                v_isSharedCheck_4528_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_4511_))
                                                        as u8;
                                                if v_isSharedCheck_4528_ == 0 {
                                                    v___x_4523_ = v___x_4511_;
                                                    v_isShared_4524_ = v_isSharedCheck_4528_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_4521_);
                                                    crate::leanh::lean_dec(v___x_4511_);
                                                    v___x_4523_ = crate::leanh::lean_box(0);
                                                    v_isShared_4524_ = v_isSharedCheck_4528_;
                                                    state = 15;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        v___x_4529_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(v_x_4428_, v_a_4429_, v_a_4430_);
                                        if crate::leanh::lean_obj_tag(v___x_4529_) == 0 {
                                            v_a_4530_ = crate::leanh::lean_ctor_get(v___x_4529_, 0);
                                            v_isSharedCheck_4538_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_4529_))
                                                    as u8;
                                            if v_isSharedCheck_4538_ == 0 {
                                                v___x_4532_ = v___x_4529_;
                                                v_isShared_4533_ = v_isSharedCheck_4538_;
                                                state = 17;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_4530_);
                                                crate::leanh::lean_dec(v___x_4529_);
                                                v___x_4532_ = crate::leanh::lean_box(0);
                                                v_isShared_4533_ = v_isSharedCheck_4538_;
                                                state = 17;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_x_4428_);
                                            v_a_4539_ = crate::leanh::lean_ctor_get(v___x_4529_, 0);
                                            v_isSharedCheck_4546_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_4529_))
                                                    as u8;
                                            if v_isSharedCheck_4546_ == 0 {
                                                v___x_4541_ = v___x_4529_;
                                                v_isShared_4542_ = v_isSharedCheck_4546_;
                                                state = 19;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_4539_);
                                                crate::leanh::lean_dec(v___x_4529_);
                                                v___x_4541_ = crate::leanh::lean_box(0);
                                                v_isShared_4542_ = v_isSharedCheck_4546_;
                                                state = 19;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    v___x_4547_ =
                                        l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(
                                            v_x_4428_, v_a_4429_, v_a_4430_,
                                        );
                                    if crate::leanh::lean_obj_tag(v___x_4547_) == 0 {
                                        v_a_4548_ = crate::leanh::lean_ctor_get(v___x_4547_, 0);
                                        v_isSharedCheck_4557_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4547_)) as u8;
                                        if v_isSharedCheck_4557_ == 0 {
                                            v___x_4550_ = v___x_4547_;
                                            v_isShared_4551_ = v_isSharedCheck_4557_;
                                            state = 21;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4548_);
                                            crate::leanh::lean_dec(v___x_4547_);
                                            v___x_4550_ = crate::leanh::lean_box(0);
                                            v_isShared_4551_ = v_isSharedCheck_4557_;
                                            state = 21;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_x_4428_);
                                        v_a_4558_ = crate::leanh::lean_ctor_get(v___x_4547_, 0);
                                        v_isSharedCheck_4565_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4547_)) as u8;
                                        if v_isSharedCheck_4565_ == 0 {
                                            v___x_4560_ = v___x_4547_;
                                            v_isShared_4561_ = v_isSharedCheck_4565_;
                                            state = 23;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4558_);
                                            crate::leanh::lean_dec(v___x_4547_);
                                            v___x_4560_ = crate::leanh::lean_box(0);
                                            v_isShared_4561_ = v_isSharedCheck_4565_;
                                            state = 23;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_4566_ =
                                    l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(
                                        v_x_4428_, v_a_4429_, v_a_4430_,
                                    );
                                if crate::leanh::lean_obj_tag(v___x_4566_) == 0 {
                                    v_a_4567_ = crate::leanh::lean_ctor_get(v___x_4566_, 0);
                                    v_isSharedCheck_4576_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4566_)) as u8;
                                    if v_isSharedCheck_4576_ == 0 {
                                        v___x_4569_ = v___x_4566_;
                                        v_isShared_4570_ = v_isSharedCheck_4576_;
                                        state = 25;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4567_);
                                        crate::leanh::lean_dec(v___x_4566_);
                                        v___x_4569_ = crate::leanh::lean_box(0);
                                        v_isShared_4570_ = v_isSharedCheck_4576_;
                                        state = 25;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_x_4428_);
                                    v_a_4577_ = crate::leanh::lean_ctor_get(v___x_4566_, 0);
                                    v_isSharedCheck_4584_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4566_)) as u8;
                                    if v_isSharedCheck_4584_ == 0 {
                                        v___x_4579_ = v___x_4566_;
                                        v_isShared_4580_ = v_isSharedCheck_4584_;
                                        state = 27;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4577_);
                                        crate::leanh::lean_dec(v___x_4566_);
                                        v___x_4579_ = crate::leanh::lean_box(0);
                                        v_isShared_4580_ = v_isSharedCheck_4584_;
                                        state = 27;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v___x_4585_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(
                                v_x_4428_, v_a_4429_, v_a_4430_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4585_) == 0 {
                                v_a_4586_ = crate::leanh::lean_ctor_get(v___x_4585_, 0);
                                v_isSharedCheck_4595_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4585_)) as u8;
                                if v_isSharedCheck_4595_ == 0 {
                                    v___x_4588_ = v___x_4585_;
                                    v_isShared_4589_ = v_isSharedCheck_4595_;
                                    state = 29;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4586_);
                                    crate::leanh::lean_dec(v___x_4585_);
                                    v___x_4588_ = crate::leanh::lean_box(0);
                                    v_isShared_4589_ = v_isSharedCheck_4595_;
                                    state = 29;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_x_4428_);
                                v_a_4596_ = crate::leanh::lean_ctor_get(v___x_4585_, 0);
                                v_isSharedCheck_4603_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4585_)) as u8;
                                if v_isSharedCheck_4603_ == 0 {
                                    v___x_4598_ = v___x_4585_;
                                    v_isShared_4599_ = v_isSharedCheck_4603_;
                                    state = 31;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4596_);
                                    crate::leanh::lean_dec(v___x_4585_);
                                    v___x_4598_ = crate::leanh::lean_box(0);
                                    v_isShared_4599_ = v_isSharedCheck_4603_;
                                    state = 31;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_4604_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(
                            v_x_4428_, v_a_4429_, v_a_4430_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4604_) == 0 {
                            v_a_4605_ = crate::leanh::lean_ctor_get(v___x_4604_, 0);
                            v_isSharedCheck_4613_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4604_)) as u8;
                            if v_isSharedCheck_4613_ == 0 {
                                v___x_4607_ = v___x_4604_;
                                v_isShared_4608_ = v_isSharedCheck_4613_;
                                state = 33;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4605_);
                                crate::leanh::lean_dec(v___x_4604_);
                                v___x_4607_ = crate::leanh::lean_box(0);
                                v_isShared_4608_ = v_isSharedCheck_4613_;
                                state = 33;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_x_4428_);
                            v_a_4614_ = crate::leanh::lean_ctor_get(v___x_4604_, 0);
                            v_isSharedCheck_4621_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4604_)) as u8;
                            if v_isSharedCheck_4621_ == 0 {
                                v___x_4616_ = v___x_4604_;
                                v_isShared_4617_ = v_isSharedCheck_4621_;
                                state = 35;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4614_);
                                crate::leanh::lean_dec(v___x_4604_);
                                v___x_4616_ = crate::leanh::lean_box(0);
                                v_isShared_4617_ = v_isSharedCheck_4621_;
                                state = 35;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_4622_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(
                        v_x_4428_, v_a_4429_, v_a_4430_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4622_) == 0 {
                        v_a_4623_ = crate::leanh::lean_ctor_get(v___x_4622_, 0);
                        v_isSharedCheck_4632_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4622_)) as u8;
                        if v_isSharedCheck_4632_ == 0 {
                            v___x_4625_ = v___x_4622_;
                            v_isShared_4626_ = v_isSharedCheck_4632_;
                            state = 37;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4623_);
                            crate::leanh::lean_dec(v___x_4622_);
                            v___x_4625_ = crate::leanh::lean_box(0);
                            v_isShared_4626_ = v_isSharedCheck_4632_;
                            state = 37;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_x_4428_);
                        v_a_4633_ = crate::leanh::lean_ctor_get(v___x_4622_, 0);
                        v_isSharedCheck_4640_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4622_)) as u8;
                        if v_isSharedCheck_4640_ == 0 {
                            v___x_4635_ = v___x_4622_;
                            v_isShared_4636_ = v_isSharedCheck_4640_;
                            state = 39;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4633_);
                            crate::leanh::lean_dec(v___x_4622_);
                            v___x_4635_ = crate::leanh::lean_box(0);
                            v_isShared_4636_ = v_isSharedCheck_4640_;
                            state = 39;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4460_ = crate::leanh::lean_alloc_ctor(6, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4460_, 0, v_x_4428_);
                crate::leanh::lean_ctor_set(v___x_4460_, 1, v_a_4456_);
                if v_isShared_4459_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4458_, 0, v___x_4460_);
                    v___x_4462_ = v___x_4458_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4463_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4463_, 0, v___x_4460_);
                    v___x_4462_ = v_reuseFailAlloc_4463_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4462_;
            }
            3 => {
                if v_isShared_4468_ == 0 {
                    v___x_4470_ = v___x_4467_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4471_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
                    v___x_4470_ = v_reuseFailAlloc_4471_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4470_;
            }
            5 => {
                v___x_4479_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4479_, 0, v_x_4428_);
                crate::leanh::lean_ctor_set(v___x_4479_, 1, v_a_4475_);
                if v_isShared_4478_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4477_, 0, v___x_4479_);
                    v___x_4481_ = v___x_4477_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4482_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4482_, 0, v___x_4479_);
                    v___x_4481_ = v_reuseFailAlloc_4482_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4481_;
            }
            7 => {
                if v_isShared_4487_ == 0 {
                    v___x_4489_ = v___x_4486_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4490_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_a_4484_);
                    v___x_4489_ = v_reuseFailAlloc_4490_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4489_;
            }
            9 => {
                v___x_4497_ = crate::leanh::lean_alloc_ctor(3, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4497_, 0, v_x_4428_);
                v___x_4498_ = (crate::leanh::lean_unbox(v_a_4493_) as u8);
                crate::leanh::lean_dec(v_a_4493_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4497_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4498_,
                );
                if v_isShared_4496_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4495_, 0, v___x_4497_);
                    v___x_4500_ = v___x_4495_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4501_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4501_, 0, v___x_4497_);
                    v___x_4500_ = v_reuseFailAlloc_4501_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4500_;
            }
            11 => {
                if v_isShared_4506_ == 0 {
                    v___x_4508_ = v___x_4505_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4509_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_a_4503_);
                    v___x_4508_ = v_reuseFailAlloc_4509_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4508_;
            }
            13 => {
                v___x_4516_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4516_, 0, v_x_4428_);
                crate::leanh::lean_ctor_set(v___x_4516_, 1, v_a_4512_);
                if v_isShared_4515_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4514_, 0, v___x_4516_);
                    v___x_4518_ = v___x_4514_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4519_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4519_, 0, v___x_4516_);
                    v___x_4518_ = v_reuseFailAlloc_4519_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4518_;
            }
            15 => {
                if v_isShared_4524_ == 0 {
                    v___x_4526_ = v___x_4523_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4527_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_a_4521_);
                    v___x_4526_ = v_reuseFailAlloc_4527_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4526_;
            }
            17 => {
                v___x_4534_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4534_, 0, v_x_4428_);
                crate::leanh::lean_ctor_set(v___x_4534_, 1, v_a_4530_);
                if v_isShared_4533_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4532_, 0, v___x_4534_);
                    v___x_4536_ = v___x_4532_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4537_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 0, v___x_4534_);
                    v___x_4536_ = v_reuseFailAlloc_4537_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4536_;
            }
            19 => {
                if v_isShared_4542_ == 0 {
                    v___x_4544_ = v___x_4541_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4545_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4545_, 0, v_a_4539_);
                    v___x_4544_ = v_reuseFailAlloc_4545_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4544_;
            }
            21 => {
                v___x_4552_ = lean_nat_to_int(v_a_4548_);
                v___x_4553_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4553_, 0, v_x_4428_);
                crate::leanh::lean_ctor_set(v___x_4553_, 1, v___x_4552_);
                if v_isShared_4551_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4550_, 0, v___x_4553_);
                    v___x_4555_ = v___x_4550_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4556_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4556_, 0, v___x_4553_);
                    v___x_4555_ = v_reuseFailAlloc_4556_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4555_;
            }
            23 => {
                if v_isShared_4561_ == 0 {
                    v___x_4563_ = v___x_4560_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4564_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4564_, 0, v_a_4558_);
                    v___x_4563_ = v_reuseFailAlloc_4564_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4563_;
            }
            25 => {
                v___x_4571_ = lean_nat_to_int(v_a_4567_);
                v___x_4572_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4572_, 0, v_x_4428_);
                crate::leanh::lean_ctor_set(v___x_4572_, 1, v___x_4571_);
                if v_isShared_4570_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4569_, 0, v___x_4572_);
                    v___x_4574_ = v___x_4569_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4575_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4575_, 0, v___x_4572_);
                    v___x_4574_ = v_reuseFailAlloc_4575_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_4574_;
            }
            27 => {
                if v_isShared_4580_ == 0 {
                    v___x_4582_ = v___x_4579_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4583_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
                    v___x_4582_ = v_reuseFailAlloc_4583_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_4582_;
            }
            29 => {
                v___x_4590_ = lean_nat_to_int(v_a_4586_);
                v___x_4591_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4591_, 0, v_x_4428_);
                crate::leanh::lean_ctor_set(v___x_4591_, 1, v___x_4590_);
                if v_isShared_4589_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4588_, 0, v___x_4591_);
                    v___x_4593_ = v___x_4588_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_4594_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4594_, 0, v___x_4591_);
                    v___x_4593_ = v_reuseFailAlloc_4594_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_4593_;
            }
            31 => {
                if v_isShared_4599_ == 0 {
                    v___x_4601_ = v___x_4598_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4602_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_a_4596_);
                    v___x_4601_ = v_reuseFailAlloc_4602_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_4601_;
            }
            33 => {
                v___x_4609_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4609_, 0, v_x_4428_);
                crate::leanh::lean_ctor_set(v___x_4609_, 1, v_a_4605_);
                if v_isShared_4608_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4607_, 0, v___x_4609_);
                    v___x_4611_ = v___x_4607_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_4612_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4612_, 0, v___x_4609_);
                    v___x_4611_ = v_reuseFailAlloc_4612_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_4611_;
            }
            35 => {
                if v_isShared_4617_ == 0 {
                    v___x_4619_ = v___x_4616_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_4620_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4620_, 0, v_a_4614_);
                    v___x_4619_ = v_reuseFailAlloc_4620_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_4619_;
            }
            37 => {
                v___x_4627_ = crate::leanh::lean_alloc_ctor(2, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_4627_, 0, v_x_4428_);
                v___x_4628_ = crate::leanh::lean_unbox_float(v_a_4623_);
                crate::leanh::lean_dec(v_a_4623_);
                crate::leanh::lean_ctor_set_float(
                    v___x_4627_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4628_,
                );
                if v_isShared_4626_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4625_, 0, v___x_4627_);
                    v___x_4630_ = v___x_4625_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_4631_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4631_, 0, v___x_4627_);
                    v___x_4630_ = v_reuseFailAlloc_4631_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_4630_;
            }
            39 => {
                if v_isShared_4636_ == 0 {
                    v___x_4638_ = v___x_4635_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_4639_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_a_4633_);
                    v___x_4638_ = v_reuseFailAlloc_4639_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_4638_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Toml_Elab_Value(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Toml_Data_Value(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Toml_Grammar(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Toml_Elab_Value(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lake_Toml_Grammar(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Toml_Elab_Value(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Toml_Data_Value(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Toml_Grammar(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Toml_Grammar(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Toml_Elab_Value(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Toml_Elab_Value(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Toml_Elab_Value(builtin);
}
