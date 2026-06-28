// Lean compiler output
// Module: Lake.Toml.Data.Value
// Imports: Init.Data.Float Lake.Toml.Data.Dict Lake.Toml.Data.DateTime Lake.Util.String Init.Data.String.TakeDrop Init.Data.String.Search Init.Data.String.Defs Init.Data.ToString.Macro
use crate::r#gen::Init::Data::Float::{
    initialize_Init_Data_Float, runtime_initialize_Init_Data_Float,
};
use crate::r#gen::Init::Data::Int::Repr::l_Int_repr;
use crate::r#gen::Init::Data::Repr::l_Nat_toDigits;
use crate::r#gen::Init::Data::String::Defs::{
    initialize_Init_Data_String_Defs, l_String_intercalate,
    runtime_initialize_Init_Data_String_Defs,
};
use crate::r#gen::Init::Data::String::FindPos::l_String_Slice_posLE;
use crate::r#gen::Init::Data::String::Iterate::l_String_Slice_positions;
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_structEq;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lake::Toml::Data::DateTime::{
    initialize_Lake_Toml_Data_DateTime, l_Lake_Toml_DateTime_toString,
    l_Lake_Toml_instDecidableEqDateTime_decEq, runtime_initialize_Lake_Toml_Data_DateTime,
};
use crate::r#gen::Lake::Toml::Data::Dict::{
    initialize_Lake_Toml_Data_Dict, l_Lake_Toml_RBDict_empty, l_Lake_Toml_RBDict_mkEmpty___redArg,
    runtime_initialize_Lake_Toml_Data_Dict,
};
use crate::r#gen::Lake::Util::String::{
    initialize_Lake_Util_String, l_Lake_lpadAscii, runtime_initialize_Lake_Util_String,
};
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, l_Lean_Name_isAnonymous,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Float::{lean_float_beq, lean_float_to_string};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_int_dec_eq;
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_extract, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_to_list, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed,
    lean_string_dec_eq, lean_string_mk, lean_string_utf8_byte_size, lean_uint32_dec_eq,
    lean_uint32_dec_le, lean_uint32_dec_lt, lean_uint32_to_nat, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_2, lean_box, lean_box_float,
    lean_ctor_get, lean_ctor_get_float, lean_ctor_get_uint8, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lake_Toml_instInhabitedValue_default___closed__0_value: LeanStringObject<1> =
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
static mut l_Lake_Toml_instInhabitedValue_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instInhabitedValue_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_Toml_instInhabitedValue_default___closed__1_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_instInhabitedValue_default___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_Toml_instInhabitedValue_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instInhabitedValue_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lake_Toml_instInhabitedValue_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instInhabitedValue_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lake_Toml_instInhabitedValue: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instInhabitedValue_default___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_Toml_instBEqValue___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Toml_instBEqValue_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Toml_instBEqValue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instBEqValue___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Toml_instBEqValue: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instBEqValue___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_Table_empty___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Toml_Table_empty___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Table_empty___closed__0_value) as *mut LeanObject;
static mut l_Lake_Toml_Table_empty___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_Table_empty___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_Table_empty: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [92, 117, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__1_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [92, 92, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__2_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [92, 34, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__2_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__3_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [92, 114, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__3_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__4_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [92, 102, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__4_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__5_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [92, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__5_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__6_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [92, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__6_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__7_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [92, 98, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__7_value) as *mut LeanObject;
pub static l_Lake_Toml_ppString___closed__0_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [34, 0],
};
static mut l_Lake_Toml_ppString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_ppString___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_ppKey___closed__0_value: LeanStringObject<2> = LeanStringObject {
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
static mut l_Lake_Toml_ppKey___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_ppKey___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_ppInlineArray___closed__0_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_ppInlineArray___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_ppInlineArray___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_ppInlineArray___closed__1_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [44, 32, 0],
};
static mut l_Lake_Toml_ppInlineArray___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_ppInlineArray___closed__1_value) as *mut LeanObject;
pub static l_Lake_Toml_ppInlineArray___closed__2_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_ppInlineArray___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_ppInlineArray___closed__2_value) as *mut LeanObject;
pub static l_Lake_Toml_Value_toString___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_Value_toString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_toString___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_Value_toString___closed__1_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_Value_toString___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Value_toString___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 61, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_ppInlineTable___closed__0_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [123, 0],
};
static mut l_Lake_Toml_ppInlineTable___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_ppInlineTable___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_ppInlineTable___closed__1_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [125, 0],
};
static mut l_Lake_Toml_ppInlineTable___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_ppInlineTable___closed__1_value) as *mut LeanObject;
pub static l_Lake_Toml_instToStringValue___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_Toml_Value_toString as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_instToStringValue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instToStringValue___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Toml_instToStringValue: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instToStringValue___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval___closed__0_value:
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
    m_data: [10, 0],
};
static mut l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval___closed__0_value
) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 91, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__1_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [93, 93, 10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__2_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [76, 97, 107, 101, 46, 84, 111, 109, 108, 46, 68, 97, 116, 97, 46, 86, 97, 108, 117, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__3_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [76, 97, 107, 101, 46, 84, 111, 109, 108, 46, 112, 112, 84, 97, 98, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__4_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__4_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [32, 61, 32, 91, 93, 10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__1_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [93, 10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__1_value) as *mut LeanObject;
pub static l_Lake_Toml_ppTable___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Toml_instInhabitedValue_default___closed__0_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_instInhabitedValue_default___closed__0_value)
            as *mut LeanObject,
    ],
};
static mut l_Lake_Toml_ppTable___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_ppTable___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lake_Toml_Value_ctorIdx(mut v_x_808_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_808_) {
        0 => {
            let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
            v___x_809_ = lean_unsigned_to_nat(0);
            return v___x_809_;
        }
        1 => {
            let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
            v___x_810_ = lean_unsigned_to_nat(1);
            return v___x_810_;
        }
        2 => {
            let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
            v___x_811_ = lean_unsigned_to_nat(2);
            return v___x_811_;
        }
        3 => {
            let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
            v___x_812_ = lean_unsigned_to_nat(3);
            return v___x_812_;
        }
        4 => {
            let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
            v___x_813_ = lean_unsigned_to_nat(4);
            return v___x_813_;
        }
        5 => {
            let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
            v___x_814_ = lean_unsigned_to_nat(5);
            return v___x_814_;
        }
        _ => {
            let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
            v___x_815_ = lean_unsigned_to_nat(6);
            return v___x_815_;
        }
    }
}
pub unsafe fn l_Lake_Toml_Value_ctorIdx___boxed(mut v_x_816_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_817_: *mut LeanObject = core::ptr::null_mut();
    v_res_817_ = l_Lake_Toml_Value_ctorIdx(v_x_816_);
    lean_dec_ref(v_x_816_);
    return v_res_817_;
}
pub unsafe fn l_Lake_Toml_Value_ctorElim___redArg(
    mut v_t_818_: *mut LeanObject,
    mut v_k_819_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_818_) {
        1 => {
            let mut v_ref_820_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_821_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
            v_ref_820_ = lean_ctor_get(v_t_818_, 0);
            lean_inc(v_ref_820_);
            v_n_821_ = lean_ctor_get(v_t_818_, 1);
            lean_inc(v_n_821_);
            lean_dec_ref_known(v_t_818_, 2);
            v___x_822_ = lean_apply_2(v_k_819_, v_ref_820_, v_n_821_);
            return v___x_822_;
        }
        2 => {
            let mut v_ref_823_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_824_: f64 = 0.0;
            let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
            v_ref_823_ = lean_ctor_get(v_t_818_, 0);
            lean_inc(v_ref_823_);
            v_n_824_ = lean_ctor_get_float(
                v_t_818_,
                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            );
            lean_dec_ref_known(v_t_818_, 1);
            v___x_825_ = lean_box_float(v_n_824_);
            v___x_826_ = lean_apply_2(v_k_819_, v_ref_823_, v___x_825_);
            return v___x_826_;
        }
        3 => {
            let mut v_ref_827_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_828_: u8 = 0;
            let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
            v_ref_827_ = lean_ctor_get(v_t_818_, 0);
            lean_inc(v_ref_827_);
            v_b_828_ = lean_ctor_get_uint8(
                v_t_818_,
                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            );
            lean_dec_ref_known(v_t_818_, 1);
            v___x_829_ = lean_box((v_b_828_) as usize);
            v___x_830_ = lean_apply_2(v_k_819_, v_ref_827_, v___x_829_);
            return v___x_830_;
        }
        _ => {
            let mut v_ref_831_: *mut LeanObject = core::ptr::null_mut();
            let mut v_s_832_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
            v_ref_831_ = lean_ctor_get(v_t_818_, 0);
            lean_inc(v_ref_831_);
            v_s_832_ = lean_ctor_get(v_t_818_, 1);
            lean_inc_ref(v_s_832_);
            lean_dec_ref(v_t_818_);
            v___x_833_ = lean_apply_2(v_k_819_, v_ref_831_, v_s_832_);
            return v___x_833_;
        }
    }
}
pub unsafe fn l_Lake_Toml_Value_ctorElim(
    mut v_motive__1_834_: *mut LeanObject,
    mut v_ctorIdx_835_: *mut LeanObject,
    mut v_t_836_: *mut LeanObject,
    mut v_h_837_: *mut LeanObject,
    mut v_k_838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    v___x_839_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_836_, v_k_838_);
    return v___x_839_;
}
pub unsafe fn l_Lake_Toml_Value_ctorElim___boxed(
    mut v_motive__1_840_: *mut LeanObject,
    mut v_ctorIdx_841_: *mut LeanObject,
    mut v_t_842_: *mut LeanObject,
    mut v_h_843_: *mut LeanObject,
    mut v_k_844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_845_: *mut LeanObject = core::ptr::null_mut();
    v_res_845_ = l_Lake_Toml_Value_ctorElim(
        v_motive__1_840_,
        v_ctorIdx_841_,
        v_t_842_,
        v_h_843_,
        v_k_844_,
    );
    lean_dec(v_ctorIdx_841_);
    return v_res_845_;
}
pub unsafe fn l_Lake_Toml_Value_string_elim___redArg(
    mut v_t_846_: *mut LeanObject,
    mut v_string_847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    v___x_848_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_846_, v_string_847_);
    return v___x_848_;
}
pub unsafe fn l_Lake_Toml_Value_string_elim(
    mut v_motive__1_849_: *mut LeanObject,
    mut v_t_850_: *mut LeanObject,
    mut v_h_851_: *mut LeanObject,
    mut v_string_852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    v___x_853_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_850_, v_string_852_);
    return v___x_853_;
}
pub unsafe fn l_Lake_Toml_Value_integer_elim___redArg(
    mut v_t_854_: *mut LeanObject,
    mut v_integer_855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    v___x_856_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_854_, v_integer_855_);
    return v___x_856_;
}
pub unsafe fn l_Lake_Toml_Value_integer_elim(
    mut v_motive__1_857_: *mut LeanObject,
    mut v_t_858_: *mut LeanObject,
    mut v_h_859_: *mut LeanObject,
    mut v_integer_860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    v___x_861_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_858_, v_integer_860_);
    return v___x_861_;
}
pub unsafe fn l_Lake_Toml_Value_float_elim___redArg(
    mut v_t_862_: *mut LeanObject,
    mut v_float_863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    v___x_864_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_862_, v_float_863_);
    return v___x_864_;
}
pub unsafe fn l_Lake_Toml_Value_float_elim(
    mut v_motive__1_865_: *mut LeanObject,
    mut v_t_866_: *mut LeanObject,
    mut v_h_867_: *mut LeanObject,
    mut v_float_868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    v___x_869_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_866_, v_float_868_);
    return v___x_869_;
}
pub unsafe fn l_Lake_Toml_Value_boolean_elim___redArg(
    mut v_t_870_: *mut LeanObject,
    mut v_boolean_871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    v___x_872_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_870_, v_boolean_871_);
    return v___x_872_;
}
pub unsafe fn l_Lake_Toml_Value_boolean_elim(
    mut v_motive__1_873_: *mut LeanObject,
    mut v_t_874_: *mut LeanObject,
    mut v_h_875_: *mut LeanObject,
    mut v_boolean_876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    v___x_877_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_874_, v_boolean_876_);
    return v___x_877_;
}
pub unsafe fn l_Lake_Toml_Value_dateTime_elim___redArg(
    mut v_t_878_: *mut LeanObject,
    mut v_dateTime_879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    v___x_880_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_878_, v_dateTime_879_);
    return v___x_880_;
}
pub unsafe fn l_Lake_Toml_Value_dateTime_elim(
    mut v_motive__1_881_: *mut LeanObject,
    mut v_t_882_: *mut LeanObject,
    mut v_h_883_: *mut LeanObject,
    mut v_dateTime_884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    v___x_885_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_882_, v_dateTime_884_);
    return v___x_885_;
}
pub unsafe fn l_Lake_Toml_Value_array_elim___redArg(
    mut v_t_886_: *mut LeanObject,
    mut v_array_887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    v___x_888_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_886_, v_array_887_);
    return v___x_888_;
}
pub unsafe fn l_Lake_Toml_Value_array_elim(
    mut v_motive__1_889_: *mut LeanObject,
    mut v_t_890_: *mut LeanObject,
    mut v_h_891_: *mut LeanObject,
    mut v_array_892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    v___x_893_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_890_, v_array_892_);
    return v___x_893_;
}
pub unsafe fn l_Lake_Toml_Value_table_x27_elim___redArg(
    mut v_t_894_: *mut LeanObject,
    mut v_table_x27_895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    v___x_896_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_894_, v_table_x27_895_);
    return v___x_896_;
}
pub unsafe fn l_Lake_Toml_Value_table_x27_elim(
    mut v_motive__1_897_: *mut LeanObject,
    mut v_t_898_: *mut LeanObject,
    mut v_h_899_: *mut LeanObject,
    mut v_table_x27_900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    v___x_901_ = l_Lake_Toml_Value_ctorElim___redArg(v_t_898_, v_table_x27_900_);
    return v___x_901_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg(
    mut v_xs_908_: *mut LeanObject,
    mut v_ys_909_: *mut LeanObject,
    mut v_x_910_: *mut LeanObject,
) -> u8 {
    let mut v_zero_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_912_: u8 = 0;
    let mut v_one_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_911_ = lean_unsigned_to_nat(0);
                v_isZero_912_ = lean_nat_dec_eq(v_x_910_, v_zero_911_);
                if v_isZero_912_ == 1 {
                    lean_dec(v_x_910_);
                    return v_isZero_912_;
                } else {
                    v_one_913_ = lean_unsigned_to_nat(1);
                    v_n_914_ = lean_nat_sub(v_x_910_, v_one_913_);
                    lean_dec(v_x_910_);
                    v___x_915_ = lean_array_fget_borrowed(v_xs_908_, v_n_914_);
                    v___x_916_ = lean_array_fget_borrowed(v_ys_909_, v_n_914_);
                    lean_inc(v___x_916_);
                    lean_inc(v___x_915_);
                    v___x_917_ = l_Lake_Toml_instBEqValue_beq(v___x_915_, v___x_916_);
                    if v___x_917_ == 0 {
                        lean_dec(v_n_914_);
                        return v___x_917_;
                    } else {
                        v_x_910_ = v_n_914_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_instBEqValue_beq(
    mut v_x_919_: *mut LeanObject,
    mut v_x_920_: *mut LeanObject,
) -> u8 {
    match lean_obj_tag(v_x_919_) {
        0 => {
            if lean_obj_tag(v_x_920_) == 0 {
                let mut v_ref_921_: *mut LeanObject = core::ptr::null_mut();
                let mut v_s_922_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_923_: *mut LeanObject = core::ptr::null_mut();
                let mut v_s_924_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_925_: u8 = 0;
                v_ref_921_ = lean_ctor_get(v_x_919_, 0);
                lean_inc(v_ref_921_);
                v_s_922_ = lean_ctor_get(v_x_919_, 1);
                lean_inc_ref(v_s_922_);
                lean_dec_ref_known(v_x_919_, 2);
                v_ref_923_ = lean_ctor_get(v_x_920_, 0);
                lean_inc(v_ref_923_);
                v_s_924_ = lean_ctor_get(v_x_920_, 1);
                lean_inc_ref(v_s_924_);
                lean_dec_ref_known(v_x_920_, 2);
                v___x_925_ = l_Lean_Syntax_structEq(v_ref_921_, v_ref_923_);
                if v___x_925_ == 0 {
                    lean_dec_ref(v_s_924_);
                    lean_dec_ref(v_s_922_);
                    return v___x_925_;
                } else {
                    let mut v___x_926_: u8 = 0;
                    v___x_926_ = lean_string_dec_eq(v_s_922_, v_s_924_);
                    lean_dec_ref(v_s_924_);
                    lean_dec_ref(v_s_922_);
                    return v___x_926_;
                }
            } else {
                let mut v___x_927_: u8 = 0;
                lean_dec_ref_known(v_x_919_, 2);
                lean_dec_ref(v_x_920_);
                v___x_927_ = 0;
                return v___x_927_;
            }
        }
        1 => {
            if lean_obj_tag(v_x_920_) == 1 {
                let mut v_ref_928_: *mut LeanObject = core::ptr::null_mut();
                let mut v_n_929_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_930_: *mut LeanObject = core::ptr::null_mut();
                let mut v_n_931_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_932_: u8 = 0;
                v_ref_928_ = lean_ctor_get(v_x_919_, 0);
                lean_inc(v_ref_928_);
                v_n_929_ = lean_ctor_get(v_x_919_, 1);
                lean_inc(v_n_929_);
                lean_dec_ref_known(v_x_919_, 2);
                v_ref_930_ = lean_ctor_get(v_x_920_, 0);
                lean_inc(v_ref_930_);
                v_n_931_ = lean_ctor_get(v_x_920_, 1);
                lean_inc(v_n_931_);
                lean_dec_ref_known(v_x_920_, 2);
                v___x_932_ = l_Lean_Syntax_structEq(v_ref_928_, v_ref_930_);
                if v___x_932_ == 0 {
                    lean_dec(v_n_931_);
                    lean_dec(v_n_929_);
                    return v___x_932_;
                } else {
                    let mut v___x_933_: u8 = 0;
                    v___x_933_ = lean_int_dec_eq(v_n_929_, v_n_931_);
                    lean_dec(v_n_931_);
                    lean_dec(v_n_929_);
                    return v___x_933_;
                }
            } else {
                let mut v___x_934_: u8 = 0;
                lean_dec_ref_known(v_x_919_, 2);
                lean_dec_ref(v_x_920_);
                v___x_934_ = 0;
                return v___x_934_;
            }
        }
        2 => {
            if lean_obj_tag(v_x_920_) == 2 {
                let mut v_ref_935_: *mut LeanObject = core::ptr::null_mut();
                let mut v_n_936_: f64 = 0.0;
                let mut v_ref_937_: *mut LeanObject = core::ptr::null_mut();
                let mut v_n_938_: f64 = 0.0;
                let mut v___x_939_: u8 = 0;
                v_ref_935_ = lean_ctor_get(v_x_919_, 0);
                lean_inc(v_ref_935_);
                v_n_936_ = lean_ctor_get_float(
                    v_x_919_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                lean_dec_ref_known(v_x_919_, 1);
                v_ref_937_ = lean_ctor_get(v_x_920_, 0);
                lean_inc(v_ref_937_);
                v_n_938_ = lean_ctor_get_float(
                    v_x_920_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                lean_dec_ref_known(v_x_920_, 1);
                v___x_939_ = l_Lean_Syntax_structEq(v_ref_935_, v_ref_937_);
                if v___x_939_ == 0 {
                    return v___x_939_;
                } else {
                    let mut v___x_940_: u8 = 0;
                    v___x_940_ = lean_float_beq(v_n_936_, v_n_938_);
                    return v___x_940_;
                }
            } else {
                let mut v___x_941_: u8 = 0;
                lean_dec_ref_known(v_x_919_, 1);
                lean_dec_ref(v_x_920_);
                v___x_941_ = 0;
                return v___x_941_;
            }
        }
        3 => {
            if lean_obj_tag(v_x_920_) == 3 {
                let mut v_ref_942_: *mut LeanObject = core::ptr::null_mut();
                let mut v_b_943_: u8 = 0;
                let mut v_ref_944_: *mut LeanObject = core::ptr::null_mut();
                let mut v_b_945_: u8 = 0;
                let mut v___x_946_: u8 = 0;
                v_ref_942_ = lean_ctor_get(v_x_919_, 0);
                lean_inc(v_ref_942_);
                v_b_943_ = lean_ctor_get_uint8(
                    v_x_919_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                lean_dec_ref_known(v_x_919_, 1);
                v_ref_944_ = lean_ctor_get(v_x_920_, 0);
                lean_inc(v_ref_944_);
                v_b_945_ = lean_ctor_get_uint8(
                    v_x_920_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                lean_dec_ref_known(v_x_920_, 1);
                v___x_946_ = l_Lean_Syntax_structEq(v_ref_942_, v_ref_944_);
                if v___x_946_ == 0 {
                    return v___x_946_;
                } else {
                    if v_b_943_ == 0 {
                        if v_b_945_ == 0 {
                            return v___x_946_;
                        } else {
                            return v_b_943_;
                        }
                    } else {
                        return v_b_945_;
                    }
                }
            } else {
                let mut v___x_947_: u8 = 0;
                lean_dec_ref_known(v_x_919_, 1);
                lean_dec_ref(v_x_920_);
                v___x_947_ = 0;
                return v___x_947_;
            }
        }
        4 => {
            if lean_obj_tag(v_x_920_) == 4 {
                let mut v_ref_948_: *mut LeanObject = core::ptr::null_mut();
                let mut v_dt_949_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_950_: *mut LeanObject = core::ptr::null_mut();
                let mut v_dt_951_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_952_: u8 = 0;
                v_ref_948_ = lean_ctor_get(v_x_919_, 0);
                lean_inc(v_ref_948_);
                v_dt_949_ = lean_ctor_get(v_x_919_, 1);
                lean_inc_ref(v_dt_949_);
                lean_dec_ref_known(v_x_919_, 2);
                v_ref_950_ = lean_ctor_get(v_x_920_, 0);
                lean_inc(v_ref_950_);
                v_dt_951_ = lean_ctor_get(v_x_920_, 1);
                lean_inc_ref(v_dt_951_);
                lean_dec_ref_known(v_x_920_, 2);
                v___x_952_ = l_Lean_Syntax_structEq(v_ref_948_, v_ref_950_);
                if v___x_952_ == 0 {
                    lean_dec_ref(v_dt_951_);
                    lean_dec_ref(v_dt_949_);
                    return v___x_952_;
                } else {
                    let mut v___x_953_: u8 = 0;
                    v___x_953_ = l_Lake_Toml_instDecidableEqDateTime_decEq(v_dt_949_, v_dt_951_);
                    return v___x_953_;
                }
            } else {
                let mut v___x_954_: u8 = 0;
                lean_dec_ref_known(v_x_919_, 2);
                lean_dec_ref(v_x_920_);
                v___x_954_ = 0;
                return v___x_954_;
            }
        }
        5 => {
            if lean_obj_tag(v_x_920_) == 5 {
                let mut v_ref_955_: *mut LeanObject = core::ptr::null_mut();
                let mut v_xs_956_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_957_: *mut LeanObject = core::ptr::null_mut();
                let mut v_xs_958_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_959_: u8 = 0;
                v_ref_955_ = lean_ctor_get(v_x_919_, 0);
                lean_inc(v_ref_955_);
                v_xs_956_ = lean_ctor_get(v_x_919_, 1);
                lean_inc_ref(v_xs_956_);
                lean_dec_ref_known(v_x_919_, 2);
                v_ref_957_ = lean_ctor_get(v_x_920_, 0);
                lean_inc(v_ref_957_);
                v_xs_958_ = lean_ctor_get(v_x_920_, 1);
                lean_inc_ref(v_xs_958_);
                lean_dec_ref_known(v_x_920_, 2);
                v___x_959_ = l_Lean_Syntax_structEq(v_ref_955_, v_ref_957_);
                if v___x_959_ == 0 {
                    lean_dec_ref(v_xs_958_);
                    lean_dec_ref(v_xs_956_);
                    return v___x_959_;
                } else {
                    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_962_: u8 = 0;
                    v___x_960_ = lean_array_get_size(v_xs_956_);
                    v___x_961_ = lean_array_get_size(v_xs_958_);
                    v___x_962_ = lean_nat_dec_eq(v___x_960_, v___x_961_);
                    if v___x_962_ == 0 {
                        lean_dec_ref(v_xs_958_);
                        lean_dec_ref(v_xs_956_);
                        return v___x_962_;
                    } else {
                        let mut v___x_963_: u8 = 0;
                        v___x_963_ =
                            l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg(
                                v_xs_956_, v_xs_958_, v___x_960_,
                            );
                        lean_dec_ref(v_xs_958_);
                        lean_dec_ref(v_xs_956_);
                        return v___x_963_;
                    }
                }
            } else {
                let mut v___x_964_: u8 = 0;
                lean_dec_ref_known(v_x_919_, 2);
                lean_dec_ref(v_x_920_);
                v___x_964_ = 0;
                return v___x_964_;
            }
        }
        _ => {
            if lean_obj_tag(v_x_920_) == 6 {
                let mut v_ref_965_: *mut LeanObject = core::ptr::null_mut();
                let mut v_xs_966_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ref_967_: *mut LeanObject = core::ptr::null_mut();
                let mut v_xs_968_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_969_: u8 = 0;
                v_ref_965_ = lean_ctor_get(v_x_919_, 0);
                lean_inc(v_ref_965_);
                v_xs_966_ = lean_ctor_get(v_x_919_, 1);
                lean_inc_ref(v_xs_966_);
                lean_dec_ref_known(v_x_919_, 2);
                v_ref_967_ = lean_ctor_get(v_x_920_, 0);
                lean_inc(v_ref_967_);
                v_xs_968_ = lean_ctor_get(v_x_920_, 1);
                lean_inc_ref(v_xs_968_);
                lean_dec_ref_known(v_x_920_, 2);
                v___x_969_ = l_Lean_Syntax_structEq(v_ref_965_, v_ref_967_);
                if v___x_969_ == 0 {
                    lean_dec_ref(v_xs_968_);
                    lean_dec_ref(v_xs_966_);
                    return v___x_969_;
                } else {
                    let mut v___x_970_: u8 = 0;
                    v___x_970_ =
                        l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg(
                            v_xs_966_, v_xs_968_,
                        );
                    lean_dec_ref(v_xs_968_);
                    lean_dec_ref(v_xs_966_);
                    return v___x_970_;
                }
            } else {
                let mut v___x_971_: u8 = 0;
                lean_dec_ref_known(v_x_919_, 2);
                lean_dec_ref(v_x_920_);
                v___x_971_ = 0;
                return v___x_971_;
            }
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg(
    mut v_xs_972_: *mut LeanObject,
    mut v_ys_973_: *mut LeanObject,
    mut v_x_974_: *mut LeanObject,
) -> u8 {
    let mut v_zero_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_976_: u8 = 0;
    let mut v_one_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_980_: u8 = 0;
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: u8 = 0;
    let mut v___x_989_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_975_ = lean_unsigned_to_nat(0);
                v_isZero_976_ = lean_nat_dec_eq(v_x_974_, v_zero_975_);
                if v_isZero_976_ == 1 {
                    lean_dec(v_x_974_);
                    return v_isZero_976_;
                } else {
                    v_one_977_ = lean_unsigned_to_nat(1);
                    v_n_978_ = lean_nat_sub(v_x_974_, v_one_977_);
                    lean_dec(v_x_974_);
                    v___x_982_ = lean_array_fget_borrowed(v_xs_972_, v_n_978_);
                    v_fst_983_ = lean_ctor_get(v___x_982_, 0);
                    v_snd_984_ = lean_ctor_get(v___x_982_, 1);
                    v___x_985_ = lean_array_fget_borrowed(v_ys_973_, v_n_978_);
                    v_fst_986_ = lean_ctor_get(v___x_985_, 0);
                    v_snd_987_ = lean_ctor_get(v___x_985_, 1);
                    v___x_988_ = lean_name_eq(v_fst_983_, v_fst_986_);
                    if v___x_988_ == 0 {
                        v___y_980_ = v___x_988_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_987_);
                        lean_inc(v_snd_984_);
                        v___x_989_ = l_Lake_Toml_instBEqValue_beq(v_snd_984_, v_snd_987_);
                        v___y_980_ = v___x_989_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_980_ == 0 {
                    lean_dec(v_n_978_);
                    return v___y_980_;
                } else {
                    v_x_974_ = v_n_978_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg(
    mut v_self_990_: *mut LeanObject,
    mut v_other_991_: *mut LeanObject,
) -> u8 {
    let mut v_items_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_items_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_996_: u8 = 0;
    v_items_992_ = lean_ctor_get(v_self_990_, 0);
    v_items_993_ = lean_ctor_get(v_other_991_, 0);
    v___x_994_ = lean_array_get_size(v_items_992_);
    v___x_995_ = lean_array_get_size(v_items_993_);
    v___x_996_ = lean_nat_dec_eq(v___x_994_, v___x_995_);
    if v___x_996_ == 0 {
        return v___x_996_;
    } else {
        let mut v___x_997_: u8 = 0;
        v___x_997_ = l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg(v_items_992_, v_items_993_, v___x_994_);
        return v___x_997_;
    }
}
pub unsafe fn l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg___boxed(
    mut v_self_998_: *mut LeanObject,
    mut v_other_999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1000_: u8 = 0;
    let mut v_r_1001_: *mut LeanObject = core::ptr::null_mut();
    v_res_1000_ = l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg(
        v_self_998_,
        v_other_999_,
    );
    lean_dec_ref(v_other_999_);
    lean_dec_ref(v_self_998_);
    v_r_1001_ = lean_box((v_res_1000_) as usize);
    return v_r_1001_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg___boxed(
    mut v_xs_1002_: *mut LeanObject,
    mut v_ys_1003_: *mut LeanObject,
    mut v_x_1004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1005_: u8 = 0;
    let mut v_r_1006_: *mut LeanObject = core::ptr::null_mut();
    v_res_1005_ = l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg(
        v_xs_1002_, v_ys_1003_, v_x_1004_,
    );
    lean_dec_ref(v_ys_1003_);
    lean_dec_ref(v_xs_1002_);
    v_r_1006_ = lean_box((v_res_1005_) as usize);
    return v_r_1006_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg___boxed(
    mut v_xs_1007_: *mut LeanObject,
    mut v_ys_1008_: *mut LeanObject,
    mut v_x_1009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1010_: u8 = 0;
    let mut v_r_1011_: *mut LeanObject = core::ptr::null_mut();
    v_res_1010_ = l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg(v_xs_1007_, v_ys_1008_, v_x_1009_);
    lean_dec_ref(v_ys_1008_);
    lean_dec_ref(v_xs_1007_);
    v_r_1011_ = lean_box((v_res_1010_) as usize);
    return v_r_1011_;
}
pub unsafe fn l_Lake_Toml_instBEqValue_beq___boxed(
    mut v_x_1012_: *mut LeanObject,
    mut v_x_1013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1014_: u8 = 0;
    let mut v_r_1015_: *mut LeanObject = core::ptr::null_mut();
    v_res_1014_ = l_Lake_Toml_instBEqValue_beq(v_x_1012_, v_x_1013_);
    v_r_1015_ = lean_box((v_res_1014_) as usize);
    return v_r_1015_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0(
    mut v_xs_1016_: *mut LeanObject,
    mut v_ys_1017_: *mut LeanObject,
    mut v_hsz_1018_: *mut LeanObject,
    mut v_x_1019_: *mut LeanObject,
    mut v_x_1020_: *mut LeanObject,
) -> u8 {
    let mut v___x_1021_: u8 = 0;
    v___x_1021_ = l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___redArg(
        v_xs_1016_, v_ys_1017_, v_x_1019_,
    );
    return v___x_1021_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0___boxed(
    mut v_xs_1022_: *mut LeanObject,
    mut v_ys_1023_: *mut LeanObject,
    mut v_hsz_1024_: *mut LeanObject,
    mut v_x_1025_: *mut LeanObject,
    mut v_x_1026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1027_: u8 = 0;
    let mut v_r_1028_: *mut LeanObject = core::ptr::null_mut();
    v_res_1027_ = l_Array_isEqvAux___at___00Lake_Toml_instBEqValue_beq_spec__0(
        v_xs_1022_,
        v_ys_1023_,
        v_hsz_1024_,
        v_x_1025_,
        v_x_1026_,
    );
    lean_dec_ref(v_ys_1023_);
    lean_dec_ref(v_xs_1022_);
    v_r_1028_ = lean_box((v_res_1027_) as usize);
    return v_r_1028_;
}
pub unsafe fn l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1(
    mut v_cmp_1029_: *mut LeanObject,
    mut v_self_1030_: *mut LeanObject,
    mut v_other_1031_: *mut LeanObject,
) -> u8 {
    let mut v___x_1032_: u8 = 0;
    v___x_1032_ = l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___redArg(
        v_self_1030_,
        v_other_1031_,
    );
    return v___x_1032_;
}
pub unsafe fn l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1___boxed(
    mut v_cmp_1033_: *mut LeanObject,
    mut v_self_1034_: *mut LeanObject,
    mut v_other_1035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1036_: u8 = 0;
    let mut v_r_1037_: *mut LeanObject = core::ptr::null_mut();
    v_res_1036_ = l_Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1(
        v_cmp_1033_,
        v_self_1034_,
        v_other_1035_,
    );
    lean_dec_ref(v_other_1035_);
    lean_dec_ref(v_self_1034_);
    lean_dec_ref(v_cmp_1033_);
    v_r_1037_ = lean_box((v_res_1036_) as usize);
    return v_r_1037_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1(
    mut v_xs_1038_: *mut LeanObject,
    mut v_ys_1039_: *mut LeanObject,
    mut v_hsz_1040_: *mut LeanObject,
    mut v_x_1041_: *mut LeanObject,
    mut v_x_1042_: *mut LeanObject,
) -> u8 {
    let mut v___x_1043_: u8 = 0;
    v___x_1043_ = l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___redArg(v_xs_1038_, v_ys_1039_, v_x_1041_);
    return v___x_1043_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1___boxed(
    mut v_xs_1044_: *mut LeanObject,
    mut v_ys_1045_: *mut LeanObject,
    mut v_hsz_1046_: *mut LeanObject,
    mut v_x_1047_: *mut LeanObject,
    mut v_x_1048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1049_: u8 = 0;
    let mut v_r_1050_: *mut LeanObject = core::ptr::null_mut();
    v_res_1049_ = l_Array_isEqvAux___at___00Lake_Toml_RBDict_beq___at___00Lake_Toml_instBEqValue_beq_spec__1_spec__1(v_xs_1044_, v_ys_1045_, v_hsz_1046_, v_x_1047_, v_x_1048_);
    lean_dec_ref(v_ys_1045_);
    lean_dec_ref(v_xs_1044_);
    v_r_1050_ = lean_box((v_res_1049_) as usize);
    return v_r_1050_;
}
pub unsafe fn _init_l_Lake_Toml_Table_empty___closed__1() -> *mut LeanObject {
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    v___x_1054_ = l_Lake_Toml_Table_empty___closed__0;
    v___x_1055_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_1054_);
    return v___x_1055_;
}
pub unsafe fn _init_l_Lake_Toml_Table_empty() -> *mut LeanObject {
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    v___x_1056_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_Table_empty___closed__1),
        core::ptr::addr_of_mut!(l_Lake_Toml_Table_empty___closed__1_once),
        _init_l_Lake_Toml_Table_empty___closed__1,
    );
    return v___x_1056_;
}
pub unsafe fn l_Lake_Toml_Table_mkEmpty(mut v_capacity_1057_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    v___x_1058_ = l_Lake_Toml_RBDict_mkEmpty___redArg(v_capacity_1057_);
    return v___x_1058_;
}
pub unsafe fn l_Lake_Toml_Table_mkEmpty___boxed(
    mut v_capacity_1059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1060_: *mut LeanObject = core::ptr::null_mut();
    v_res_1060_ = l_Lake_Toml_Table_mkEmpty(v_capacity_1059_);
    lean_dec(v_capacity_1059_);
    return v_res_1060_;
}
pub unsafe fn l_Lake_Toml_Value_table(
    mut v_ref_1061_: *mut LeanObject,
    mut v_t_1062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    v___x_1063_ = lean_alloc_ctor(6, 2, (0) as u32);
    lean_ctor_set(v___x_1063_, 0, v_ref_1061_);
    lean_ctor_set(v___x_1063_, 1, v_t_1062_);
    return v___x_1063_;
}
pub unsafe fn l_Lake_Toml_Value_ref(mut v_x_1064_: *mut LeanObject) -> *mut LeanObject {
    let mut v_ref_1065_: *mut LeanObject = core::ptr::null_mut();
    v_ref_1065_ = lean_ctor_get(v_x_1064_, 0);
    lean_inc(v_ref_1065_);
    return v_ref_1065_;
}
pub unsafe fn l_Lake_Toml_Value_ref___boxed(mut v_x_1066_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1067_: *mut LeanObject = core::ptr::null_mut();
    v_res_1067_ = l_Lake_Toml_Value_ref(v_x_1066_);
    lean_dec_ref(v_x_1066_);
    return v_res_1067_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(
    mut v___x_1076_: *mut LeanObject,
    mut v_s_1077_: *mut LeanObject,
    mut v_a_1078_: *mut LeanObject,
    mut v_b_1079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_startInclusive_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: u8 = 0;
    let mut v___x_1084_: u32 = 0;
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1087_: u8 = 0;
    let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: u32 = 0;
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: u32 = 0;
    let mut v___x_1102_: u8 = 0;
    let mut v___x_1103_: u32 = 0;
    let mut v___x_1104_: u8 = 0;
    let mut v___x_1105_: u32 = 0;
    let mut v___x_1106_: u8 = 0;
    let mut v___x_1107_: u32 = 0;
    let mut v___x_1108_: u8 = 0;
    let mut v___x_1109_: u32 = 0;
    let mut v___x_1110_: u8 = 0;
    let mut v___x_1111_: u32 = 0;
    let mut v___x_1112_: u8 = 0;
    let mut v___x_1113_: u32 = 0;
    let mut v___x_1114_: u8 = 0;
    let mut v___x_1115_: u32 = 0;
    let mut v___x_1116_: u8 = 0;
    let mut v___x_1117_: u32 = 0;
    let mut v___x_1118_: u8 = 0;
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_1080_ = lean_ctor_get(v___x_1076_, 1);
                v_endExclusive_1081_ = lean_ctor_get(v___x_1076_, 2);
                v___x_1082_ = lean_nat_sub(v_endExclusive_1081_, v_startInclusive_1080_);
                v___x_1083_ = lean_nat_dec_eq(v_a_1078_, v___x_1082_);
                lean_dec(v___x_1082_);
                if v___x_1083_ == 0 {
                    v___x_1084_ = lean_string_utf8_get_fast(v_s_1077_, v_a_1078_);
                    v___x_1085_ = lean_string_utf8_next_fast(v_s_1077_, v_a_1078_);
                    lean_dec(v_a_1078_);
                    v___x_1101_ = 8;
                    v___x_1102_ = lean_uint32_dec_eq(v___x_1084_, v___x_1101_);
                    if v___x_1102_ == 0 {
                        v___x_1103_ = 9;
                        v___x_1104_ = lean_uint32_dec_eq(v___x_1084_, v___x_1103_);
                        if v___x_1104_ == 0 {
                            v___x_1105_ = 10;
                            v___x_1106_ = lean_uint32_dec_eq(v___x_1084_, v___x_1105_);
                            if v___x_1106_ == 0 {
                                v___x_1107_ = 12;
                                v___x_1108_ = lean_uint32_dec_eq(v___x_1084_, v___x_1107_);
                                if v___x_1108_ == 0 {
                                    v___x_1109_ = 13;
                                    v___x_1110_ = lean_uint32_dec_eq(v___x_1084_, v___x_1109_);
                                    if v___x_1110_ == 0 {
                                        v___x_1111_ = 34;
                                        v___x_1112_ = lean_uint32_dec_eq(v___x_1084_, v___x_1111_);
                                        if v___x_1112_ == 0 {
                                            v___x_1113_ = 92;
                                            v___x_1114_ =
                                                lean_uint32_dec_eq(v___x_1084_, v___x_1113_);
                                            if v___x_1114_ == 0 {
                                                v___x_1115_ = 32;
                                                v___x_1116_ =
                                                    lean_uint32_dec_lt(v___x_1084_, v___x_1115_);
                                                if v___x_1116_ == 0 {
                                                    v___x_1117_ = 127;
                                                    v___x_1118_ = lean_uint32_dec_eq(
                                                        v___x_1084_,
                                                        v___x_1117_,
                                                    );
                                                    v___y_1087_ = v___x_1118_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___y_1087_ = v___x_1116_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                v___x_1119_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__1;
                                                v___x_1120_ =
                                                    lean_string_append(v_b_1079_, v___x_1119_);
                                                v_a_1078_ = v___x_1085_;
                                                v_b_1079_ = v___x_1120_;
                                                state = 0;
                                                continue;
                                            }
                                        } else {
                                            v___x_1122_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__2;
                                            v___x_1123_ =
                                                lean_string_append(v_b_1079_, v___x_1122_);
                                            v_a_1078_ = v___x_1085_;
                                            v_b_1079_ = v___x_1123_;
                                            state = 0;
                                            continue;
                                        }
                                    } else {
                                        v___x_1125_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__3;
                                        v___x_1126_ = lean_string_append(v_b_1079_, v___x_1125_);
                                        v_a_1078_ = v___x_1085_;
                                        v_b_1079_ = v___x_1126_;
                                        state = 0;
                                        continue;
                                    }
                                } else {
                                    v___x_1128_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__4;
                                    v___x_1129_ = lean_string_append(v_b_1079_, v___x_1128_);
                                    v_a_1078_ = v___x_1085_;
                                    v_b_1079_ = v___x_1129_;
                                    state = 0;
                                    continue;
                                }
                            } else {
                                v___x_1131_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__5;
                                v___x_1132_ = lean_string_append(v_b_1079_, v___x_1131_);
                                v_a_1078_ = v___x_1085_;
                                v_b_1079_ = v___x_1132_;
                                state = 0;
                                continue;
                            }
                        } else {
                            v___x_1134_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__6;
                            v___x_1135_ = lean_string_append(v_b_1079_, v___x_1134_);
                            v_a_1078_ = v___x_1085_;
                            v_b_1079_ = v___x_1135_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_1137_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__7;
                        v___x_1138_ = lean_string_append(v_b_1079_, v___x_1137_);
                        v_a_1078_ = v___x_1085_;
                        v_b_1079_ = v___x_1138_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1078_);
                    return v_b_1079_;
                }
            }
            1 => {
                if v___y_1087_ == 0 {
                    v___x_1088_ = lean_string_push(v_b_1079_, v___x_1084_);
                    v_a_1078_ = v___x_1085_;
                    v_b_1079_ = v___x_1088_;
                    state = 0;
                    continue;
                } else {
                    v___x_1090_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___closed__0;
                    v___x_1091_ = lean_string_append(v_b_1079_, v___x_1090_);
                    v___x_1092_ = lean_unsigned_to_nat(16);
                    v___x_1093_ = lean_uint32_to_nat(v___x_1084_);
                    v___x_1094_ = l_Nat_toDigits(v___x_1092_, v___x_1093_);
                    v___x_1095_ = lean_string_mk(v___x_1094_);
                    v___x_1096_ = 48;
                    v___x_1097_ = lean_unsigned_to_nat(4);
                    v___x_1098_ = l_Lake_lpadAscii(v___x_1095_, v___x_1096_, v___x_1097_);
                    lean_dec_ref(v___x_1095_);
                    v___x_1099_ = lean_string_append(v___x_1091_, v___x_1098_);
                    lean_dec_ref(v___x_1098_);
                    v_a_1078_ = v___x_1085_;
                    v_b_1079_ = v___x_1099_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg___boxed(
    mut v___x_1140_: *mut LeanObject,
    mut v_s_1141_: *mut LeanObject,
    mut v_a_1142_: *mut LeanObject,
    mut v_b_1143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1144_: *mut LeanObject = core::ptr::null_mut();
    v_res_1144_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(
        v___x_1140_,
        v_s_1141_,
        v_a_1142_,
        v_b_1143_,
    );
    lean_dec_ref(v_s_1141_);
    lean_dec_ref(v___x_1140_);
    return v_res_1144_;
}
pub unsafe fn l_Lake_Toml_ppString(mut v_s_1146_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: u32 = 0;
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    v___x_1147_ = l_Lake_Toml_ppString___closed__0;
    v___x_1148_ = lean_unsigned_to_nat(0);
    v___x_1149_ = lean_string_utf8_byte_size(v_s_1146_);
    lean_inc_ref(v_s_1146_);
    v___x_1150_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1150_, 0, v_s_1146_);
    lean_ctor_set(v___x_1150_, 1, v___x_1148_);
    lean_ctor_set(v___x_1150_, 2, v___x_1149_);
    v___x_1151_ = l_String_Slice_positions(v___x_1150_);
    v_s_1152_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(
        v___x_1150_,
        v_s_1146_,
        v___x_1151_,
        v___x_1147_,
    );
    lean_dec_ref(v_s_1146_);
    lean_dec_ref_known(v___x_1150_, 3);
    v___x_1153_ = 34;
    v___x_1154_ = lean_string_push(v_s_1152_, v___x_1153_);
    return v___x_1154_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0(
    mut v___x_1155_: *mut LeanObject,
    mut v_s_1156_: *mut LeanObject,
    mut v_inst_1157_: *mut LeanObject,
    mut v_R_1158_: *mut LeanObject,
    mut v_a_1159_: *mut LeanObject,
    mut v_b_1160_: *mut LeanObject,
    mut v_c_1161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    v___x_1162_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___redArg(
        v___x_1155_,
        v_s_1156_,
        v_a_1159_,
        v_b_1160_,
    );
    return v___x_1162_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0___boxed(
    mut v___x_1163_: *mut LeanObject,
    mut v_s_1164_: *mut LeanObject,
    mut v_inst_1165_: *mut LeanObject,
    mut v_R_1166_: *mut LeanObject,
    mut v_a_1167_: *mut LeanObject,
    mut v_b_1168_: *mut LeanObject,
    mut v_c_1169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1170_: *mut LeanObject = core::ptr::null_mut();
    v_res_1170_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_ppString_spec__0(
        v___x_1163_,
        v_s_1164_,
        v_inst_1165_,
        v_R_1166_,
        v_a_1167_,
        v_b_1168_,
        v_c_1169_,
    );
    lean_dec_ref(v_s_1164_);
    lean_dec_ref(v___x_1163_);
    return v_res_1170_;
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0(
    mut v_s_1171_: *mut LeanObject,
    mut v_pos_1172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: u8 = 0;
    let mut v___y_1184_: u8 = 0;
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: u8 = 0;
    let mut v___x_1188_: u32 = 0;
    let mut v___y_1190_: u8 = 0;
    let mut v___x_1191_: u32 = 0;
    let mut v___x_1192_: u8 = 0;
    let mut v___x_1193_: u32 = 0;
    let mut v___x_1194_: u8 = 0;
    let mut v___y_1196_: u8 = 0;
    let mut v___x_1197_: u32 = 0;
    let mut v___x_1198_: u8 = 0;
    let mut v___x_1199_: u32 = 0;
    let mut v___x_1200_: u8 = 0;
    let mut v___x_1202_: u32 = 0;
    let mut v___x_1203_: u8 = 0;
    let mut v___x_1204_: u32 = 0;
    let mut v___x_1205_: u8 = 0;
    let mut v___x_1206_: u32 = 0;
    let mut v___x_1207_: u8 = 0;
    let mut v___x_1208_: u32 = 0;
    let mut v___x_1209_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1173_ = lean_ctor_get(v_s_1171_, 0);
                v_startInclusive_1174_ = lean_ctor_get(v_s_1171_, 1);
                v_endExclusive_1175_ = lean_ctor_get(v_s_1171_, 2);
                v___x_1176_ = lean_nat_add(v_startInclusive_1174_, v_pos_1172_);
                v___x_1185_ = lean_unsigned_to_nat(0);
                v___x_1186_ = lean_nat_sub(v_endExclusive_1175_, v___x_1176_);
                v___x_1187_ = lean_nat_dec_eq(v___x_1185_, v___x_1186_);
                lean_dec(v___x_1186_);
                if v___x_1187_ == 0 {
                    v___x_1188_ = lean_string_utf8_get_fast(v_str_1173_, v___x_1176_);
                    v___x_1206_ = 65;
                    v___x_1207_ = lean_uint32_dec_le(v___x_1206_, v___x_1188_);
                    if v___x_1207_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        v___x_1208_ = 90;
                        v___x_1209_ = lean_uint32_dec_le(v___x_1188_, v___x_1208_);
                        if v___x_1209_ == 0 {
                            state = 5;
                            continue;
                        } else {
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_1176_);
                    return v_pos_1172_;
                }
            }
            1 => {
                v___x_1178_ = lean_string_utf8_next_fast(v_str_1173_, v___x_1176_);
                v___x_1179_ = lean_nat_sub(v___x_1178_, v___x_1176_);
                lean_dec(v___x_1176_);
                v___x_1180_ = lean_nat_add(v_pos_1172_, v___x_1179_);
                lean_dec(v___x_1179_);
                v___x_1181_ = lean_nat_dec_lt(v_pos_1172_, v___x_1180_);
                if v___x_1181_ == 0 {
                    lean_dec(v___x_1180_);
                    return v_pos_1172_;
                } else {
                    lean_dec(v_pos_1172_);
                    v_pos_1172_ = v___x_1180_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_1184_ == 0 {
                    lean_dec(v___x_1176_);
                    return v_pos_1172_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_1190_ == 0 {
                    v___x_1191_ = 95;
                    v___x_1192_ = lean_uint32_dec_eq(v___x_1188_, v___x_1191_);
                    if v___x_1192_ == 0 {
                        v___x_1193_ = 45;
                        v___x_1194_ = lean_uint32_dec_eq(v___x_1188_, v___x_1193_);
                        v___y_1184_ = v___x_1194_;
                        state = 2;
                        continue;
                    } else {
                        v___y_1184_ = v___x_1192_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            4 => {
                if v___y_1196_ == 0 {
                    v___x_1197_ = 48;
                    v___x_1198_ = lean_uint32_dec_le(v___x_1197_, v___x_1188_);
                    if v___x_1198_ == 0 {
                        v___y_1190_ = v___x_1198_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1199_ = 57;
                        v___x_1200_ = lean_uint32_dec_le(v___x_1188_, v___x_1199_);
                        v___y_1190_ = v___x_1200_;
                        state = 3;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            5 => {
                v___x_1202_ = 97;
                v___x_1203_ = lean_uint32_dec_le(v___x_1202_, v___x_1188_);
                if v___x_1203_ == 0 {
                    v___y_1196_ = v___x_1203_;
                    state = 4;
                    continue;
                } else {
                    v___x_1204_ = 122;
                    v___x_1205_ = lean_uint32_dec_le(v___x_1188_, v___x_1204_);
                    v___y_1196_ = v___x_1205_;
                    state = 4;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0___boxed(
    mut v_s_1210_: *mut LeanObject,
    mut v_pos_1211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1212_: *mut LeanObject = core::ptr::null_mut();
    v_res_1212_ =
        l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0(v_s_1210_, v_pos_1211_);
    lean_dec_ref(v_s_1210_);
    return v_res_1212_;
}
pub unsafe fn l_Lake_Toml_ppSimpleKey(mut v_k_1213_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: u8 = 0;
    v___x_1214_ = lean_unsigned_to_nat(0);
    v___x_1215_ = lean_string_utf8_byte_size(v_k_1213_);
    lean_inc_ref(v_k_1213_);
    v___x_1216_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1216_, 0, v_k_1213_);
    lean_ctor_set(v___x_1216_, 1, v___x_1214_);
    lean_ctor_set(v___x_1216_, 2, v___x_1215_);
    v___x_1217_ = l_String_Slice_Pos_skipWhile___at___00Lake_Toml_ppSimpleKey_spec__0(
        v___x_1216_,
        v___x_1214_,
    );
    lean_dec_ref_known(v___x_1216_, 3);
    v___x_1218_ = lean_nat_dec_eq(v___x_1217_, v___x_1215_);
    lean_dec(v___x_1217_);
    if v___x_1218_ == 0 {
        let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
        v___x_1219_ = l_Lake_Toml_ppString(v_k_1213_);
        return v___x_1219_;
    } else {
        return v_k_1213_;
    }
}
pub unsafe fn l_Lake_Toml_ppKey(mut v_k_1221_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_k_1221_) == 1 {
        let mut v_pre_1222_: *mut LeanObject = core::ptr::null_mut();
        let mut v_str_1223_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1224_: u8 = 0;
        v_pre_1222_ = lean_ctor_get(v_k_1221_, 0);
        lean_inc(v_pre_1222_);
        v_str_1223_ = lean_ctor_get(v_k_1221_, 1);
        lean_inc_ref(v_str_1223_);
        lean_dec_ref_known(v_k_1221_, 2);
        v___x_1224_ = l_Lean_Name_isAnonymous(v_pre_1222_);
        if v___x_1224_ == 0 {
            let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
            v___x_1225_ = l_Lake_Toml_ppKey(v_pre_1222_);
            v___x_1226_ = l_Lake_Toml_ppKey___closed__0;
            v___x_1227_ = lean_string_append(v___x_1225_, v___x_1226_);
            v___x_1228_ = l_Lake_Toml_ppSimpleKey(v_str_1223_);
            v___x_1229_ = lean_string_append(v___x_1227_, v___x_1228_);
            lean_dec_ref(v___x_1228_);
            return v___x_1229_;
        } else {
            let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_pre_1222_);
            v___x_1230_ = l_Lake_Toml_ppSimpleKey(v_str_1223_);
            return v___x_1230_;
        }
    } else {
        let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_k_1221_);
        v___x_1231_ = l_Lake_Toml_instInhabitedValue_default___closed__0;
        return v___x_1231_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(
    mut v_sz_1238_: usize,
    mut v_i_1239_: usize,
    mut v_bs_1240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1241_: u8 = 0;
    let mut v_v_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: usize = 0;
    let mut v___x_1253_: usize = 0;
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1241_ = lean_usize_dec_lt(v_i_1239_, v_sz_1238_);
                if v___x_1241_ == 0 {
                    return v_bs_1240_;
                } else {
                    v_v_1242_ = lean_array_uget_borrowed(v_bs_1240_, v_i_1239_);
                    v_fst_1243_ = lean_ctor_get(v_v_1242_, 0);
                    lean_inc(v_fst_1243_);
                    v_snd_1244_ = lean_ctor_get(v_v_1242_, 1);
                    lean_inc(v_snd_1244_);
                    v___x_1245_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1246_ = lean_array_uset(v_bs_1240_, v_i_1239_, v___x_1245_);
                    v___x_1247_ = l_Lake_Toml_ppKey(v_fst_1243_);
                    v___x_1248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0;
                    v___x_1249_ = lean_string_append(v___x_1247_, v___x_1248_);
                    v___x_1250_ = l_Lake_Toml_Value_toString(v_snd_1244_);
                    v___x_1251_ = lean_string_append(v___x_1249_, v___x_1250_);
                    lean_dec_ref(v___x_1250_);
                    v___x_1252_ = 1usize;
                    v___x_1253_ = lean_usize_add(v_i_1239_, v___x_1252_);
                    v___x_1254_ = lean_array_uset(v_bs_x27_1246_, v_i_1239_, v___x_1251_);
                    v_i_1239_ = v___x_1253_;
                    v_bs_1240_ = v___x_1254_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_ppInlineTable(mut v_t_1258_: *mut LeanObject) -> *mut LeanObject {
    let mut v_items_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1260_: usize = 0;
    let mut v___x_1261_: usize = 0;
    let mut v_xs_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    v_items_1259_ = lean_ctor_get(v_t_1258_, 0);
    lean_inc_ref(v_items_1259_);
    lean_dec_ref(v_t_1258_);
    v_sz_1260_ = lean_array_size(v_items_1259_);
    v___x_1261_ = 0usize;
    v_xs_1262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(v_sz_1260_, v___x_1261_, v_items_1259_);
    v___x_1263_ = l_Lake_Toml_ppInlineTable___closed__0;
    v___x_1264_ = l_Lake_Toml_ppInlineArray___closed__1;
    v___x_1265_ = lean_array_to_list(v_xs_1262_);
    v___x_1266_ = l_String_intercalate(v___x_1264_, v___x_1265_);
    v___x_1267_ = lean_string_append(v___x_1263_, v___x_1266_);
    lean_dec_ref(v___x_1266_);
    v___x_1268_ = l_Lake_Toml_ppInlineTable___closed__1;
    v___x_1269_ = lean_string_append(v___x_1267_, v___x_1268_);
    return v___x_1269_;
}
pub unsafe fn l_Lake_Toml_Value_toString(mut v_v_1270_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_v_1270_) {
        0 => {
            let mut v_s_1271_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
            v_s_1271_ = lean_ctor_get(v_v_1270_, 1);
            lean_inc_ref(v_s_1271_);
            lean_dec_ref_known(v_v_1270_, 2);
            v___x_1272_ = l_Lake_Toml_ppString(v_s_1271_);
            return v___x_1272_;
        }
        1 => {
            let mut v_n_1273_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
            v_n_1273_ = lean_ctor_get(v_v_1270_, 1);
            lean_inc(v_n_1273_);
            lean_dec_ref_known(v_v_1270_, 2);
            v___x_1274_ = l_Int_repr(v_n_1273_);
            lean_dec(v_n_1273_);
            return v___x_1274_;
        }
        2 => {
            let mut v_n_1275_: f64 = 0.0;
            let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
            v_n_1275_ = lean_ctor_get_float(
                v_v_1270_,
                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            );
            lean_dec_ref_known(v_v_1270_, 1);
            v___x_1276_ = lean_float_to_string(v_n_1275_);
            return v___x_1276_;
        }
        3 => {
            let mut v_b_1277_: u8 = 0;
            v_b_1277_ = lean_ctor_get_uint8(
                v_v_1270_,
                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            );
            lean_dec_ref_known(v_v_1270_, 1);
            if v_b_1277_ == 0 {
                let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
                v___x_1278_ = l_Lake_Toml_Value_toString___closed__0;
                return v___x_1278_;
            } else {
                let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
                v___x_1279_ = l_Lake_Toml_Value_toString___closed__1;
                return v___x_1279_;
            }
        }
        4 => {
            let mut v_dt_1280_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
            v_dt_1280_ = lean_ctor_get(v_v_1270_, 1);
            lean_inc_ref(v_dt_1280_);
            lean_dec_ref_known(v_v_1270_, 2);
            v___x_1281_ = l_Lake_Toml_DateTime_toString(v_dt_1280_);
            return v___x_1281_;
        }
        5 => {
            let mut v_xs_1282_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
            v_xs_1282_ = lean_ctor_get(v_v_1270_, 1);
            lean_inc_ref(v_xs_1282_);
            lean_dec_ref_known(v_v_1270_, 2);
            v___x_1283_ = l_Lake_Toml_ppInlineArray(v_xs_1282_);
            return v___x_1283_;
        }
        _ => {
            let mut v_xs_1284_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
            v_xs_1284_ = lean_ctor_get(v_v_1270_, 1);
            lean_inc_ref(v_xs_1284_);
            lean_dec_ref_known(v_v_1270_, 2);
            v___x_1285_ = l_Lake_Toml_ppInlineTable(v_xs_1284_);
            return v___x_1285_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(
    mut v_sz_1286_: usize,
    mut v_i_1287_: usize,
    mut v_bs_1288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1289_: u8 = 0;
    let mut v_v_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: usize = 0;
    let mut v___x_1295_: usize = 0;
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1289_ = lean_usize_dec_lt(v_i_1287_, v_sz_1286_);
                if v___x_1289_ == 0 {
                    return v_bs_1288_;
                } else {
                    v_v_1290_ = lean_array_uget(v_bs_1288_, v_i_1287_);
                    v___x_1291_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1292_ = lean_array_uset(v_bs_1288_, v_i_1287_, v___x_1291_);
                    v___x_1293_ = l_Lake_Toml_Value_toString(v_v_1290_);
                    v___x_1294_ = 1usize;
                    v___x_1295_ = lean_usize_add(v_i_1287_, v___x_1294_);
                    v___x_1296_ = lean_array_uset(v_bs_x27_1292_, v_i_1287_, v___x_1293_);
                    v_i_1287_ = v___x_1295_;
                    v_bs_1288_ = v___x_1296_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_ppInlineArray(mut v_vs_1298_: *mut LeanObject) -> *mut LeanObject {
    let mut v_sz_1299_: usize = 0;
    let mut v___x_1300_: usize = 0;
    let mut v_xs_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    v_sz_1299_ = lean_array_size(v_vs_1298_);
    v___x_1300_ = 0usize;
    v_xs_1301_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(v_sz_1299_, v___x_1300_, v_vs_1298_);
    v___x_1302_ = l_Lake_Toml_ppInlineArray___closed__0;
    v___x_1303_ = l_Lake_Toml_ppInlineArray___closed__1;
    v___x_1304_ = lean_array_to_list(v_xs_1301_);
    v___x_1305_ = l_String_intercalate(v___x_1303_, v___x_1304_);
    v___x_1306_ = lean_string_append(v___x_1302_, v___x_1305_);
    lean_dec_ref(v___x_1305_);
    v___x_1307_ = l_Lake_Toml_ppInlineArray___closed__2;
    v___x_1308_ = lean_string_append(v___x_1306_, v___x_1307_);
    return v___x_1308_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3___boxed(
    mut v_sz_1309_: *mut LeanObject,
    mut v_i_1310_: *mut LeanObject,
    mut v_bs_1311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1312_: usize = 0;
    let mut v_i_boxed_1313_: usize = 0;
    let mut v_res_1314_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1312_ = lean_unbox_usize(v_sz_1309_);
    lean_dec(v_sz_1309_);
    v_i_boxed_1313_ = lean_unbox_usize(v_i_1310_);
    lean_dec(v_i_1310_);
    v_res_1314_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineArray_spec__3(v_sz_boxed_1312_, v_i_boxed_1313_, v_bs_1311_);
    return v_res_1314_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___boxed(
    mut v_sz_1315_: *mut LeanObject,
    mut v_i_1316_: *mut LeanObject,
    mut v_bs_1317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1318_: usize = 0;
    let mut v_i_boxed_1319_: usize = 0;
    let mut v_res_1320_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1318_ = lean_unbox_usize(v_sz_1315_);
    lean_dec(v_sz_1315_);
    v_i_boxed_1319_ = lean_unbox_usize(v_i_1316_);
    lean_dec(v_i_1316_);
    v_res_1320_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0(v_sz_boxed_1318_, v_i_boxed_1319_, v_bs_1317_);
    return v_res_1320_;
}
pub unsafe fn l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(
    mut v_s_1324_: *mut LeanObject,
    mut v_k_1325_: *mut LeanObject,
    mut v_v_1326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    v___x_1327_ = l_Lake_Toml_ppKey(v_k_1325_);
    v___x_1328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0;
    v___x_1329_ = lean_string_append(v___x_1327_, v___x_1328_);
    v___x_1330_ = l_Lake_Toml_Value_toString(v_v_1326_);
    v___x_1331_ = lean_string_append(v___x_1329_, v___x_1330_);
    lean_dec_ref(v___x_1330_);
    v___x_1332_ = l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval___closed__0;
    v___x_1333_ = lean_string_append(v___x_1331_, v___x_1332_);
    v___x_1334_ = lean_string_append(v_s_1324_, v___x_1333_);
    lean_dec_ref(v___x_1333_);
    return v___x_1334_;
}
pub unsafe fn l_panic___at___00Lake_Toml_ppTable_spec__2(
    mut v_msg_1335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    v___x_1336_ = l_Lake_Toml_instInhabitedValue_default___closed__0;
    v___x_1337_ = lean_panic_fn_borrowed(v___x_1336_, v_msg_1335_);
    return v___x_1337_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(
    mut v_as_1338_: *mut LeanObject,
    mut v_i_1339_: usize,
    mut v_stop_1340_: usize,
    mut v_b_1341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1342_: u8 = 0;
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: usize = 0;
    let mut v___x_1348_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1342_ = lean_usize_dec_eq(v_i_1339_, v_stop_1340_);
                if v___x_1342_ == 0 {
                    v___x_1343_ = lean_array_uget_borrowed(v_as_1338_, v_i_1339_);
                    v_fst_1344_ = lean_ctor_get(v___x_1343_, 0);
                    v_snd_1345_ = lean_ctor_get(v___x_1343_, 1);
                    lean_inc(v_snd_1345_);
                    lean_inc(v_fst_1344_);
                    v___x_1346_ =
                        l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(
                            v_b_1341_,
                            v_fst_1344_,
                            v_snd_1345_,
                        );
                    v___x_1347_ = 1usize;
                    v___x_1348_ = lean_usize_add(v_i_1339_, v___x_1347_);
                    v_i_1339_ = v___x_1348_;
                    v_b_1341_ = v___x_1346_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1341_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1___boxed(
    mut v_as_1350_: *mut LeanObject,
    mut v_i_1351_: *mut LeanObject,
    mut v_stop_1352_: *mut LeanObject,
    mut v_b_1353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1354_: usize = 0;
    let mut v_stop_boxed_1355_: usize = 0;
    let mut v_res_1356_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1354_ = lean_unbox_usize(v_i_1351_);
    lean_dec(v_i_1351_);
    v_stop_boxed_1355_ = lean_unbox_usize(v_stop_1352_);
    lean_dec(v_stop_1352_);
    v_res_1356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_as_1350_, v_i_boxed_1354_, v_stop_boxed_1355_, v_b_1353_);
    lean_dec_ref(v_as_1350_);
    return v_res_1356_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5()
-> *mut LeanObject {
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    v___x_1362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__4;
    v___x_1363_ = lean_unsigned_to_nat(17);
    v___x_1364_ = lean_unsigned_to_nat(128);
    v___x_1365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__3;
    v___x_1366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__2;
    v___x_1367_ = l_mkPanicMessageWithDecl(
        v___x_1366_,
        v___x_1365_,
        v___x_1364_,
        v___x_1363_,
        v___x_1362_,
    );
    return v___x_1367_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(
    mut v_fst_1368_: *mut LeanObject,
    mut v_as_1369_: *mut LeanObject,
    mut v_i_1370_: usize,
    mut v_stop_1371_: usize,
    mut v_b_1372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: usize = 0;
    let mut v___x_1376_: usize = 0;
    let mut v___y_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: u32 = 0;
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: u8 = 0;
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_items_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: u8 = 0;
    let mut v___x_1395_: u8 = 0;
    let mut v___x_1396_: usize = 0;
    let mut v___x_1397_: usize = 0;
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: usize = 0;
    let mut v___x_1400_: usize = 0;
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1382_ = lean_usize_dec_eq(v_i_1370_, v_stop_1371_);
                if v___x_1382_ == 0 {
                    v___x_1383_ = lean_array_uget_borrowed(v_as_1369_, v_i_1370_);
                    if lean_obj_tag(v___x_1383_) == 6 {
                        v_xs_1384_ = lean_ctor_get(v___x_1383_, 1);
                        v_items_1385_ = lean_ctor_get(v_xs_1384_, 0);
                        v___x_1386_ = lean_unsigned_to_nat(0);
                        v___x_1387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__0;
                        lean_inc(v_fst_1368_);
                        v___x_1388_ = l_Lake_Toml_ppKey(v_fst_1368_);
                        v___x_1389_ = lean_string_append(v___x_1387_, v___x_1388_);
                        lean_dec_ref(v___x_1388_);
                        v___x_1390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__1;
                        v___x_1391_ = lean_string_append(v___x_1389_, v___x_1390_);
                        v_s_1392_ = lean_string_append(v_b_1372_, v___x_1391_);
                        lean_dec_ref(v___x_1391_);
                        v___x_1393_ = lean_array_get_size(v_items_1385_);
                        v___x_1394_ = lean_nat_dec_lt(v___x_1386_, v___x_1393_);
                        if v___x_1394_ == 0 {
                            v___y_1379_ = v_s_1392_;
                            state = 2;
                            continue;
                        } else {
                            v___x_1395_ = lean_nat_dec_le(v___x_1393_, v___x_1393_);
                            if v___x_1395_ == 0 {
                                if v___x_1394_ == 0 {
                                    v___y_1379_ = v_s_1392_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_1396_ = 0usize;
                                    v___x_1397_ = lean_usize_of_nat(v___x_1393_);
                                    v___x_1398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_1385_, v___x_1396_, v___x_1397_, v_s_1392_);
                                    v___y_1379_ = v___x_1398_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v___x_1399_ = 0usize;
                                v___x_1400_ = lean_usize_of_nat(v___x_1393_);
                                v___x_1401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_1385_, v___x_1399_, v___x_1400_, v_s_1392_);
                                v___y_1379_ = v___x_1401_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_b_1372_);
                        v___x_1402_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___closed__5);
                        v___x_1403_ = l_panic___at___00Lake_Toml_ppTable_spec__2(v___x_1402_);
                        v___y_1374_ = v___x_1403_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_1368_);
                    return v_b_1372_;
                }
            }
            1 => {
                v___x_1375_ = 1usize;
                v___x_1376_ = lean_usize_add(v_i_1370_, v___x_1375_);
                v_i_1370_ = v___x_1376_;
                v_b_1372_ = v___y_1374_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1380_ = 10;
                v___x_1381_ = lean_string_push(v___y_1379_, v___x_1380_);
                v___y_1374_ = v___x_1381_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3___boxed(
    mut v_fst_1404_: *mut LeanObject,
    mut v_as_1405_: *mut LeanObject,
    mut v_i_1406_: *mut LeanObject,
    mut v_stop_1407_: *mut LeanObject,
    mut v_b_1408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1409_: usize = 0;
    let mut v_stop_boxed_1410_: usize = 0;
    let mut v_res_1411_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1409_ = lean_unbox_usize(v_i_1406_);
    lean_dec(v_i_1406_);
    v_stop_boxed_1410_ = lean_unbox_usize(v_stop_1407_);
    lean_dec(v_stop_1407_);
    v_res_1411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(v_fst_1404_, v_as_1405_, v_i_boxed_1409_, v_stop_boxed_1410_, v_b_1408_);
    lean_dec_ref(v_as_1405_);
    return v_res_1411_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(
    mut v___x_1412_: *mut LeanObject,
    mut v_as_1413_: *mut LeanObject,
    mut v_i_1414_: usize,
    mut v_stop_1415_: usize,
) -> u8 {
    let mut v___x_1416_: u8 = 0;
    let mut v___x_1417_: u8 = 0;
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: u8 = 0;
    let mut v___x_1421_: usize = 0;
    let mut v___x_1422_: usize = 0;
    let mut v___x_1424_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1416_ = lean_usize_dec_eq(v_i_1414_, v_stop_1415_);
                if v___x_1416_ == 0 {
                    v___x_1417_ = 1;
                    v___x_1418_ = lean_array_uget_borrowed(v_as_1413_, v_i_1414_);
                    if lean_obj_tag(v___x_1418_) == 6 {
                        v___x_1419_ = lean_unsigned_to_nat(0);
                        v___x_1420_ = lean_nat_dec_eq(v___x_1412_, v___x_1419_);
                        if v___x_1420_ == 0 {
                            v___x_1421_ = 1usize;
                            v___x_1422_ = lean_usize_add(v_i_1414_, v___x_1421_);
                            v_i_1414_ = v___x_1422_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_1417_;
                        }
                    } else {
                        return v___x_1417_;
                    }
                } else {
                    v___x_1424_ = 0;
                    return v___x_1424_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4___boxed(
    mut v___x_1425_: *mut LeanObject,
    mut v_as_1426_: *mut LeanObject,
    mut v_i_1427_: *mut LeanObject,
    mut v_stop_1428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1429_: usize = 0;
    let mut v_stop_boxed_1430_: usize = 0;
    let mut v_res_1431_: u8 = 0;
    let mut v_r_1432_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1429_ = lean_unbox_usize(v_i_1427_);
    lean_dec(v_i_1427_);
    v_stop_boxed_1430_ = lean_unbox_usize(v_stop_1428_);
    lean_dec(v_stop_1428_);
    v_res_1431_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(v___x_1425_, v_as_1426_, v_i_boxed_1429_, v_stop_boxed_1430_);
    lean_dec_ref(v_as_1426_);
    lean_dec(v___x_1425_);
    v_r_1432_ = lean_box((v_res_1431_) as usize);
    return v_r_1432_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(
    mut v_as_1435_: *mut LeanObject,
    mut v_i_1436_: usize,
    mut v_stop_1437_: usize,
    mut v_b_1438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: usize = 0;
    let mut v___x_1442_: usize = 0;
    let mut v___x_1444_: u8 = 0;
    let mut v_fst_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: u32 = 0;
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1457_: u8 = 0;
    let mut v_xs_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: u8 = 0;
    let mut v___x_1463_: u8 = 0;
    let mut v___x_1464_: usize = 0;
    let mut v___x_1465_: usize = 0;
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: usize = 0;
    let mut v___x_1471_: usize = 0;
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: u8 = 0;
    let mut v___x_1477_: u8 = 0;
    let mut v___x_1478_: usize = 0;
    let mut v___x_1479_: usize = 0;
    let mut v___x_1480_: u8 = 0;
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1483_: u8 = 0;
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1495_: u8 = 0;
    let mut v_unused_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1500_: u8 = 0;
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1508_: u8 = 0;
    let mut v_unused_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1511_: u8 = 0;
    let mut v_unused_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_items_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fs_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: u8 = 0;
    let mut v___x_1525_: u8 = 0;
    let mut v___x_1526_: usize = 0;
    let mut v___x_1527_: usize = 0;
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: usize = 0;
    let mut v___x_1530_: usize = 0;
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1535_: u8 = 0;
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1540_: u8 = 0;
    let mut v_unused_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1444_ = lean_usize_dec_eq(v_i_1436_, v_stop_1437_);
                if v___x_1444_ == 0 {
                    v_fst_1445_ = lean_ctor_get(v_b_1438_, 0);
                    v_snd_1446_ = lean_ctor_get(v_b_1438_, 1);
                    v___x_1452_ = lean_array_uget(v_as_1435_, v_i_1436_);
                    v_snd_1453_ = lean_ctor_get(v___x_1452_, 1);
                    match lean_obj_tag(v_snd_1453_) {
                        5 => {
                            lean_inc_ref(v_snd_1453_);
                            v_fst_1454_ = lean_ctor_get(v___x_1452_, 0);
                            v_isSharedCheck_1511_ = (!lean_is_exclusive(v___x_1452_)) as u8;
                            if v_isSharedCheck_1511_ == 0 {
                                v_unused_1512_ = lean_ctor_get(v___x_1452_, 1);
                                lean_dec(v_unused_1512_);
                                v___x_1456_ = v___x_1452_;
                                v_isShared_1457_ = v_isSharedCheck_1511_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_fst_1454_);
                                lean_dec(v___x_1452_);
                                v___x_1456_ = lean_box(0);
                                v_isShared_1457_ = v_isSharedCheck_1511_;
                                state = 3;
                                continue;
                            }
                        }
                        6 => {
                            lean_inc(v_snd_1446_);
                            lean_inc(v_fst_1445_);
                            lean_dec_ref(v_b_1438_);
                            v_xs_1513_ = lean_ctor_get(v_snd_1453_, 1);
                            lean_inc_ref(v_xs_1513_);
                            v_fst_1514_ = lean_ctor_get(v___x_1452_, 0);
                            lean_inc(v_fst_1514_);
                            lean_dec(v___x_1452_);
                            v_items_1515_ = lean_ctor_get(v_xs_1513_, 0);
                            lean_inc_ref(v_items_1515_);
                            lean_dec_ref(v_xs_1513_);
                            v___x_1516_ = l_Lake_Toml_ppInlineArray___closed__0;
                            v___x_1517_ = l_Lake_Toml_ppKey(v_fst_1514_);
                            v___x_1518_ = lean_string_append(v___x_1516_, v___x_1517_);
                            lean_dec_ref(v___x_1517_);
                            v___x_1519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__1;
                            v___x_1520_ = lean_string_append(v___x_1518_, v___x_1519_);
                            v_fs_1521_ = lean_string_append(v_snd_1446_, v___x_1520_);
                            lean_dec_ref(v___x_1520_);
                            v___x_1522_ = lean_unsigned_to_nat(0);
                            v___x_1523_ = lean_array_get_size(v_items_1515_);
                            v___x_1524_ = lean_nat_dec_lt(v___x_1522_, v___x_1523_);
                            if v___x_1524_ == 0 {
                                lean_dec_ref(v_items_1515_);
                                v___y_1448_ = v_fs_1521_;
                                state = 2;
                                continue;
                            } else {
                                v___x_1525_ = lean_nat_dec_le(v___x_1523_, v___x_1523_);
                                if v___x_1525_ == 0 {
                                    if v___x_1524_ == 0 {
                                        lean_dec_ref(v_items_1515_);
                                        v___y_1448_ = v_fs_1521_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_1526_ = 0usize;
                                        v___x_1527_ = lean_usize_of_nat(v___x_1523_);
                                        v___x_1528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_1515_, v___x_1526_, v___x_1527_, v_fs_1521_);
                                        lean_dec_ref(v_items_1515_);
                                        v___y_1448_ = v___x_1528_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v___x_1529_ = 0usize;
                                    v___x_1530_ = lean_usize_of_nat(v___x_1523_);
                                    v___x_1531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__1(v_items_1515_, v___x_1529_, v___x_1530_, v_fs_1521_);
                                    lean_dec_ref(v_items_1515_);
                                    v___y_1448_ = v___x_1531_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            lean_inc(v_snd_1453_);
                            lean_inc(v_snd_1446_);
                            lean_inc(v_fst_1445_);
                            lean_dec_ref(v_b_1438_);
                            v_fst_1532_ = lean_ctor_get(v___x_1452_, 0);
                            v_isSharedCheck_1540_ = (!lean_is_exclusive(v___x_1452_)) as u8;
                            if v_isSharedCheck_1540_ == 0 {
                                v_unused_1541_ = lean_ctor_get(v___x_1452_, 1);
                                lean_dec(v_unused_1541_);
                                v___x_1534_ = v___x_1452_;
                                v_isShared_1535_ = v_isSharedCheck_1540_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_fst_1532_);
                                lean_dec(v___x_1452_);
                                v___x_1534_ = lean_box(0);
                                v_isShared_1535_ = v_isSharedCheck_1540_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                } else {
                    return v_b_1438_;
                }
            }
            1 => {
                v___x_1441_ = 1usize;
                v___x_1442_ = lean_usize_add(v_i_1436_, v___x_1441_);
                v_i_1436_ = v___x_1442_;
                v_b_1438_ = v___y_1440_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1449_ = 10;
                v___x_1450_ = lean_string_push(v___y_1448_, v___x_1449_);
                v___x_1451_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1451_, 0, v_fst_1445_);
                lean_ctor_set(v___x_1451_, 1, v___x_1450_);
                v___y_1440_ = v___x_1451_;
                state = 1;
                continue;
            }
            3 => {
                v_xs_1458_ = lean_ctor_get(v_snd_1453_, 1);
                lean_inc_ref(v_xs_1458_);
                lean_dec_ref_known(v_snd_1453_, 2);
                v___x_1459_ = lean_array_get_size(v_xs_1458_);
                v___x_1460_ = lean_unsigned_to_nat(0);
                v___x_1476_ = lean_nat_dec_eq(v___x_1459_, v___x_1460_);
                if v___x_1476_ == 0 {
                    v___x_1477_ = lean_nat_dec_lt(v___x_1460_, v___x_1459_);
                    if v___x_1477_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        if v___x_1477_ == 0 {
                            state = 4;
                            continue;
                        } else {
                            v___x_1478_ = 0usize;
                            v___x_1479_ = lean_usize_of_nat(v___x_1459_);
                            v___x_1480_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Toml_ppTable_spec__4(v___x_1459_, v_xs_1458_, v___x_1478_, v___x_1479_);
                            if v___x_1480_ == 0 {
                                state = 4;
                                continue;
                            } else {
                                if v___x_1476_ == 0 {
                                    lean_inc(v_snd_1446_);
                                    lean_inc(v_fst_1445_);
                                    lean_del_object(v___x_1456_);
                                    v_isSharedCheck_1495_ = (!lean_is_exclusive(v_b_1438_)) as u8;
                                    if v_isSharedCheck_1495_ == 0 {
                                        v_unused_1496_ = lean_ctor_get(v_b_1438_, 1);
                                        lean_dec(v_unused_1496_);
                                        v_unused_1497_ = lean_ctor_get(v_b_1438_, 0);
                                        lean_dec(v_unused_1497_);
                                        v___x_1482_ = v_b_1438_;
                                        v_isShared_1483_ = v_isSharedCheck_1495_;
                                        state = 7;
                                        continue;
                                    } else {
                                        lean_dec(v_b_1438_);
                                        v___x_1482_ = lean_box(0);
                                        v_isShared_1483_ = v_isSharedCheck_1495_;
                                        state = 7;
                                        continue;
                                    }
                                } else {
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_inc(v_snd_1446_);
                    lean_inc(v_fst_1445_);
                    lean_dec_ref(v_xs_1458_);
                    lean_del_object(v___x_1456_);
                    v_isSharedCheck_1508_ = (!lean_is_exclusive(v_b_1438_)) as u8;
                    if v_isSharedCheck_1508_ == 0 {
                        v_unused_1509_ = lean_ctor_get(v_b_1438_, 1);
                        lean_dec(v_unused_1509_);
                        v_unused_1510_ = lean_ctor_get(v_b_1438_, 0);
                        lean_dec(v_unused_1510_);
                        v___x_1499_ = v_b_1438_;
                        v_isShared_1500_ = v_isSharedCheck_1508_;
                        state = 9;
                        continue;
                    } else {
                        lean_dec(v_b_1438_);
                        v___x_1499_ = lean_box(0);
                        v_isShared_1500_ = v_isSharedCheck_1508_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1462_ = lean_nat_dec_lt(v___x_1460_, v___x_1459_);
                if v___x_1462_ == 0 {
                    lean_dec_ref(v_xs_1458_);
                    lean_del_object(v___x_1456_);
                    lean_dec(v_fst_1454_);
                    v___y_1440_ = v_b_1438_;
                    state = 1;
                    continue;
                } else {
                    v___x_1463_ = lean_nat_dec_le(v___x_1459_, v___x_1459_);
                    if v___x_1463_ == 0 {
                        if v___x_1462_ == 0 {
                            lean_dec_ref(v_xs_1458_);
                            lean_del_object(v___x_1456_);
                            lean_dec(v_fst_1454_);
                            v___y_1440_ = v_b_1438_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snd_1446_);
                            lean_inc(v_fst_1445_);
                            lean_dec_ref(v_b_1438_);
                            v___x_1464_ = 0usize;
                            v___x_1465_ = lean_usize_of_nat(v___x_1459_);
                            v___x_1466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(v_fst_1454_, v_xs_1458_, v___x_1464_, v___x_1465_, v_snd_1446_);
                            lean_dec_ref(v_xs_1458_);
                            if v_isShared_1457_ == 0 {
                                lean_ctor_set(v___x_1456_, 1, v___x_1466_);
                                lean_ctor_set(v___x_1456_, 0, v_fst_1445_);
                                v___x_1468_ = v___x_1456_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_fst_1445_);
                                lean_ctor_set(v_reuseFailAlloc_1469_, 1, v___x_1466_);
                                v___x_1468_ = v_reuseFailAlloc_1469_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_inc(v_snd_1446_);
                        lean_inc(v_fst_1445_);
                        lean_dec_ref(v_b_1438_);
                        v___x_1470_ = 0usize;
                        v___x_1471_ = lean_usize_of_nat(v___x_1459_);
                        v___x_1472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__3(v_fst_1454_, v_xs_1458_, v___x_1470_, v___x_1471_, v_snd_1446_);
                        lean_dec_ref(v_xs_1458_);
                        if v_isShared_1457_ == 0 {
                            lean_ctor_set(v___x_1456_, 1, v___x_1472_);
                            lean_ctor_set(v___x_1456_, 0, v_fst_1445_);
                            v___x_1474_ = v___x_1456_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_fst_1445_);
                            lean_ctor_set(v_reuseFailAlloc_1475_, 1, v___x_1472_);
                            v___x_1474_ = v_reuseFailAlloc_1475_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v___y_1440_ = v___x_1468_;
                state = 1;
                continue;
            }
            6 => {
                v___y_1440_ = v___x_1474_;
                state = 1;
                continue;
            }
            7 => {
                v___x_1484_ = l_Lake_Toml_ppKey(v_fst_1454_);
                v___x_1485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_ppInlineTable_spec__0___closed__0;
                v___x_1486_ = lean_string_append(v___x_1484_, v___x_1485_);
                v___x_1487_ = l_Lake_Toml_ppInlineArray(v_xs_1458_);
                v___x_1488_ = lean_string_append(v___x_1486_, v___x_1487_);
                lean_dec_ref(v___x_1487_);
                v___x_1489_ =
                    l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval___closed__0;
                v___x_1490_ = lean_string_append(v___x_1488_, v___x_1489_);
                v___x_1491_ = lean_string_append(v_fst_1445_, v___x_1490_);
                lean_dec_ref(v___x_1490_);
                if v_isShared_1483_ == 0 {
                    lean_ctor_set(v___x_1482_, 0, v___x_1491_);
                    v___x_1493_ = v___x_1482_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
                    lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_snd_1446_);
                    v___x_1493_ = v_reuseFailAlloc_1494_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___y_1440_ = v___x_1493_;
                state = 1;
                continue;
            }
            9 => {
                v___x_1501_ = l_Lake_Toml_ppKey(v_fst_1454_);
                v___x_1502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___closed__0;
                v___x_1503_ = lean_string_append(v___x_1501_, v___x_1502_);
                v___x_1504_ = lean_string_append(v_fst_1445_, v___x_1503_);
                lean_dec_ref(v___x_1503_);
                if v_isShared_1500_ == 0 {
                    lean_ctor_set(v___x_1499_, 0, v___x_1504_);
                    v___x_1506_ = v___x_1499_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
                    lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_snd_1446_);
                    v___x_1506_ = v_reuseFailAlloc_1507_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___y_1440_ = v___x_1506_;
                state = 1;
                continue;
            }
            11 => {
                v___x_1536_ = l___private_Lake_Toml_Data_Value_0__Lake_Toml_ppTable_appendKeyval(
                    v_fst_1445_,
                    v_fst_1532_,
                    v_snd_1453_,
                );
                if v_isShared_1535_ == 0 {
                    lean_ctor_set(v___x_1534_, 1, v_snd_1446_);
                    lean_ctor_set(v___x_1534_, 0, v___x_1536_);
                    v___x_1538_ = v___x_1534_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
                    lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_snd_1446_);
                    v___x_1538_ = v_reuseFailAlloc_1539_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___y_1440_ = v___x_1538_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5___boxed(
    mut v_as_1542_: *mut LeanObject,
    mut v_i_1543_: *mut LeanObject,
    mut v_stop_1544_: *mut LeanObject,
    mut v_b_1545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1546_: usize = 0;
    let mut v_stop_boxed_1547_: usize = 0;
    let mut v_res_1548_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1546_ = lean_unbox_usize(v_i_1543_);
    lean_dec(v_i_1543_);
    v_stop_boxed_1547_ = lean_unbox_usize(v_stop_1544_);
    lean_dec(v_stop_1544_);
    v_res_1548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_as_1542_, v_i_boxed_1546_, v_stop_boxed_1547_, v_b_1545_);
    lean_dec_ref(v_as_1542_);
    return v_res_1548_;
}
pub unsafe fn l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0(
    mut v_s_1549_: *mut LeanObject,
    mut v_pos_1550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: u8 = 0;
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: u8 = 0;
    let mut v___y_1565_: u8 = 0;
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: u32 = 0;
    let mut v___y_1569_: u8 = 0;
    let mut v___x_1570_: u32 = 0;
    let mut v___x_1571_: u8 = 0;
    let mut v___x_1572_: u32 = 0;
    let mut v___x_1573_: u8 = 0;
    let mut v___x_1574_: u32 = 0;
    let mut v___x_1575_: u8 = 0;
    let mut v___x_1576_: u32 = 0;
    let mut v___x_1577_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1551_ = lean_ctor_get(v_s_1549_, 0);
                v_startInclusive_1552_ = lean_ctor_get(v_s_1549_, 1);
                v___x_1553_ = lean_nat_add(v_startInclusive_1552_, v_pos_1550_);
                v___x_1554_ = lean_nat_sub(v___x_1553_, v_startInclusive_1552_);
                v___x_1555_ = lean_unsigned_to_nat(0);
                v___x_1556_ = lean_nat_dec_eq(v___x_1554_, v___x_1555_);
                if v___x_1556_ == 0 {
                    lean_inc(v_startInclusive_1552_);
                    lean_inc_ref(v_str_1551_);
                    v___x_1557_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1557_, 0, v_str_1551_);
                    lean_ctor_set(v___x_1557_, 1, v_startInclusive_1552_);
                    lean_ctor_set(v___x_1557_, 2, v___x_1553_);
                    v___x_1558_ = lean_unsigned_to_nat(1);
                    v___x_1559_ = lean_nat_sub(v___x_1554_, v___x_1558_);
                    lean_dec(v___x_1554_);
                    v___x_1560_ = l_String_Slice_posLE(v___x_1557_, v___x_1559_);
                    lean_dec_ref_known(v___x_1557_, 3);
                    v___x_1566_ = lean_nat_add(v_startInclusive_1552_, v___x_1560_);
                    v___x_1567_ = lean_string_utf8_get_fast(v_str_1551_, v___x_1566_);
                    lean_dec(v___x_1566_);
                    v___x_1574_ = 32;
                    v___x_1575_ = lean_uint32_dec_eq(v___x_1567_, v___x_1574_);
                    if v___x_1575_ == 0 {
                        v___x_1576_ = 9;
                        v___x_1577_ = lean_uint32_dec_eq(v___x_1567_, v___x_1576_);
                        v___y_1569_ = v___x_1577_;
                        state = 3;
                        continue;
                    } else {
                        v___y_1569_ = v___x_1575_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1554_);
                    lean_dec(v___x_1553_);
                    return v_pos_1550_;
                }
            }
            1 => {
                v___x_1562_ = lean_nat_dec_lt(v___x_1560_, v_pos_1550_);
                if v___x_1562_ == 0 {
                    lean_dec(v___x_1560_);
                    return v_pos_1550_;
                } else {
                    lean_dec(v_pos_1550_);
                    v_pos_1550_ = v___x_1560_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_1565_ == 0 {
                    lean_dec(v___x_1560_);
                    return v_pos_1550_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_1569_ == 0 {
                    v___x_1570_ = 13;
                    v___x_1571_ = lean_uint32_dec_eq(v___x_1567_, v___x_1570_);
                    if v___x_1571_ == 0 {
                        v___x_1572_ = 10;
                        v___x_1573_ = lean_uint32_dec_eq(v___x_1567_, v___x_1572_);
                        v___y_1565_ = v___x_1573_;
                        state = 2;
                        continue;
                    } else {
                        v___y_1565_ = v___x_1571_;
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
pub unsafe fn l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0___boxed(
    mut v_s_1578_: *mut LeanObject,
    mut v_pos_1579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1580_: *mut LeanObject = core::ptr::null_mut();
    v_res_1580_ =
        l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0(v_s_1578_, v_pos_1579_);
    lean_dec_ref(v_s_1578_);
    return v_res_1580_;
}
pub unsafe fn l_Lake_Toml_ppTable(mut v_t_1583_: *mut LeanObject) -> *mut LeanObject {
    let mut v_fst_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: u32 = 0;
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_items_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: u8 = 0;
    let mut v___x_1606_: u8 = 0;
    let mut v___x_1607_: usize = 0;
    let mut v___x_1608_: usize = 0;
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: usize = 0;
    let mut v___x_1611_: usize = 0;
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1600_ = l_Lake_Toml_instInhabitedValue_default___closed__0;
                v___x_1601_ = l_Lake_Toml_ppTable___closed__0;
                v_items_1602_ = lean_ctor_get(v_t_1583_, 0);
                v___x_1603_ = lean_unsigned_to_nat(0);
                v___x_1604_ = lean_array_get_size(v_items_1602_);
                v___x_1605_ = lean_nat_dec_lt(v___x_1603_, v___x_1604_);
                if v___x_1605_ == 0 {
                    v_fst_1585_ = v___x_1600_;
                    v_snd_1586_ = v___x_1600_;
                    state = 1;
                    continue;
                } else {
                    v___x_1606_ = lean_nat_dec_le(v___x_1604_, v___x_1604_);
                    if v___x_1606_ == 0 {
                        if v___x_1605_ == 0 {
                            v_fst_1585_ = v___x_1600_;
                            v_snd_1586_ = v___x_1600_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1607_ = 0usize;
                            v___x_1608_ = lean_usize_of_nat(v___x_1604_);
                            v___x_1609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_items_1602_, v___x_1607_, v___x_1608_, v___x_1601_);
                            v___y_1597_ = v___x_1609_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_1610_ = 0usize;
                        v___x_1611_ = lean_usize_of_nat(v___x_1604_);
                        v___x_1612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_ppTable_spec__5(v_items_1602_, v___x_1610_, v___x_1611_, v___x_1601_);
                        v___y_1597_ = v___x_1612_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1587_ = 10;
                v___x_1588_ = lean_string_push(v_fst_1585_, v___x_1587_);
                v___x_1589_ = lean_string_append(v___x_1588_, v_snd_1586_);
                lean_dec_ref(v_snd_1586_);
                v___x_1590_ = lean_unsigned_to_nat(0);
                v___x_1591_ = lean_string_utf8_byte_size(v___x_1589_);
                lean_inc_ref(v___x_1589_);
                v___x_1592_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1592_, 0, v___x_1589_);
                lean_ctor_set(v___x_1592_, 1, v___x_1590_);
                lean_ctor_set(v___x_1592_, 2, v___x_1591_);
                v___x_1593_ = l_String_Slice_Pos_revSkipWhile___at___00Lake_Toml_ppTable_spec__0(
                    v___x_1592_,
                    v___x_1591_,
                );
                lean_dec_ref_known(v___x_1592_, 3);
                v___x_1594_ = lean_string_utf8_extract(v___x_1589_, v___x_1590_, v___x_1593_);
                lean_dec(v___x_1593_);
                lean_dec_ref(v___x_1589_);
                v___x_1595_ = lean_string_push(v___x_1594_, v___x_1587_);
                return v___x_1595_;
            }
            2 => {
                v_fst_1598_ = lean_ctor_get(v___y_1597_, 0);
                lean_inc(v_fst_1598_);
                v_snd_1599_ = lean_ctor_get(v___y_1597_, 1);
                lean_inc(v_snd_1599_);
                lean_dec_ref(v___y_1597_);
                v_fst_1585_ = v_fst_1598_;
                v_snd_1586_ = v_snd_1599_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_ppTable___boxed(mut v_t_1613_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1614_: *mut LeanObject = core::ptr::null_mut();
    v_res_1614_ = l_Lake_Toml_ppTable(v_t_1613_);
    lean_dec_ref(v_t_1613_);
    return v_res_1614_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Toml_Data_Value(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Float(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Toml_Data_Dict(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Toml_Data_DateTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_String(builtin);
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
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_Toml_Table_empty = _init_l_Lake_Toml_Table_empty();
    lean_mark_persistent(l_Lake_Toml_Table_empty);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Toml_Data_Value(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Toml_Data_Value(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Float(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Toml_Data_Dict(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Toml_Data_DateTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_String(builtin);
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
    res = initialize_Init_Data_String_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Toml_Data_Value(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Toml_Data_Value(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Toml_Data_Value(builtin);
}
