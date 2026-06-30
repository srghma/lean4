// Lean compiler output
// Module: Lean.Elab.StructInstHint
// Imports: Lean.Meta.Hint Init.Data.String.OrderInstances
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_array_size, lean_array_to_list,
    lean_array_uget_borrowed, lean_array_uset, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mod, lean_nat_sub,
    lean_panic_fn_borrowed, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_append,
    lean_string_is_valid_pos, lean_string_mk, lean_string_utf8_byte_size,
    lean_string_utf8_get_fast, lean_string_utf8_next, lean_string_utf8_next_fast,
    lean_uint32_dec_eq, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::List::Basic::l_List_replicateTR___redArg;
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_pos_x21;
use crate::r#gen::Init::Data::String::Defs::l_String_instInhabitedSlice;
use crate::r#gen::Init::Data::String::OrderInstances::{
    initialize_Init_Data_String_OrderInstances, runtime_initialize_Init_Data_String_OrderInstances,
};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_getSepArgs;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getHeadInfo, l_Lean_Syntax_getKind,
    l_Lean_Syntax_getNumArgs, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::l_Lean_diagnostics;
use crate::r#gen::Lean::Data::Lsp::Utf16::l_Lean_FileMap_utf8PosToLspPos;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isPrefixOf;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::{
    l_Lean_Kernel_enableDiag, l_Lean_Kernel_isDiagnosticsEnabled,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_nil, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Hint::{
    initialize_Lean_Meta_Hint, l_Lean_MessageData_hint, runtime_initialize_Lean_Meta_Hint,
};
use crate::r#gen::Lean::Meta::TryThis::l_Lean_Meta_Tactic_TryThis_format_inputWidth;
use crate::r#gen::Lean::PrettyPrinter::Delaborator::Basic::l_Lean_PrettyPrinter_delab;
use crate::r#gen::Lean::PrettyPrinter::Delaborator::Options::l_Lean_pp_mvars;
use crate::r#gen::Lean::PrettyPrinter::l_Lean_PrettyPrinter_ppCategory;
use crate::r#gen::Lean::Syntax::l_Lean_Syntax_ofRange;
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
pub static l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__3_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 0]};
static mut l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__3_value) as *mut leanh::LeanObject,2026475204632980274 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___closed__0_value) as *mut leanh::LeanObject,11147748073509477642 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0___closed__0_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        65, 100, 100, 32, 109, 105, 115, 115, 105, 110, 103, 32, 102, 105, 101, 108, 100, 115, 0,
    ],
};
static mut l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 58, 61, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 101, 114, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__1_value) as *mut leanh::LeanObject,8609355255726335675 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__6_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__2_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        65, 100, 100, 32, 109, 105, 115, 115, 105, 110, 103, 32, 102, 105, 101, 108, 100, 115, 58,
        0,
    ],
};
static mut l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__4_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__6_value:
    leanh::LeanStringObject<26> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__7_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__8_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f(
    mut v_stx_826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_834_: u8 = 0;
    let mut v___y_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_840_: u8 = 0;
    let mut v___y_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_845_: u8 = 0;
    let mut v___y_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: u8 = 0;
    let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_856_: u8 = 0;
    let mut v___x_857_: u8 = 0;
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: u8 = 0;
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: u8 = 0;
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: u8 = 0;
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_883_ = l_Lean_Syntax_getHeadInfo(v_stx_826_);
                if leanh::lean_obj_tag(v___x_883_) == 0 {
                    leanh::lean_dec_ref_known(v___x_883_, 4);
                    leanh::lean_inc(v_stx_826_);
                    v___x_884_ = l_Lean_Syntax_getKind(v_stx_826_);
                    v___x_885_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__4;
                    v___x_886_ = lean_name_eq(v___x_884_, v___x_885_);
                    leanh::lean_dec(v___x_884_);
                    if v___x_886_ == 0 {
                        leanh::lean_dec(v_stx_826_);
                        v___x_887_ = leanh::lean_box(0);
                        return v___x_887_;
                    } else {
                        v___x_888_ = leanh::lean_unsigned_to_nat(1);
                        v___x_889_ = l_Lean_Syntax_getArg(v_stx_826_, v___x_888_);
                        v___x_890_ = l_Lean_Syntax_getArg(v___x_889_, v___x_888_);
                        leanh::lean_dec(v___x_889_);
                        if leanh::lean_obj_tag(v___x_890_) == 0 {
                            if v___x_886_ == 0 {
                                v_fst_855_ = v___x_890_;
                                v_snd_856_ = v___x_886_;
                                state = 3;
                                continue;
                            } else {
                                v___x_891_ = leanh::lean_unsigned_to_nat(0);
                                v___x_892_ = l_Lean_Syntax_getArg(v_stx_826_, v___x_891_);
                                v___x_893_ = 0;
                                v_fst_855_ = v___x_892_;
                                v_snd_856_ = v___x_893_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_fst_855_ = v___x_890_;
                            v_snd_856_ = v___x_886_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_883_);
                    leanh::lean_dec(v_stx_826_);
                    v___x_894_ = leanh::lean_box(0);
                    return v___x_894_;
                }
            }
            1 => {
                v___x_836_ = leanh::lean_alloc_ctor(0, 7, (1) as u32);
                leanh::lean_ctor_set(v___x_836_, 0, v___y_829_);
                leanh::lean_ctor_set(v___x_836_, 1, v___y_835_);
                leanh::lean_ctor_set(v___x_836_, 2, v___y_832_);
                leanh::lean_ctor_set(v___x_836_, 3, v___y_831_);
                leanh::lean_ctor_set(v___x_836_, 4, v___y_828_);
                leanh::lean_ctor_set(v___x_836_, 5, v___y_830_);
                leanh::lean_ctor_set(v___x_836_, 6, v___y_833_);
                leanh::lean_ctor_set_uint8(
                    v___x_836_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v___y_834_,
                );
                v___x_837_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_837_, 0, v___x_836_);
                return v___x_837_;
            }
            2 => {
                v___x_847_ = lean_array_get_size(v___y_844_);
                v___x_848_ = leanh::lean_unsigned_to_nat(1);
                v___x_849_ = lean_nat_sub(v___x_847_, v___x_848_);
                v___x_850_ = lean_nat_dec_lt(v___x_849_, v___x_847_);
                if v___x_850_ == 0 {
                    leanh::lean_dec(v___x_849_);
                    leanh::lean_dec_ref(v___y_844_);
                    v___x_851_ = leanh::lean_box(0);
                    v___y_828_ = v___y_839_;
                    v___y_829_ = v___y_846_;
                    v___y_830_ = v___y_841_;
                    v___y_831_ = v___y_842_;
                    v___y_832_ = v___x_847_;
                    v___y_833_ = v___y_843_;
                    v___y_834_ = v___y_845_;
                    v___y_835_ = v___x_851_;
                    state = 1;
                    continue;
                } else {
                    v___x_852_ = lean_array_fget(v___y_844_, v___x_849_);
                    leanh::lean_dec(v___x_849_);
                    leanh::lean_dec_ref(v___y_844_);
                    v___x_853_ = l_Lean_Syntax_getTailPos_x3f(v___x_852_, v___y_840_);
                    leanh::lean_dec(v___x_852_);
                    v___y_828_ = v___y_839_;
                    v___y_829_ = v___y_846_;
                    v___y_830_ = v___y_841_;
                    v___y_831_ = v___y_842_;
                    v___y_832_ = v___x_847_;
                    v___y_833_ = v___y_843_;
                    v___y_834_ = v___y_845_;
                    v___y_835_ = v___x_853_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_857_ = 0;
                v___x_858_ = l_Lean_Syntax_getPos_x3f(v_fst_855_, v___x_857_);
                if leanh::lean_obj_tag(v___x_858_) == 0 {
                    leanh::lean_dec(v_fst_855_);
                    leanh::lean_dec(v_stx_826_);
                    v___x_859_ = leanh::lean_box(0);
                    return v___x_859_;
                } else {
                    v_val_860_ = leanh::lean_ctor_get(v___x_858_, 0);
                    leanh::lean_inc(v_val_860_);
                    leanh::lean_dec_ref_known(v___x_858_, 1);
                    v___x_861_ = l_Lean_Syntax_getTailPos_x3f(v_fst_855_, v___x_857_);
                    leanh::lean_dec(v_fst_855_);
                    if leanh::lean_obj_tag(v___x_861_) == 0 {
                        leanh::lean_dec(v_val_860_);
                        leanh::lean_dec(v_stx_826_);
                        v___x_862_ = leanh::lean_box(0);
                        return v___x_862_;
                    } else {
                        v_val_863_ = leanh::lean_ctor_get(v___x_861_, 0);
                        leanh::lean_inc(v_val_863_);
                        leanh::lean_dec_ref_known(v___x_861_, 1);
                        v___x_864_ = leanh::lean_unsigned_to_nat(0);
                        v___x_865_ = l_Lean_Syntax_getArg(v_stx_826_, v___x_864_);
                        v___x_866_ = l_Lean_Syntax_getPos_x3f(v___x_865_, v___x_857_);
                        leanh::lean_dec(v___x_865_);
                        if leanh::lean_obj_tag(v___x_866_) == 0 {
                            leanh::lean_dec(v_val_863_);
                            leanh::lean_dec(v_val_860_);
                            leanh::lean_dec(v_stx_826_);
                            v___x_867_ = leanh::lean_box(0);
                            return v___x_867_;
                        } else {
                            v_val_868_ = leanh::lean_ctor_get(v___x_866_, 0);
                            leanh::lean_inc(v_val_868_);
                            leanh::lean_dec_ref_known(v___x_866_, 1);
                            v___x_869_ = leanh::lean_unsigned_to_nat(5);
                            v___x_870_ = l_Lean_Syntax_getArg(v_stx_826_, v___x_869_);
                            v___x_871_ = l_Lean_Syntax_getPos_x3f(v___x_870_, v___x_857_);
                            leanh::lean_dec(v___x_870_);
                            if leanh::lean_obj_tag(v___x_871_) == 0 {
                                leanh::lean_dec(v_val_868_);
                                leanh::lean_dec(v_val_863_);
                                leanh::lean_dec(v_val_860_);
                                leanh::lean_dec(v_stx_826_);
                                v___x_872_ = leanh::lean_box(0);
                                return v___x_872_;
                            } else {
                                v_val_873_ = leanh::lean_ctor_get(v___x_871_, 0);
                                leanh::lean_inc(v_val_873_);
                                leanh::lean_dec_ref_known(v___x_871_, 1);
                                v___x_874_ = leanh::lean_unsigned_to_nat(2);
                                v___x_875_ = l_Lean_Syntax_getArg(v_stx_826_, v___x_874_);
                                leanh::lean_dec(v_stx_826_);
                                v___x_876_ = l_Lean_Syntax_getArg(v___x_875_, v___x_864_);
                                leanh::lean_dec(v___x_875_);
                                v___x_877_ = l_Lean_Syntax_getSepArgs(v___x_876_);
                                leanh::lean_dec(v___x_876_);
                                v___x_878_ = lean_array_get_size(v___x_877_);
                                v___x_879_ = lean_nat_dec_lt(v___x_864_, v___x_878_);
                                if v___x_879_ == 0 {
                                    v___x_880_ = leanh::lean_box(0);
                                    v___y_839_ = v_val_860_;
                                    v___y_840_ = v___x_857_;
                                    v___y_841_ = v_val_863_;
                                    v___y_842_ = v_val_868_;
                                    v___y_843_ = v_val_873_;
                                    v___y_844_ = v___x_877_;
                                    v___y_845_ = v_snd_856_;
                                    v___y_846_ = v___x_880_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_881_ = lean_array_fget(v___x_877_, v___x_864_);
                                    v___x_882_ = l_Lean_Syntax_getPos_x3f(v___x_881_, v___x_857_);
                                    leanh::lean_dec(v___x_881_);
                                    v___y_839_ = v_val_860_;
                                    v___y_840_ = v___x_857_;
                                    v___y_841_ = v_val_863_;
                                    v___y_842_ = v_val_868_;
                                    v___y_843_ = v_val_873_;
                                    v___y_844_ = v___x_877_;
                                    v___y_845_ = v_snd_856_;
                                    v___y_846_ = v___x_882_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd_spec__0___redArg(
    mut v___x_895_: *mut leanh::LeanObject,
    mut v___x_896_: *mut leanh::LeanObject,
    mut v_s_897_: *mut leanh::LeanObject,
    mut v_a_898_: *mut leanh::LeanObject,
    mut v_b_899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: u8 = 0;
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: u32 = 0;
    let mut v___x_906_: u32 = 0;
    let mut v___x_907_: u8 = 0;
    let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_900_ = leanh::lean_ctor_get(v___x_895_, 1);
                v_endExclusive_901_ = leanh::lean_ctor_get(v___x_895_, 2);
                v___x_902_ = lean_nat_sub(v_endExclusive_901_, v_startInclusive_900_);
                v___x_903_ = lean_nat_dec_eq(v_a_898_, v___x_902_);
                leanh::lean_dec(v___x_902_);
                if v___x_903_ == 0 {
                    v___x_904_ = lean_nat_add(v___x_896_, v_a_898_);
                    v___x_905_ = lean_string_utf8_get_fast(v_s_897_, v___x_904_);
                    v___x_906_ = 10;
                    v___x_907_ = lean_uint32_dec_eq(v___x_905_, v___x_906_);
                    if v___x_907_ == 0 {
                        leanh::lean_dec(v_a_898_);
                        v___x_908_ = leanh::lean_box(0);
                        v___x_909_ = lean_string_utf8_next_fast(v_s_897_, v___x_904_);
                        leanh::lean_dec(v___x_904_);
                        v___x_910_ = lean_nat_sub(v___x_909_, v___x_896_);
                        v_a_898_ = v___x_910_;
                        v_b_899_ = v___x_908_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_904_);
                        v___x_912_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_912_, 0, v_a_898_);
                        return v___x_912_;
                    }
                } else {
                    leanh::lean_dec(v_a_898_);
                    leanh::lean_inc(v_b_899_);
                    return v_b_899_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd_spec__0___redArg___boxed(
    mut v___x_913_: *mut leanh::LeanObject,
    mut v___x_914_: *mut leanh::LeanObject,
    mut v_s_915_: *mut leanh::LeanObject,
    mut v_a_916_: *mut leanh::LeanObject,
    mut v_b_917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_918_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd_spec__0___redArg(v___x_913_, v___x_914_, v_s_915_, v_a_916_, v_b_917_);
    leanh::lean_dec(v_b_917_);
    leanh::lean_dec_ref(v_s_915_);
    leanh::lean_dec(v___x_914_);
    leanh::lean_dec_ref(v___x_913_);
    return v_res_918_;
}
pub unsafe fn l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd(
    mut v_s_919_: *mut leanh::LeanObject,
    mut v_p_920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_searcher_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_searcher_921_ = leanh::lean_unsigned_to_nat(0);
    v___x_922_ = lean_string_utf8_byte_size(v_s_919_);
    leanh::lean_inc_ref_n(v_s_919_, 2);
    v___x_923_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_923_, 0, v_s_919_);
    leanh::lean_ctor_set(v___x_923_, 1, v_searcher_921_);
    leanh::lean_ctor_set(v___x_923_, 2, v___x_922_);
    v___x_924_ = l_String_Slice_pos_x21(v___x_923_, v_p_920_);
    leanh::lean_dec_ref_known(v___x_923_, 3);
    leanh::lean_inc(v___x_924_);
    v___x_925_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_925_, 0, v_s_919_);
    leanh::lean_ctor_set(v___x_925_, 1, v___x_924_);
    leanh::lean_ctor_set(v___x_925_, 2, v___x_922_);
    v___x_926_ = leanh::lean_box(0);
    v___x_927_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd_spec__0___redArg(v___x_925_, v___x_924_, v_s_919_, v_searcher_921_, v___x_926_);
    leanh::lean_dec_ref(v_s_919_);
    leanh::lean_dec_ref_known(v___x_925_, 3);
    if leanh::lean_obj_tag(v___x_927_) == 0 {
        let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_929_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_928_ = lean_nat_sub(v___x_922_, v___x_924_);
        v___x_929_ = lean_nat_add(v___x_924_, v___x_928_);
        leanh::lean_dec(v___x_928_);
        leanh::lean_dec(v___x_924_);
        return v___x_929_;
    } else {
        let mut v_val_930_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_931_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_930_ = leanh::lean_ctor_get(v___x_927_, 0);
        leanh::lean_inc(v_val_930_);
        leanh::lean_dec_ref_known(v___x_927_, 1);
        v___x_931_ = lean_nat_add(v___x_924_, v_val_930_);
        leanh::lean_dec(v_val_930_);
        leanh::lean_dec(v___x_924_);
        return v___x_931_;
    }
}
pub unsafe fn l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd___boxed(
    mut v_s_932_: *mut leanh::LeanObject,
    mut v_p_933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_934_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd(v_s_932_, v_p_933_);
    leanh::lean_dec(v_p_933_);
    return v_res_934_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd_spec__0(
    mut v___x_935_: *mut leanh::LeanObject,
    mut v___x_936_: *mut leanh::LeanObject,
    mut v_s_937_: *mut leanh::LeanObject,
    mut v_inst_938_: *mut leanh::LeanObject,
    mut v_R_939_: *mut leanh::LeanObject,
    mut v_a_940_: *mut leanh::LeanObject,
    mut v_b_941_: *mut leanh::LeanObject,
    mut v_c_942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_943_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd_spec__0___redArg(v___x_935_, v___x_936_, v_s_937_, v_a_940_, v_b_941_);
    return v___x_943_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd_spec__0___boxed(
    mut v___x_944_: *mut leanh::LeanObject,
    mut v___x_945_: *mut leanh::LeanObject,
    mut v_s_946_: *mut leanh::LeanObject,
    mut v_inst_947_: *mut leanh::LeanObject,
    mut v_R_948_: *mut leanh::LeanObject,
    mut v_a_949_: *mut leanh::LeanObject,
    mut v_b_950_: *mut leanh::LeanObject,
    mut v_c_951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_952_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd_spec__0(v___x_944_, v___x_945_, v_s_946_, v_inst_947_, v_R_948_, v_a_949_, v_b_950_, v_c_951_);
    leanh::lean_dec(v_b_950_);
    leanh::lean_dec_ref(v_s_946_);
    leanh::lean_dec(v___x_945_);
    leanh::lean_dec_ref(v___x_944_);
    return v_res_952_;
}
pub unsafe fn l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg(
    mut v_stx_956_: *mut leanh::LeanObject,
    mut v_view_957_: *mut leanh::LeanObject,
    mut v_a_958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_numFields_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: u8 = 0;
    let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rawFields_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastInterveningSepIdx_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: u8 = 0;
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: u8 = 0;
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_987_: u8 = 0;
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_994_: u8 = 0;
    let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_998_: u8 = 0;
    let mut v_fileMap_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: u8 = 0;
    let mut v___x_1007_: u8 = 0;
    let mut v___x_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1016_: u8 = 0;
    let mut v_unused_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1022_: u8 = 0;
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1027_: u8 = 0;
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_numFields_960_ = leanh::lean_ctor_get(v_view_957_, 2);
                v___x_961_ = leanh::lean_unsigned_to_nat(2);
                v___x_962_ = lean_nat_dec_le(v___x_961_, v_numFields_960_);
                if v___x_962_ == 0 {
                    v___x_963_ = leanh::lean_box((v___x_962_) as usize);
                    v___x_964_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_964_, 0, v___x_963_);
                    return v___x_964_;
                } else {
                    v___x_965_ = l_Lean_Syntax_getArg(v_stx_956_, v___x_961_);
                    v___x_966_ = leanh::lean_unsigned_to_nat(0);
                    v_rawFields_967_ = l_Lean_Syntax_getArg(v___x_965_, v___x_966_);
                    leanh::lean_dec(v___x_965_);
                    v___x_968_ = l_Lean_Syntax_getNumArgs(v_rawFields_967_);
                    v___x_969_ = lean_nat_sub(v___x_968_, v___x_961_);
                    v___x_970_ = leanh::lean_unsigned_to_nat(1);
                    v___x_971_ = lean_nat_add(v___x_968_, v___x_970_);
                    leanh::lean_dec(v___x_968_);
                    v___x_972_ = lean_nat_mod(v___x_971_, v___x_961_);
                    leanh::lean_dec(v___x_971_);
                    v_lastInterveningSepIdx_973_ = lean_nat_sub(v___x_969_, v___x_972_);
                    leanh::lean_dec(v___x_972_);
                    leanh::lean_dec(v___x_969_);
                    v___x_974_ =
                        l_Lean_Syntax_getArg(v_rawFields_967_, v_lastInterveningSepIdx_973_);
                    v___x_975_ = l_Lean_Syntax_getKind(v___x_974_);
                    v___x_976_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___closed__1;
                    v___x_977_ = lean_name_eq(v___x_975_, v___x_976_);
                    leanh::lean_dec(v___x_975_);
                    if v___x_977_ == 0 {
                        leanh::lean_dec(v_lastInterveningSepIdx_973_);
                        leanh::lean_dec(v_rawFields_967_);
                        v___x_978_ = leanh::lean_box((v___x_977_) as usize);
                        v___x_979_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_979_, 0, v___x_978_);
                        return v___x_979_;
                    } else {
                        v___x_980_ = lean_nat_sub(v_lastInterveningSepIdx_973_, v___x_970_);
                        v___x_981_ = l_Lean_Syntax_getArg(v_rawFields_967_, v___x_980_);
                        leanh::lean_dec(v___x_980_);
                        v___x_982_ = 0;
                        v___x_983_ = l_Lean_Syntax_getPos_x3f(v___x_981_, v___x_982_);
                        leanh::lean_dec(v___x_981_);
                        if leanh::lean_obj_tag(v___x_983_) == 1 {
                            v_val_984_ = leanh::lean_ctor_get(v___x_983_, 0);
                            v_isSharedCheck_1027_ =
                                (!leanh::lean_is_exclusive(v___x_983_)) as u8;
                            if v_isSharedCheck_1027_ == 0 {
                                v___x_986_ = v___x_983_;
                                v_isShared_987_ = v_isSharedCheck_1027_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_984_);
                                leanh::lean_dec(v___x_983_);
                                v___x_986_ = leanh::lean_box(0);
                                v_isShared_987_ = v_isSharedCheck_1027_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_983_);
                            leanh::lean_dec(v_lastInterveningSepIdx_973_);
                            leanh::lean_dec(v_rawFields_967_);
                            v___x_1028_ = leanh::lean_box((v___x_982_) as usize);
                            v___x_1029_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1029_, 0, v___x_1028_);
                            return v___x_1029_;
                        }
                    }
                }
            }
            1 => {
                v___x_988_ = lean_nat_add(v_lastInterveningSepIdx_973_, v___x_970_);
                leanh::lean_dec(v_lastInterveningSepIdx_973_);
                v___x_989_ = l_Lean_Syntax_getArg(v_rawFields_967_, v___x_988_);
                leanh::lean_dec(v___x_988_);
                leanh::lean_dec(v_rawFields_967_);
                v___x_990_ = l_Lean_Syntax_getPos_x3f(v___x_989_, v___x_982_);
                if leanh::lean_obj_tag(v___x_990_) == 1 {
                    leanh::lean_del_object(v___x_986_);
                    v_val_991_ = leanh::lean_ctor_get(v___x_990_, 0);
                    v_isSharedCheck_1022_ = (!leanh::lean_is_exclusive(v___x_990_)) as u8;
                    if v_isSharedCheck_1022_ == 0 {
                        v___x_993_ = v___x_990_;
                        v_isShared_994_ = v_isSharedCheck_1022_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_991_);
                        leanh::lean_dec(v___x_990_);
                        v___x_993_ = leanh::lean_box(0);
                        v_isShared_994_ = v_isSharedCheck_1022_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_990_);
                    leanh::lean_dec(v___x_989_);
                    leanh::lean_dec(v_val_984_);
                    v___x_1023_ = leanh::lean_box((v___x_982_) as usize);
                    if v_isShared_987_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_986_, 0);
                        leanh::lean_ctor_set(v___x_986_, 0, v___x_1023_);
                        v___x_1025_ = v___x_986_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1026_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1023_);
                        v___x_1025_ = v_reuseFailAlloc_1026_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v___x_995_ = l_Lean_Syntax_getTailPos_x3f(v___x_989_, v___x_982_);
                leanh::lean_dec(v___x_989_);
                if leanh::lean_obj_tag(v___x_995_) == 1 {
                    leanh::lean_del_object(v___x_993_);
                    v_isSharedCheck_1016_ = (!leanh::lean_is_exclusive(v___x_995_)) as u8;
                    if v_isSharedCheck_1016_ == 0 {
                        v_unused_1017_ = leanh::lean_ctor_get(v___x_995_, 0);
                        leanh::lean_dec(v_unused_1017_);
                        v___x_997_ = v___x_995_;
                        v_isShared_998_ = v_isSharedCheck_1016_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_995_);
                        v___x_997_ = leanh::lean_box(0);
                        v_isShared_998_ = v_isSharedCheck_1016_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_995_);
                    leanh::lean_dec(v_val_991_);
                    leanh::lean_dec(v_val_984_);
                    v___x_1018_ = leanh::lean_box((v___x_982_) as usize);
                    if v_isShared_994_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_993_, 0);
                        leanh::lean_ctor_set(v___x_993_, 0, v___x_1018_);
                        v___x_1020_ = v___x_993_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1021_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1018_);
                        v___x_1020_ = v_reuseFailAlloc_1021_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v_fileMap_999_ = leanh::lean_ctor_get(v_a_958_, 1);
                leanh::lean_inc_ref_n(v_fileMap_999_, 2);
                v___x_1000_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_999_, v_val_984_);
                leanh::lean_dec(v_val_984_);
                v_line_1001_ = leanh::lean_ctor_get(v___x_1000_, 0);
                leanh::lean_inc(v_line_1001_);
                v_character_1002_ = leanh::lean_ctor_get(v___x_1000_, 1);
                leanh::lean_inc(v_character_1002_);
                leanh::lean_dec_ref(v___x_1000_);
                v___x_1003_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_999_, v_val_991_);
                leanh::lean_dec(v_val_991_);
                v_line_1004_ = leanh::lean_ctor_get(v___x_1003_, 0);
                leanh::lean_inc(v_line_1004_);
                v_character_1005_ = leanh::lean_ctor_get(v___x_1003_, 1);
                leanh::lean_inc(v_character_1005_);
                leanh::lean_dec_ref(v___x_1003_);
                v___x_1006_ = lean_nat_dec_eq(v_line_1004_, v_line_1001_);
                leanh::lean_dec(v_line_1001_);
                leanh::lean_dec(v_line_1004_);
                if v___x_1006_ == 0 {
                    v___x_1007_ = lean_nat_dec_lt(v_character_1005_, v_character_1002_);
                    leanh::lean_dec(v_character_1002_);
                    leanh::lean_dec(v_character_1005_);
                    v___x_1008_ = leanh::lean_box((v___x_1007_) as usize);
                    if v_isShared_998_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_997_, 0);
                        leanh::lean_ctor_set(v___x_997_, 0, v___x_1008_);
                        v___x_1010_ = v___x_997_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1011_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
                        v___x_1010_ = v_reuseFailAlloc_1011_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_character_1005_);
                    leanh::lean_dec(v_character_1002_);
                    v___x_1012_ = leanh::lean_box((v___x_1006_) as usize);
                    if v_isShared_998_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_997_, 0);
                        leanh::lean_ctor_set(v___x_997_, 0, v___x_1012_);
                        v___x_1014_ = v___x_997_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1015_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1012_);
                        v___x_1014_ = v_reuseFailAlloc_1015_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1010_;
            }
            5 => {
                return v___x_1014_;
            }
            6 => {
                return v___x_1020_;
            }
            7 => {
                return v___x_1025_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___boxed(
    mut v_stx_1030_: *mut leanh::LeanObject,
    mut v_view_1031_: *mut leanh::LeanObject,
    mut v_a_1032_: *mut leanh::LeanObject,
    mut v_a_1033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1034_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg(v_stx_1030_, v_view_1031_, v_a_1032_);
    leanh::lean_dec_ref(v_a_1032_);
    leanh::lean_dec_ref(v_view_1031_);
    leanh::lean_dec(v_stx_1030_);
    return v_res_1034_;
}
pub unsafe fn l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle(
    mut v_stx_1035_: *mut leanh::LeanObject,
    mut v_view_1036_: *mut leanh::LeanObject,
    mut v_a_1037_: *mut leanh::LeanObject,
    mut v_a_1038_: *mut leanh::LeanObject,
    mut v_a_1039_: *mut leanh::LeanObject,
    mut v_a_1040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1042_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg(v_stx_1035_, v_view_1036_, v_a_1039_);
    return v___x_1042_;
}
pub unsafe fn l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___boxed(
    mut v_stx_1043_: *mut leanh::LeanObject,
    mut v_view_1044_: *mut leanh::LeanObject,
    mut v_a_1045_: *mut leanh::LeanObject,
    mut v_a_1046_: *mut leanh::LeanObject,
    mut v_a_1047_: *mut leanh::LeanObject,
    mut v_a_1048_: *mut leanh::LeanObject,
    mut v_a_1049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1050_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle(v_stx_1043_, v_view_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
    leanh::lean_dec(v_a_1048_);
    leanh::lean_dec_ref(v_a_1047_);
    leanh::lean_dec(v_a_1046_);
    leanh::lean_dec_ref(v_a_1045_);
    leanh::lean_dec_ref(v_view_1044_);
    leanh::lean_dec(v_stx_1043_);
    return v_res_1050_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1(
    mut v_opts_1051_: *mut leanh::LeanObject,
    mut v_opt_1052_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1053_ = leanh::lean_ctor_get(v_opt_1052_, 0);
    v_defValue_1054_ = leanh::lean_ctor_get(v_opt_1052_, 1);
    v_map_1055_ = leanh::lean_ctor_get(v_opts_1051_, 0);
    v___x_1056_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1055_,
            v_name_1053_,
        );
    if leanh::lean_obj_tag(v___x_1056_) == 0 {
        let mut v___x_1057_: u8 = 0;
        v___x_1057_ = (leanh::lean_unbox(v_defValue_1054_) as u8);
        return v___x_1057_;
    } else {
        let mut v_val_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1058_ = leanh::lean_ctor_get(v___x_1056_, 0);
        leanh::lean_inc(v_val_1058_);
        leanh::lean_dec_ref_known(v___x_1056_, 1);
        if leanh::lean_obj_tag(v_val_1058_) == 1 {
            let mut v_v_1059_: u8 = 0;
            v_v_1059_ = leanh::lean_ctor_get_uint8(v_val_1058_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_1058_, 0);
            return v_v_1059_;
        } else {
            let mut v___x_1060_: u8 = 0;
            leanh::lean_dec(v_val_1058_);
            v___x_1060_ = (leanh::lean_unbox(v_defValue_1054_) as u8);
            return v___x_1060_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1___boxed(
    mut v_opts_1061_: *mut leanh::LeanObject,
    mut v_opt_1062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1063_: u8 = 0;
    let mut v_r_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1063_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1(
        v_opts_1061_,
        v_opt_1062_,
    );
    leanh::lean_dec_ref(v_opt_1062_);
    leanh::lean_dec_ref(v_opts_1061_);
    v_r_1064_ = leanh::lean_box((v_res_1063_) as usize);
    return v_r_1064_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2(
    mut v_opts_1065_: *mut leanh::LeanObject,
    mut v_opt_1066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1067_ = leanh::lean_ctor_get(v_opt_1066_, 0);
    v_defValue_1068_ = leanh::lean_ctor_get(v_opt_1066_, 1);
    v_map_1069_ = leanh::lean_ctor_get(v_opts_1065_, 0);
    v___x_1070_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1069_,
            v_name_1067_,
        );
    if leanh::lean_obj_tag(v___x_1070_) == 0 {
        leanh::lean_inc(v_defValue_1068_);
        return v_defValue_1068_;
    } else {
        let mut v_val_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1071_ = leanh::lean_ctor_get(v___x_1070_, 0);
        leanh::lean_inc(v_val_1071_);
        leanh::lean_dec_ref_known(v___x_1070_, 1);
        if leanh::lean_obj_tag(v_val_1071_) == 3 {
            let mut v_v_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_1072_ = leanh::lean_ctor_get(v_val_1071_, 0);
            leanh::lean_inc(v_v_1072_);
            leanh::lean_dec_ref_known(v_val_1071_, 1);
            return v_v_1072_;
        } else {
            leanh::lean_dec(v_val_1071_);
            leanh::lean_inc(v_defValue_1068_);
            return v_defValue_1068_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___boxed(
    mut v_opts_1073_: *mut leanh::LeanObject,
    mut v_opt_1074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1075_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2(
        v_opts_1073_,
        v_opt_1074_,
    );
    leanh::lean_dec_ref(v_opt_1074_);
    leanh::lean_dec_ref(v_opts_1073_);
    return v_res_1075_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__6(
    mut v_msg_1076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1077_ = l_String_instInhabitedSlice;
    v___x_1078_ = lean_panic_fn_borrowed(v___x_1077_, v_msg_1076_);
    return v___x_1078_;
}
pub unsafe fn l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0(
    mut v_x_1080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1081_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0___closed__0;
    return v___x_1081_;
}
pub unsafe fn l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0___boxed(
    mut v_x_1082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1083_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0(v_x_1082_);
    leanh::lean_dec_ref(v_x_1082_);
    return v_res_1083_;
}
pub unsafe fn l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(
    mut v_fileMap_1084_: *mut leanh::LeanObject,
    mut v_p_1085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1086_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_1084_, v_p_1085_);
    v_character_1087_ = leanh::lean_ctor_get(v___x_1086_, 1);
    leanh::lean_inc(v_character_1087_);
    leanh::lean_dec_ref(v___x_1086_);
    return v_character_1087_;
}
pub unsafe fn l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1___boxed(
    mut v_fileMap_1088_: *mut leanh::LeanObject,
    mut v_p_1089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1090_ =
        l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(v_fileMap_1088_, v_p_1089_);
    leanh::lean_dec(v_p_1089_);
    return v_res_1090_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7_spec__8(
    mut v_x_1091_: *mut leanh::LeanObject,
    mut v_x_1092_: *mut leanh::LeanObject,
    mut v_x_1093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1098_: u8 = 0;
    let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1105_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1093_) == 0 {
                    leanh::lean_dec(v_x_1091_);
                    return v_x_1092_;
                } else {
                    v_head_1094_ = leanh::lean_ctor_get(v_x_1093_, 0);
                    v_tail_1095_ = leanh::lean_ctor_get(v_x_1093_, 1);
                    v_isSharedCheck_1105_ = (!leanh::lean_is_exclusive(v_x_1093_)) as u8;
                    if v_isSharedCheck_1105_ == 0 {
                        v___x_1097_ = v_x_1093_;
                        v_isShared_1098_ = v_isSharedCheck_1105_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1095_);
                        leanh::lean_inc(v_head_1094_);
                        leanh::lean_dec(v_x_1093_);
                        v___x_1097_ = leanh::lean_box(0);
                        v_isShared_1098_ = v_isSharedCheck_1105_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1091_);
                if v_isShared_1098_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1097_, 5);
                    leanh::lean_ctor_set(v___x_1097_, 1, v_x_1091_);
                    leanh::lean_ctor_set(v___x_1097_, 0, v_x_1092_);
                    v___x_1100_ = v___x_1097_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1104_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_x_1092_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_x_1091_);
                    v___x_1100_ = v_reuseFailAlloc_1104_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1101_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1101_, 0, v_head_1094_);
                v___x_1102_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1102_, 0, v___x_1100_);
                leanh::lean_ctor_set(v___x_1102_, 1, v___x_1101_);
                v_x_1092_ = v___x_1102_;
                v_x_1093_ = v_tail_1095_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7(
    mut v_x_1106_: *mut leanh::LeanObject,
    mut v_x_1107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1106_) == 0 {
        let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1107_);
        v___x_1108_ = leanh::lean_box(0);
        return v___x_1108_;
    } else {
        let mut v_tail_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_1109_ = leanh::lean_ctor_get(v_x_1106_, 1);
        if leanh::lean_obj_tag(v_tail_1109_) == 0 {
            let mut v_head_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_1107_);
            v_head_1110_ = leanh::lean_ctor_get(v_x_1106_, 0);
            leanh::lean_inc(v_head_1110_);
            leanh::lean_dec_ref_known(v_x_1106_, 2);
            v___x_1111_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1111_, 0, v_head_1110_);
            return v___x_1111_;
        } else {
            let mut v_head_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_1109_);
            v_head_1112_ = leanh::lean_ctor_get(v_x_1106_, 0);
            leanh::lean_inc(v_head_1112_);
            leanh::lean_dec_ref_known(v_x_1106_, 2);
            v___x_1113_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1113_, 0, v_head_1112_);
            v___x_1114_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7_spec__8(v_x_1107_, v___x_1113_, v_tail_1109_);
            return v___x_1114_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___redArg(
    mut v___x_1115_: *mut leanh::LeanObject,
    mut v_j_1116_: *mut leanh::LeanObject,
    mut v_a_1117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1119_: u8 = 0;
    let mut v_one_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1118_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1119_ = lean_nat_dec_eq(v_j_1116_, v_zero_1118_);
                if v_isZero_1119_ == 1 {
                    leanh::lean_dec(v_j_1116_);
                    return v_a_1117_;
                } else {
                    v_one_1120_ = leanh::lean_unsigned_to_nat(1);
                    v_n_1121_ = lean_nat_sub(v_j_1116_, v_one_1120_);
                    leanh::lean_dec(v_j_1116_);
                    v___x_1122_ = lean_string_utf8_next(v___x_1115_, v_a_1117_);
                    leanh::lean_dec(v_a_1117_);
                    v_j_1116_ = v_n_1121_;
                    v_a_1117_ = v___x_1122_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___redArg___boxed(
    mut v___x_1124_: *mut leanh::LeanObject,
    mut v_j_1125_: *mut leanh::LeanObject,
    mut v_a_1126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1127_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___redArg(v___x_1124_, v_j_1125_, v_a_1126_);
    leanh::lean_dec_ref(v___x_1124_);
    return v_res_1127_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0(
    mut v_o_1131_: *mut leanh::LeanObject,
    mut v_k_1132_: *mut leanh::LeanObject,
    mut v_v_1133_: u8,
) -> *mut leanh::LeanObject {
    let mut v_map_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1135_: u8 = 0;
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1138_: u8 = 0;
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: u8 = 0;
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1149_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_1134_ = leanh::lean_ctor_get(v_o_1131_, 0);
                v_hasTrace_1135_ = leanh::lean_ctor_get_uint8(
                    v_o_1131_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1149_ = (!leanh::lean_is_exclusive(v_o_1131_)) as u8;
                if v_isSharedCheck_1149_ == 0 {
                    v___x_1137_ = v_o_1131_;
                    v_isShared_1138_ = v_isSharedCheck_1149_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_map_1134_);
                    leanh::lean_dec(v_o_1131_);
                    v___x_1137_ = leanh::lean_box(0);
                    v_isShared_1138_ = v_isSharedCheck_1149_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1139_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                leanh::lean_ctor_set_uint8(v___x_1139_, 0 as u32, v_v_1133_);
                leanh::lean_inc(v_k_1132_);
                v___x_1140_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1132_, v___x_1139_, v_map_1134_);
                if v_hasTrace_1135_ == 0 {
                    v___x_1141_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__1;
                    v___x_1142_ = l_Lean_Name_isPrefixOf(v___x_1141_, v_k_1132_);
                    leanh::lean_dec(v_k_1132_);
                    if v_isShared_1138_ == 0 {
                        leanh::lean_ctor_set(v___x_1137_, 0, v___x_1140_);
                        v___x_1144_ = v___x_1137_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1145_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1140_);
                        v___x_1144_ = v_reuseFailAlloc_1145_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_k_1132_);
                    if v_isShared_1138_ == 0 {
                        leanh::lean_ctor_set(v___x_1137_, 0, v___x_1140_);
                        v___x_1147_ = v___x_1137_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1148_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1140_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_1148_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_1135_,
                        );
                        v___x_1147_ = v_reuseFailAlloc_1148_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1144_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1142_,
                );
                return v___x_1144_;
            }
            3 => {
                return v___x_1147_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___boxed(
    mut v_o_1150_: *mut leanh::LeanObject,
    mut v_k_1151_: *mut leanh::LeanObject,
    mut v_v_1152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_boxed_1153_: u8 = 0;
    let mut v_res_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_1153_ = (leanh::lean_unbox(v_v_1152_) as u8);
    v_res_1154_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0(v_o_1150_, v_k_1151_, v_v_boxed_1153_);
    return v_res_1154_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0(
    mut v_opts_1155_: *mut leanh::LeanObject,
    mut v_opt_1156_: *mut leanh::LeanObject,
    mut v_val_1157_: u8,
) -> *mut leanh::LeanObject {
    let mut v_name_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1158_ = leanh::lean_ctor_get(v_opt_1156_, 0);
    leanh::lean_inc(v_name_1158_);
    leanh::lean_dec_ref(v_opt_1156_);
    v___x_1159_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0(v_opts_1155_, v_name_1158_, v_val_1157_);
    return v___x_1159_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0___boxed(
    mut v_opts_1160_: *mut leanh::LeanObject,
    mut v_opt_1161_: *mut leanh::LeanObject,
    mut v_val_1162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_boxed_1163_: u8 = 0;
    let mut v_res_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_1163_ = (leanh::lean_unbox(v_val_1162_) as u8);
    v_res_1164_ = l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0(
        v_opts_1160_,
        v_opt_1161_,
        v_val_boxed_1163_,
    );
    return v_res_1164_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1169_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1169_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1170_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__3);
    v___x_1171_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1171_, 0, v___x_1170_);
    return v___x_1171_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1172_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__4);
    v___x_1173_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1173_, 0, v___x_1172_);
    leanh::lean_ctor_set(v___x_1173_, 1, v___x_1172_);
    return v___x_1173_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3(
    mut v_sz_1175_: usize,
    mut v_i_1176_: usize,
    mut v_bs_1177_: *mut leanh::LeanObject,
    mut v___y_1178_: *mut leanh::LeanObject,
    mut v___y_1179_: *mut leanh::LeanObject,
    mut v___y_1180_: *mut leanh::LeanObject,
    mut v___y_1181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1183_: u8 = 0;
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: usize = 0;
    let mut v___x_1197_: usize = 0;
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1214_: u8 = 0;
    let mut v_inheritedTraceOptions_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: u8 = 0;
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: u8 = 0;
    let mut v_fileName_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1235_: u8 = 0;
    let mut v_inheritedTraceOptions_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1251_: u8 = 0;
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1255_: u8 = 0;
    let mut v_a_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1259_: u8 = 0;
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1263_: u8 = 0;
    let mut v___y_1265_: u8 = 0;
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1277_: u8 = 0;
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1284_: u8 = 0;
    let mut v_unused_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: u8 = 0;
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1183_ = lean_usize_dec_lt(v_i_1176_, v_sz_1175_);
                if v___x_1183_ == 0 {
                    v___x_1184_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1184_, 0, v_bs_1177_);
                    return v___x_1184_;
                } else {
                    v_v_1185_ = lean_array_uget_borrowed(v_bs_1177_, v_i_1176_);
                    v_fst_1186_ = leanh::lean_ctor_get(v_v_1185_, 0);
                    leanh::lean_inc(v_fst_1186_);
                    v_snd_1187_ = leanh::lean_ctor_get(v_v_1185_, 1);
                    leanh::lean_inc(v_snd_1187_);
                    v___x_1188_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1189_ = lean_array_uset(v_bs_1177_, v_i_1176_, v___x_1188_);
                    if leanh::lean_obj_tag(v_snd_1187_) == 1 {
                        v_val_1200_ = leanh::lean_ctor_get(v_snd_1187_, 0);
                        leanh::lean_inc(v_val_1200_);
                        leanh::lean_dec_ref_known(v_snd_1187_, 1);
                        v___x_1201_ = lean_st_ref_get(v___y_1181_);
                        v_fileName_1202_ = leanh::lean_ctor_get(v___y_1180_, 0);
                        v_fileMap_1203_ = leanh::lean_ctor_get(v___y_1180_, 1);
                        v_options_1204_ = leanh::lean_ctor_get(v___y_1180_, 2);
                        v_currRecDepth_1205_ = leanh::lean_ctor_get(v___y_1180_, 3);
                        v_ref_1206_ = leanh::lean_ctor_get(v___y_1180_, 5);
                        v_currNamespace_1207_ = leanh::lean_ctor_get(v___y_1180_, 6);
                        v_openDecls_1208_ = leanh::lean_ctor_get(v___y_1180_, 7);
                        v_initHeartbeats_1209_ = leanh::lean_ctor_get(v___y_1180_, 8);
                        v_maxHeartbeats_1210_ = leanh::lean_ctor_get(v___y_1180_, 9);
                        v_quotContext_1211_ = leanh::lean_ctor_get(v___y_1180_, 10);
                        v_currMacroScope_1212_ = leanh::lean_ctor_get(v___y_1180_, 11);
                        v_cancelTk_x3f_1213_ = leanh::lean_ctor_get(v___y_1180_, 12);
                        v_suppressElabErrors_1214_ = leanh::lean_ctor_get_uint8(
                            v___y_1180_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                        );
                        v_inheritedTraceOptions_1215_ =
                            leanh::lean_ctor_get(v___y_1180_, 13);
                        v_env_1216_ = leanh::lean_ctor_get(v___x_1201_, 0);
                        leanh::lean_inc_ref(v_env_1216_);
                        leanh::lean_dec(v___x_1201_);
                        v___x_1217_ = leanh::lean_box(1);
                        v___x_1218_ = l_Lean_pp_mvars;
                        v___x_1219_ = 0;
                        leanh::lean_inc_ref(v_options_1204_);
                        v___x_1220_ = l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0(v_options_1204_, v___x_1218_, v___x_1219_);
                        v___x_1221_ = l_Lean_diagnostics;
                        v___x_1222_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1(v___x_1220_, v___x_1221_);
                        v___x_1286_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1216_);
                        leanh::lean_dec_ref(v_env_1216_);
                        if v___x_1286_ == 0 {
                            if v___x_1222_ == 0 {
                                v___y_1265_ = v___x_1183_;
                                state = 7;
                                continue;
                            } else {
                                v___y_1265_ = v___x_1286_;
                                state = 7;
                                continue;
                            }
                        } else {
                            v___y_1265_ = v___x_1222_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_snd_1187_);
                        v___x_1287_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__6;
                        v_value_1191_ = v___x_1287_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1192_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_fst_1186_,
                    v___x_1183_,
                );
                v___x_1193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__0;
                v___x_1194_ = lean_string_append(v___x_1192_, v___x_1193_);
                v___x_1195_ = lean_string_append(v___x_1194_, v_value_1191_);
                leanh::lean_dec_ref(v_value_1191_);
                v___x_1196_ = 1usize;
                v___x_1197_ = lean_usize_add(v_i_1176_, v___x_1196_);
                v___x_1198_ = lean_array_uset(v_bs_x27_1189_, v_i_1176_, v___x_1195_);
                v_i_1176_ = v___x_1197_;
                v_bs_1177_ = v___x_1198_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1238_ = l_Lean_maxRecDepth;
                v___x_1239_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2(v___x_1220_, v___x_1238_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_1236_);
                leanh::lean_inc(v_cancelTk_x3f_1234_);
                leanh::lean_inc(v_currMacroScope_1233_);
                leanh::lean_inc(v_quotContext_1232_);
                leanh::lean_inc(v_maxHeartbeats_1231_);
                leanh::lean_inc(v_initHeartbeats_1230_);
                leanh::lean_inc(v_openDecls_1229_);
                leanh::lean_inc(v_currNamespace_1228_);
                leanh::lean_inc(v_ref_1227_);
                leanh::lean_inc(v_currRecDepth_1226_);
                leanh::lean_inc_ref(v_fileMap_1225_);
                leanh::lean_inc_ref(v_fileName_1224_);
                v___x_1240_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_1240_, 0, v_fileName_1224_);
                leanh::lean_ctor_set(v___x_1240_, 1, v_fileMap_1225_);
                leanh::lean_ctor_set(v___x_1240_, 2, v___x_1220_);
                leanh::lean_ctor_set(v___x_1240_, 3, v_currRecDepth_1226_);
                leanh::lean_ctor_set(v___x_1240_, 4, v___x_1239_);
                leanh::lean_ctor_set(v___x_1240_, 5, v_ref_1227_);
                leanh::lean_ctor_set(v___x_1240_, 6, v_currNamespace_1228_);
                leanh::lean_ctor_set(v___x_1240_, 7, v_openDecls_1229_);
                leanh::lean_ctor_set(v___x_1240_, 8, v_initHeartbeats_1230_);
                leanh::lean_ctor_set(v___x_1240_, 9, v_maxHeartbeats_1231_);
                leanh::lean_ctor_set(v___x_1240_, 10, v_quotContext_1232_);
                leanh::lean_ctor_set(v___x_1240_, 11, v_currMacroScope_1233_);
                leanh::lean_ctor_set(v___x_1240_, 12, v_cancelTk_x3f_1234_);
                leanh::lean_ctor_set(v___x_1240_, 13, v_inheritedTraceOptions_1236_);
                leanh::lean_ctor_set_uint8(
                    v___x_1240_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___x_1222_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1240_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_1235_,
                );
                v___x_1241_ = l_Lean_PrettyPrinter_delab(
                    v_val_1200_,
                    v___x_1217_,
                    v___y_1178_,
                    v___y_1179_,
                    v___x_1240_,
                    v___y_1237_,
                );
                leanh::lean_dec_ref_known(v___x_1240_, 14);
                if leanh::lean_obj_tag(v___x_1241_) == 0 {
                    v_a_1242_ = leanh::lean_ctor_get(v___x_1241_, 0);
                    leanh::lean_inc(v_a_1242_);
                    leanh::lean_dec_ref_known(v___x_1241_, 1);
                    v___x_1243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__2;
                    v___x_1244_ = l_Lean_PrettyPrinter_ppCategory(
                        v___x_1243_,
                        v_a_1242_,
                        v___y_1180_,
                        v___y_1181_,
                    );
                    if leanh::lean_obj_tag(v___x_1244_) == 0 {
                        v_a_1245_ = leanh::lean_ctor_get(v___x_1244_, 0);
                        leanh::lean_inc(v_a_1245_);
                        leanh::lean_dec_ref_known(v___x_1244_, 1);
                        v___x_1246_ = l_Std_Format_defWidth;
                        v___x_1247_ =
                            l_Std_Format_pretty(v_a_1245_, v___x_1246_, v___x_1188_, v___x_1188_);
                        v_value_1191_ = v___x_1247_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_x27_1189_);
                        leanh::lean_dec(v_fst_1186_);
                        v_a_1248_ = leanh::lean_ctor_get(v___x_1244_, 0);
                        v_isSharedCheck_1255_ =
                            (!leanh::lean_is_exclusive(v___x_1244_)) as u8;
                        if v_isSharedCheck_1255_ == 0 {
                            v___x_1250_ = v___x_1244_;
                            v_isShared_1251_ = v_isSharedCheck_1255_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1248_);
                            leanh::lean_dec(v___x_1244_);
                            v___x_1250_ = leanh::lean_box(0);
                            v_isShared_1251_ = v_isSharedCheck_1255_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_bs_x27_1189_);
                    leanh::lean_dec(v_fst_1186_);
                    v_a_1256_ = leanh::lean_ctor_get(v___x_1241_, 0);
                    v_isSharedCheck_1263_ = (!leanh::lean_is_exclusive(v___x_1241_)) as u8;
                    if v_isSharedCheck_1263_ == 0 {
                        v___x_1258_ = v___x_1241_;
                        v_isShared_1259_ = v_isSharedCheck_1263_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1256_);
                        leanh::lean_dec(v___x_1241_);
                        v___x_1258_ = leanh::lean_box(0);
                        v_isShared_1259_ = v_isSharedCheck_1263_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1251_ == 0 {
                    v___x_1253_ = v___x_1250_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1254_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
                    v___x_1253_ = v_reuseFailAlloc_1254_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1253_;
            }
            5 => {
                if v_isShared_1259_ == 0 {
                    v___x_1261_ = v___x_1258_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1262_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
                    v___x_1261_ = v_reuseFailAlloc_1262_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1261_;
            }
            7 => {
                if v___y_1265_ == 0 {
                    v___x_1266_ = lean_st_ref_take(v___y_1181_);
                    v_env_1267_ = leanh::lean_ctor_get(v___x_1266_, 0);
                    v_nextMacroScope_1268_ = leanh::lean_ctor_get(v___x_1266_, 1);
                    v_ngen_1269_ = leanh::lean_ctor_get(v___x_1266_, 2);
                    v_auxDeclNGen_1270_ = leanh::lean_ctor_get(v___x_1266_, 3);
                    v_traceState_1271_ = leanh::lean_ctor_get(v___x_1266_, 4);
                    v_messages_1272_ = leanh::lean_ctor_get(v___x_1266_, 6);
                    v_infoState_1273_ = leanh::lean_ctor_get(v___x_1266_, 7);
                    v_snapshotTasks_1274_ = leanh::lean_ctor_get(v___x_1266_, 8);
                    v_isSharedCheck_1284_ = (!leanh::lean_is_exclusive(v___x_1266_)) as u8;
                    if v_isSharedCheck_1284_ == 0 {
                        v_unused_1285_ = leanh::lean_ctor_get(v___x_1266_, 5);
                        leanh::lean_dec(v_unused_1285_);
                        v___x_1276_ = v___x_1266_;
                        v_isShared_1277_ = v_isSharedCheck_1284_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_1274_);
                        leanh::lean_inc(v_infoState_1273_);
                        leanh::lean_inc(v_messages_1272_);
                        leanh::lean_inc(v_traceState_1271_);
                        leanh::lean_inc(v_auxDeclNGen_1270_);
                        leanh::lean_inc(v_ngen_1269_);
                        leanh::lean_inc(v_nextMacroScope_1268_);
                        leanh::lean_inc(v_env_1267_);
                        leanh::lean_dec(v___x_1266_);
                        v___x_1276_ = leanh::lean_box(0);
                        v_isShared_1277_ = v_isSharedCheck_1284_;
                        state = 8;
                        continue;
                    }
                } else {
                    v_fileName_1224_ = v_fileName_1202_;
                    v_fileMap_1225_ = v_fileMap_1203_;
                    v_currRecDepth_1226_ = v_currRecDepth_1205_;
                    v_ref_1227_ = v_ref_1206_;
                    v_currNamespace_1228_ = v_currNamespace_1207_;
                    v_openDecls_1229_ = v_openDecls_1208_;
                    v_initHeartbeats_1230_ = v_initHeartbeats_1209_;
                    v_maxHeartbeats_1231_ = v_maxHeartbeats_1210_;
                    v_quotContext_1232_ = v_quotContext_1211_;
                    v_currMacroScope_1233_ = v_currMacroScope_1212_;
                    v_cancelTk_x3f_1234_ = v_cancelTk_x3f_1213_;
                    v_suppressElabErrors_1235_ = v_suppressElabErrors_1214_;
                    v_inheritedTraceOptions_1236_ = v_inheritedTraceOptions_1215_;
                    v___y_1237_ = v___y_1181_;
                    state = 2;
                    continue;
                }
            }
            8 => {
                v___x_1278_ = l_Lean_Kernel_enableDiag(v_env_1267_, v___x_1222_);
                v___x_1279_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__5);
                if v_isShared_1277_ == 0 {
                    leanh::lean_ctor_set(v___x_1276_, 5, v___x_1279_);
                    leanh::lean_ctor_set(v___x_1276_, 0, v___x_1278_);
                    v___x_1281_ = v___x_1276_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1283_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1278_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_nextMacroScope_1268_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 2, v_ngen_1269_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 3, v_auxDeclNGen_1270_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 4, v_traceState_1271_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 5, v___x_1279_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 6, v_messages_1272_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 7, v_infoState_1273_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 8, v_snapshotTasks_1274_);
                    v___x_1281_ = v_reuseFailAlloc_1283_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1282_ = lean_st_ref_set(v___y_1181_, v___x_1281_);
                v_fileName_1224_ = v_fileName_1202_;
                v_fileMap_1225_ = v_fileMap_1203_;
                v_currRecDepth_1226_ = v_currRecDepth_1205_;
                v_ref_1227_ = v_ref_1206_;
                v_currNamespace_1228_ = v_currNamespace_1207_;
                v_openDecls_1229_ = v_openDecls_1208_;
                v_initHeartbeats_1230_ = v_initHeartbeats_1209_;
                v_maxHeartbeats_1231_ = v_maxHeartbeats_1210_;
                v_quotContext_1232_ = v_quotContext_1211_;
                v_currMacroScope_1233_ = v_currMacroScope_1212_;
                v_cancelTk_x3f_1234_ = v_cancelTk_x3f_1213_;
                v_suppressElabErrors_1235_ = v_suppressElabErrors_1214_;
                v_inheritedTraceOptions_1236_ = v_inheritedTraceOptions_1215_;
                v___y_1237_ = v___y_1181_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___boxed(
    mut v_sz_1288_: *mut leanh::LeanObject,
    mut v_i_1289_: *mut leanh::LeanObject,
    mut v_bs_1290_: *mut leanh::LeanObject,
    mut v___y_1291_: *mut leanh::LeanObject,
    mut v___y_1292_: *mut leanh::LeanObject,
    mut v___y_1293_: *mut leanh::LeanObject,
    mut v___y_1294_: *mut leanh::LeanObject,
    mut v___y_1295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1296_: usize = 0;
    let mut v_i_boxed_1297_: usize = 0;
    let mut v_res_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1296_ = leanh::lean_unbox_usize(v_sz_1288_);
    leanh::lean_dec(v_sz_1288_);
    v_i_boxed_1297_ = leanh::lean_unbox_usize(v_i_1289_);
    leanh::lean_dec(v_i_1289_);
    v_res_1298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3(v_sz_boxed_1296_, v_i_boxed_1297_, v_bs_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
    leanh::lean_dec(v___y_1294_);
    leanh::lean_dec_ref(v___y_1293_);
    leanh::lean_dec(v___y_1292_);
    leanh::lean_dec_ref(v___y_1291_);
    return v_res_1298_;
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__5(
    mut v_s_1299_: *mut leanh::LeanObject,
    mut v_pos_1300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: u8 = 0;
    let mut v___y_1312_: u8 = 0;
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: u8 = 0;
    let mut v___x_1316_: u32 = 0;
    let mut v___y_1318_: u8 = 0;
    let mut v___x_1319_: u32 = 0;
    let mut v___x_1320_: u8 = 0;
    let mut v___x_1321_: u32 = 0;
    let mut v___x_1322_: u8 = 0;
    let mut v___x_1323_: u32 = 0;
    let mut v___x_1324_: u8 = 0;
    let mut v___x_1325_: u32 = 0;
    let mut v___x_1326_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1301_ = leanh::lean_ctor_get(v_s_1299_, 0);
                v_startInclusive_1302_ = leanh::lean_ctor_get(v_s_1299_, 1);
                v_endExclusive_1303_ = leanh::lean_ctor_get(v_s_1299_, 2);
                v___x_1304_ = lean_nat_add(v_startInclusive_1302_, v_pos_1300_);
                v___x_1313_ = leanh::lean_unsigned_to_nat(0);
                v___x_1314_ = lean_nat_sub(v_endExclusive_1303_, v___x_1304_);
                v___x_1315_ = lean_nat_dec_eq(v___x_1313_, v___x_1314_);
                leanh::lean_dec(v___x_1314_);
                if v___x_1315_ == 0 {
                    v___x_1316_ = lean_string_utf8_get_fast(v_str_1301_, v___x_1304_);
                    v___x_1323_ = 32;
                    v___x_1324_ = lean_uint32_dec_eq(v___x_1316_, v___x_1323_);
                    if v___x_1324_ == 0 {
                        v___x_1325_ = 9;
                        v___x_1326_ = lean_uint32_dec_eq(v___x_1316_, v___x_1325_);
                        v___y_1318_ = v___x_1326_;
                        state = 3;
                        continue;
                    } else {
                        v___y_1318_ = v___x_1324_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1304_);
                    return v_pos_1300_;
                }
            }
            1 => {
                v___x_1306_ = lean_string_utf8_next_fast(v_str_1301_, v___x_1304_);
                v___x_1307_ = lean_nat_sub(v___x_1306_, v___x_1304_);
                leanh::lean_dec(v___x_1304_);
                v___x_1308_ = lean_nat_add(v_pos_1300_, v___x_1307_);
                leanh::lean_dec(v___x_1307_);
                v___x_1309_ = lean_nat_dec_lt(v_pos_1300_, v___x_1308_);
                if v___x_1309_ == 0 {
                    leanh::lean_dec(v___x_1308_);
                    return v_pos_1300_;
                } else {
                    leanh::lean_dec(v_pos_1300_);
                    v_pos_1300_ = v___x_1308_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_1312_ == 0 {
                    leanh::lean_dec(v___x_1304_);
                    return v_pos_1300_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_1318_ == 0 {
                    v___x_1319_ = 13;
                    v___x_1320_ = lean_uint32_dec_eq(v___x_1316_, v___x_1319_);
                    if v___x_1320_ == 0 {
                        v___x_1321_ = 10;
                        v___x_1322_ = lean_uint32_dec_eq(v___x_1316_, v___x_1321_);
                        v___y_1312_ = v___x_1322_;
                        state = 2;
                        continue;
                    } else {
                        v___y_1312_ = v___x_1320_;
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
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__5___boxed(
    mut v_s_1327_: *mut leanh::LeanObject,
    mut v_pos_1328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1329_ =
        l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__5(
            v_s_1327_,
            v_pos_1328_,
        );
    leanh::lean_dec_ref(v_s_1327_);
    return v_res_1329_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8(
    mut v_as_1332_: *mut leanh::LeanObject,
    mut v_i_1333_: usize,
    mut v_stop_1334_: usize,
    mut v_b_1335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1336_: u8 = 0;
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: usize = 0;
    let mut v___x_1345_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1336_ = lean_usize_dec_eq(v_i_1333_, v_stop_1334_);
                if v___x_1336_ == 0 {
                    v___x_1337_ = lean_array_uget_borrowed(v_as_1332_, v_i_1333_);
                    v___x_1338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8___closed__0;
                    v___x_1339_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1339_, 0, v_b_1335_);
                    leanh::lean_ctor_set(v___x_1339_, 1, v___x_1338_);
                    v___x_1340_ = leanh::lean_box(1);
                    v___x_1341_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1341_, 0, v___x_1339_);
                    leanh::lean_ctor_set(v___x_1341_, 1, v___x_1340_);
                    leanh::lean_inc(v___x_1337_);
                    v___x_1342_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1342_, 0, v___x_1337_);
                    v___x_1343_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1343_, 0, v___x_1341_);
                    leanh::lean_ctor_set(v___x_1343_, 1, v___x_1342_);
                    v___x_1344_ = 1usize;
                    v___x_1345_ = lean_usize_add(v_i_1333_, v___x_1344_);
                    v_i_1333_ = v___x_1345_;
                    v_b_1335_ = v___x_1343_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1335_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8___boxed(
    mut v_as_1347_: *mut leanh::LeanObject,
    mut v_i_1348_: *mut leanh::LeanObject,
    mut v_stop_1349_: *mut leanh::LeanObject,
    mut v_b_1350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1351_: usize = 0;
    let mut v_stop_boxed_1352_: usize = 0;
    let mut v_res_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1351_ = leanh::lean_unbox_usize(v_i_1348_);
    leanh::lean_dec(v_i_1348_);
    v_stop_boxed_1352_ = leanh::lean_unbox_usize(v_stop_1349_);
    leanh::lean_dec(v_stop_1349_);
    v_res_1353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8(v_as_1347_, v_i_boxed_1351_, v_stop_boxed_1352_, v_b_1350_);
    leanh::lean_dec_ref(v_as_1347_);
    return v_res_1353_;
}
pub unsafe fn _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1358_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__2;
    v___x_1359_ = l_Lean_stringToMessageData(v___x_1358_);
    return v___x_1359_;
}
pub unsafe fn _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1366_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__8;
    v___x_1367_ = leanh::lean_unsigned_to_nat(14);
    v___x_1368_ = leanh::lean_unsigned_to_nat(22);
    v___x_1369_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__7;
    v___x_1370_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__6;
    v___x_1371_ = l_mkPanicMessageWithDecl(
        v___x_1370_,
        v___x_1369_,
        v___x_1368_,
        v___x_1367_,
        v___x_1366_,
    );
    return v___x_1371_;
}
pub unsafe fn _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_1372_: u32 = 0;
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1372_ = 32;
    v___x_1373_ = leanh::lean_box_uint32(v___x_1372_);
    return v___x_1373_;
}
pub unsafe fn l_Lean_Elab_Term_StructInst_mkMissingFieldsHint(
    mut v_fields_1374_: *mut leanh::LeanObject,
    mut v_stx_1375_: *mut leanh::LeanObject,
    mut v_a_1376_: *mut leanh::LeanObject,
    mut v_a_1377_: *mut leanh::LeanObject,
    mut v_a_1378_: *mut leanh::LeanObject,
    mut v_a_1379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1385_: u8 = 0;
    let mut v_sz_1386_: usize = 0;
    let mut v___x_1387_: usize = 0;
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1394_: u8 = 0;
    let mut v___x_1395_: u8 = 0;
    let mut v___y_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: u8 = 0;
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: u8 = 0;
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1472_: u8 = 0;
    let mut v___y_1473_: u8 = 0;
    let mut v___y_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: u8 = 0;
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: u8 = 0;
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1488_: u8 = 0;
    let mut v___y_1489_: u8 = 0;
    let mut v___y_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1501_: u8 = 0;
    let mut v___y_1502_: u8 = 0;
    let mut v___y_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: u8 = 0;
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: u8 = 0;
    let mut v___y_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1522_: u8 = 0;
    let mut v___y_1523_: u8 = 0;
    let mut v___y_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastFieldTailPos_x3f_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasWith_1539_: u8 = 0;
    let mut v_numFields_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leaderPos_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leaderTailPos_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_closingPos_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: u8 = 0;
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: u8 = 0;
    let mut v_source_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: u8 = 0;
    let mut v___x_1559_: u8 = 0;
    let mut v___x_1560_: u8 = 0;
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initFieldPos_x3f_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openingPos_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_closingPos_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: u8 = 0;
    let mut v___y_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: u8 = 0;
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: u8 = 0;
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: u8 = 0;
    let mut v___x_1596_: u8 = 0;
    let mut v___x_1597_: usize = 0;
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: usize = 0;
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1601_: u8 = 0;
    let mut v_a_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1605_: u8 = 0;
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1609_: u8 = 0;
    let mut v_isSharedCheck_1610_: u8 = 0;
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_stx_1375_);
                v___x_1381_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f(v_stx_1375_);
                if leanh::lean_obj_tag(v___x_1381_) == 1 {
                    v_val_1382_ = leanh::lean_ctor_get(v___x_1381_, 0);
                    v_isSharedCheck_1610_ = (!leanh::lean_is_exclusive(v___x_1381_)) as u8;
                    if v_isSharedCheck_1610_ == 0 {
                        v___x_1384_ = v___x_1381_;
                        v_isShared_1385_ = v_isSharedCheck_1610_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1382_);
                        leanh::lean_dec(v___x_1381_);
                        v___x_1384_ = leanh::lean_box(0);
                        v_isShared_1385_ = v_isSharedCheck_1610_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1381_);
                    leanh::lean_dec(v_stx_1375_);
                    leanh::lean_dec_ref(v_fields_1374_);
                    v___x_1611_ = l_Lean_MessageData_nil;
                    v___x_1612_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1612_, 0, v___x_1611_);
                    return v___x_1612_;
                }
            }
            1 => {
                v_sz_1386_ = lean_array_size(v_fields_1374_);
                v___x_1387_ = 0usize;
                v___x_1388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3(v_sz_1386_, v___x_1387_, v_fields_1374_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_);
                if leanh::lean_obj_tag(v___x_1388_) == 0 {
                    v_a_1389_ = leanh::lean_ctor_get(v___x_1388_, 0);
                    leanh::lean_inc(v_a_1389_);
                    leanh::lean_dec_ref_known(v___x_1388_, 1);
                    v___x_1390_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg(v_stx_1375_, v_val_1382_, v_a_1378_);
                    leanh::lean_dec(v_stx_1375_);
                    v_a_1391_ = leanh::lean_ctor_get(v___x_1390_, 0);
                    v_isSharedCheck_1601_ = (!leanh::lean_is_exclusive(v___x_1390_)) as u8;
                    if v_isSharedCheck_1601_ == 0 {
                        v___x_1393_ = v___x_1390_;
                        v_isShared_1394_ = v_isSharedCheck_1601_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1391_);
                        leanh::lean_dec(v___x_1390_);
                        v___x_1393_ = leanh::lean_box(0);
                        v_isShared_1394_ = v_isSharedCheck_1601_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1384_);
                    leanh::lean_dec(v_val_1382_);
                    leanh::lean_dec(v_stx_1375_);
                    v_a_1602_ = leanh::lean_ctor_get(v___x_1388_, 0);
                    v_isSharedCheck_1609_ = (!leanh::lean_is_exclusive(v___x_1388_)) as u8;
                    if v_isSharedCheck_1609_ == 0 {
                        v___x_1604_ = v___x_1388_;
                        v_isShared_1605_ = v_isSharedCheck_1609_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1602_);
                        leanh::lean_dec(v___x_1388_);
                        v___x_1604_ = leanh::lean_box(0);
                        v_isShared_1605_ = v_isSharedCheck_1609_;
                        state = 17;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1395_ = 1;
                v___x_1588_ = (leanh::lean_unbox(v_a_1391_) as u8);
                if v___x_1588_ == 0 {
                    v___x_1589_ = lean_array_to_list(v_a_1389_);
                    v___x_1590_ = leanh::lean_box(1);
                    v___x_1591_ = l_Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7(v___x_1589_, v___x_1590_);
                    v___y_1572_ = v___x_1591_;
                    state = 15;
                    continue;
                } else {
                    v___x_1592_ = leanh::lean_box(0);
                    v___x_1593_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1594_ = lean_array_get_size(v_a_1389_);
                    v___x_1595_ = lean_nat_dec_lt(v___x_1593_, v___x_1594_);
                    if v___x_1595_ == 0 {
                        leanh::lean_dec(v_a_1389_);
                        v___y_1585_ = v___x_1592_;
                        state = 16;
                        continue;
                    } else {
                        v___x_1596_ = lean_nat_dec_le(v___x_1594_, v___x_1594_);
                        if v___x_1596_ == 0 {
                            if v___x_1595_ == 0 {
                                leanh::lean_dec(v_a_1389_);
                                v___y_1585_ = v___x_1592_;
                                state = 16;
                                continue;
                            } else {
                                v___x_1597_ = lean_usize_of_nat(v___x_1594_);
                                v___x_1598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8(v_a_1389_, v___x_1387_, v___x_1597_, v___x_1592_);
                                leanh::lean_dec(v_a_1389_);
                                v___y_1585_ = v___x_1598_;
                                state = 16;
                                continue;
                            }
                        } else {
                            v___x_1599_ = lean_usize_of_nat(v___x_1594_);
                            v___x_1600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8(v_a_1389_, v___x_1387_, v___x_1599_, v___x_1592_);
                            leanh::lean_dec(v_a_1389_);
                            v___y_1585_ = v___x_1600_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_1402_ = l_Lean_Meta_Tactic_TryThis_format_inputWidth;
                v___x_1403_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2(v___y_1400_, v___x_1402_);
                leanh::lean_inc(v___y_1401_);
                v___x_1404_ = leanh::lean_apply_1(v___y_1398_, v___y_1401_);
                v___x_1405_ =
                    l_Std_Format_pretty(v___y_1399_, v___x_1403_, v___y_1397_, v___x_1404_);
                leanh::lean_dec(v___x_1403_);
                if v_isShared_1394_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1393_, 1);
                    leanh::lean_ctor_set(v___x_1393_, 0, v___x_1405_);
                    v___x_1407_ = v___x_1393_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1424_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1405_);
                    v___x_1407_ = v_reuseFailAlloc_1424_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1408_ = leanh::lean_box(0);
                v___x_1409_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__1;
                v___x_1410_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                leanh::lean_ctor_set(v___x_1410_, 0, v___x_1407_);
                leanh::lean_ctor_set(v___x_1410_, 1, v___x_1408_);
                leanh::lean_ctor_set(v___x_1410_, 2, v___x_1408_);
                leanh::lean_ctor_set(v___x_1410_, 3, v___x_1408_);
                leanh::lean_ctor_set(v___x_1410_, 4, v___x_1408_);
                leanh::lean_ctor_set(v___x_1410_, 5, v___x_1409_);
                leanh::lean_inc(v___y_1401_);
                v___x_1411_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1411_, 0, v___y_1401_);
                leanh::lean_ctor_set(v___x_1411_, 1, v___y_1401_);
                v___x_1412_ = l_Lean_Syntax_ofRange(v___x_1411_, v___x_1395_);
                if v_isShared_1385_ == 0 {
                    leanh::lean_ctor_set(v___x_1384_, 0, v___x_1412_);
                    v___x_1414_ = v___x_1384_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1423_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1412_);
                    v___x_1414_ = v_reuseFailAlloc_1423_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1415_ = 0;
                v___x_1416_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                leanh::lean_ctor_set(v___x_1416_, 0, v___x_1410_);
                leanh::lean_ctor_set(v___x_1416_, 1, v___x_1414_);
                leanh::lean_ctor_set(v___x_1416_, 2, v___x_1408_);
                leanh::lean_ctor_set_uint8(
                    v___x_1416_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_1415_,
                );
                v___x_1417_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3_once
                    ),
                    _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3,
                );
                v___x_1418_ = leanh::lean_unsigned_to_nat(1);
                v___x_1419_ = lean_mk_empty_array_with_capacity(v___x_1418_);
                v___x_1420_ = lean_array_push(v___x_1419_, v___x_1416_);
                v___x_1421_ = 0;
                v___x_1422_ = l_Lean_MessageData_hint(
                    v___x_1417_,
                    v___x_1420_,
                    v___x_1408_,
                    v___x_1408_,
                    v___x_1421_,
                    v_a_1378_,
                    v_a_1379_,
                );
                leanh::lean_dec_ref(v___x_1420_);
                return v___x_1422_;
            }
            6 => {
                v___x_1435_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1435_, 0, v_fst_1433_);
                leanh::lean_ctor_set(v___x_1435_, 1, v___y_1430_);
                v___x_1436_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1436_, 0, v___x_1435_);
                leanh::lean_ctor_set(v___x_1436_, 1, v_snd_1434_);
                if leanh::lean_obj_tag(v___y_1431_) == 0 {
                    if leanh::lean_obj_tag(v___y_1429_) == 0 {
                        v___y_1397_ = v___y_1426_;
                        v___y_1398_ = v___y_1428_;
                        v___y_1399_ = v___x_1436_;
                        v___y_1400_ = v___y_1432_;
                        v___y_1401_ = v___y_1427_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___y_1427_);
                        v_val_1437_ = leanh::lean_ctor_get(v___y_1429_, 0);
                        leanh::lean_inc(v_val_1437_);
                        leanh::lean_dec_ref_known(v___y_1429_, 1);
                        v___y_1397_ = v___y_1426_;
                        v___y_1398_ = v___y_1428_;
                        v___y_1399_ = v___x_1436_;
                        v___y_1400_ = v___y_1432_;
                        v___y_1401_ = v_val_1437_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_1429_);
                    leanh::lean_dec(v___y_1427_);
                    v_val_1438_ = leanh::lean_ctor_get(v___y_1431_, 0);
                    leanh::lean_inc(v_val_1438_);
                    leanh::lean_dec_ref_known(v___y_1431_, 1);
                    v___y_1397_ = v___y_1426_;
                    v___y_1398_ = v___y_1428_;
                    v___y_1399_ = v___x_1436_;
                    v___y_1400_ = v___y_1432_;
                    v___y_1401_ = v_val_1438_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                v___x_1447_ = leanh::lean_box(1);
                v___x_1448_ = leanh::lean_box(0);
                v___y_1426_ = v___y_1440_;
                v___y_1427_ = v___y_1441_;
                v___y_1428_ = v___y_1442_;
                v___y_1429_ = v___y_1444_;
                v___y_1430_ = v___y_1443_;
                v___y_1431_ = v___y_1445_;
                v___y_1432_ = v___y_1446_;
                v_fst_1433_ = v___x_1447_;
                v_snd_1434_ = v___x_1448_;
                state = 6;
                continue;
            }
            8 => {
                if leanh::lean_obj_tag(v___y_1454_) == 0 {
                    v___x_1457_ = leanh::lean_box(1);
                    v___x_1458_ = leanh::lean_box(0);
                    v___y_1426_ = v___y_1450_;
                    v___y_1427_ = v___y_1451_;
                    v___y_1428_ = v___y_1452_;
                    v___y_1429_ = v___y_1454_;
                    v___y_1430_ = v___y_1453_;
                    v___y_1431_ = v___y_1455_;
                    v___y_1432_ = v___y_1456_;
                    v_fst_1433_ = v___x_1457_;
                    v_snd_1434_ = v___x_1458_;
                    state = 6;
                    continue;
                } else {
                    v_val_1459_ = leanh::lean_ctor_get(v___y_1454_, 0);
                    leanh::lean_inc_ref(v___y_1452_);
                    leanh::lean_inc(v_val_1459_);
                    v___x_1460_ = leanh::lean_apply_1(v___y_1452_, v_val_1459_);
                    v___x_1461_ = lean_nat_sub(v___y_1450_, v___x_1460_);
                    leanh::lean_dec(v___x_1460_);
                    v___x_1462_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed__const__1;
                    v___x_1463_ = l_List_replicateTR___redArg(v___x_1461_, v___x_1462_);
                    v___x_1464_ = lean_string_mk(v___x_1463_);
                    v___x_1465_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1465_, 0, v___x_1464_);
                    v___x_1466_ = leanh::lean_box(0);
                    v___y_1426_ = v___y_1450_;
                    v___y_1427_ = v___y_1451_;
                    v___y_1428_ = v___y_1452_;
                    v___y_1429_ = v___y_1454_;
                    v___y_1430_ = v___y_1453_;
                    v___y_1431_ = v___y_1455_;
                    v___y_1432_ = v___y_1456_;
                    v_fst_1433_ = v___x_1465_;
                    v_snd_1434_ = v___x_1466_;
                    state = 6;
                    continue;
                }
            }
            9 => {
                v___x_1478_ = (leanh::lean_unbox(v_a_1391_) as u8);
                leanh::lean_dec(v_a_1391_);
                if v___x_1478_ == 0 {
                    v___x_1479_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1480_ = lean_nat_dec_lt(v___x_1479_, v___y_1469_);
                    leanh::lean_dec(v___y_1469_);
                    if v___x_1480_ == 0 {
                        if v___y_1472_ == 0 {
                            if v___y_1473_ == 0 {
                                v___x_1481_ =
                                    l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__5;
                                v___y_1426_ = v___y_1468_;
                                v___y_1427_ = v___y_1470_;
                                v___y_1428_ = v___y_1471_;
                                v___y_1429_ = v___y_1477_;
                                v___y_1430_ = v___y_1474_;
                                v___y_1431_ = v___y_1475_;
                                v___y_1432_ = v___y_1476_;
                                v_fst_1433_ = v___x_1481_;
                                v_snd_1434_ = v___x_1481_;
                                state = 6;
                                continue;
                            } else {
                                v___y_1450_ = v___y_1468_;
                                v___y_1451_ = v___y_1470_;
                                v___y_1452_ = v___y_1471_;
                                v___y_1453_ = v___y_1474_;
                                v___y_1454_ = v___y_1477_;
                                v___y_1455_ = v___y_1475_;
                                v___y_1456_ = v___y_1476_;
                                state = 8;
                                continue;
                            }
                        } else {
                            if v___y_1473_ == 0 {
                                v___y_1440_ = v___y_1468_;
                                v___y_1441_ = v___y_1470_;
                                v___y_1442_ = v___y_1471_;
                                v___y_1443_ = v___y_1474_;
                                v___y_1444_ = v___y_1477_;
                                v___y_1445_ = v___y_1475_;
                                v___y_1446_ = v___y_1476_;
                                state = 7;
                                continue;
                            } else {
                                if v___x_1480_ == 0 {
                                    v___y_1450_ = v___y_1468_;
                                    v___y_1451_ = v___y_1470_;
                                    v___y_1452_ = v___y_1471_;
                                    v___y_1453_ = v___y_1474_;
                                    v___y_1454_ = v___y_1477_;
                                    v___y_1455_ = v___y_1475_;
                                    v___y_1456_ = v___y_1476_;
                                    state = 8;
                                    continue;
                                } else {
                                    v___y_1440_ = v___y_1468_;
                                    v___y_1441_ = v___y_1470_;
                                    v___y_1442_ = v___y_1471_;
                                    v___y_1443_ = v___y_1474_;
                                    v___y_1444_ = v___y_1477_;
                                    v___y_1445_ = v___y_1475_;
                                    v___y_1446_ = v___y_1476_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___y_1440_ = v___y_1468_;
                        v___y_1441_ = v___y_1470_;
                        v___y_1442_ = v___y_1471_;
                        v___y_1443_ = v___y_1474_;
                        v___y_1444_ = v___y_1477_;
                        v___y_1445_ = v___y_1475_;
                        v___y_1446_ = v___y_1476_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_1469_);
                    v___x_1482_ = leanh::lean_box(0);
                    v___y_1426_ = v___y_1468_;
                    v___y_1427_ = v___y_1470_;
                    v___y_1428_ = v___y_1471_;
                    v___y_1429_ = v___y_1477_;
                    v___y_1430_ = v___y_1474_;
                    v___y_1431_ = v___y_1475_;
                    v___y_1432_ = v___y_1476_;
                    v_fst_1433_ = v___x_1482_;
                    v_snd_1434_ = v___x_1482_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                v___x_1494_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1494_, 0, v___y_1493_);
                v___y_1468_ = v___y_1484_;
                v___y_1469_ = v___y_1486_;
                v___y_1470_ = v___y_1485_;
                v___y_1471_ = v___y_1487_;
                v___y_1472_ = v___y_1489_;
                v___y_1473_ = v___y_1488_;
                v___y_1474_ = v___y_1490_;
                v___y_1475_ = v___y_1491_;
                v___y_1476_ = v___y_1492_;
                v___y_1477_ = v___x_1494_;
                state = 9;
                continue;
            }
            11 => {
                v___x_1510_ = leanh::lean_unsigned_to_nat(0);
                v___x_1511_ = l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__5(v___y_1507_, v___x_1510_);
                leanh::lean_dec_ref(v___y_1507_);
                v___x_1512_ = lean_nat_sub(v_endExclusive_1509_, v_startInclusive_1508_);
                leanh::lean_dec(v_startInclusive_1508_);
                leanh::lean_dec(v_endExclusive_1509_);
                v___x_1513_ = lean_nat_dec_eq(v___x_1511_, v___x_1512_);
                leanh::lean_dec(v___x_1512_);
                leanh::lean_dec(v___x_1511_);
                if v___x_1513_ == 0 {
                    leanh::lean_dec(v___y_1503_);
                    leanh::lean_dec(v___y_1499_);
                    v___x_1514_ = leanh::lean_box(0);
                    v___y_1468_ = v___y_1496_;
                    v___y_1469_ = v___y_1498_;
                    v___y_1470_ = v___y_1497_;
                    v___y_1471_ = v___y_1500_;
                    v___y_1472_ = v___y_1502_;
                    v___y_1473_ = v___y_1501_;
                    v___y_1474_ = v___y_1504_;
                    v___y_1475_ = v___y_1505_;
                    v___y_1476_ = v___y_1506_;
                    v___y_1477_ = v___x_1514_;
                    state = 9;
                    continue;
                } else {
                    v___x_1515_ = lean_nat_dec_le(v___y_1503_, v___y_1499_);
                    if v___x_1515_ == 0 {
                        leanh::lean_dec(v___y_1503_);
                        v___y_1484_ = v___y_1496_;
                        v___y_1485_ = v___y_1497_;
                        v___y_1486_ = v___y_1498_;
                        v___y_1487_ = v___y_1500_;
                        v___y_1488_ = v___y_1501_;
                        v___y_1489_ = v___y_1502_;
                        v___y_1490_ = v___y_1504_;
                        v___y_1491_ = v___y_1505_;
                        v___y_1492_ = v___y_1506_;
                        v___y_1493_ = v___y_1499_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_dec(v___y_1499_);
                        v___y_1484_ = v___y_1496_;
                        v___y_1485_ = v___y_1497_;
                        v___y_1486_ = v___y_1498_;
                        v___y_1487_ = v___y_1500_;
                        v___y_1488_ = v___y_1501_;
                        v___y_1489_ = v___y_1502_;
                        v___y_1490_ = v___y_1504_;
                        v___y_1491_ = v___y_1505_;
                        v___y_1492_ = v___y_1506_;
                        v___y_1493_ = v___y_1503_;
                        state = 10;
                        continue;
                    }
                }
            }
            12 => {
                v___x_1528_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9_once
                    ),
                    _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9,
                );
                v___x_1529_ =
                    l_panic___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__6(
                        v___x_1528_,
                    );
                v_startInclusive_1530_ = leanh::lean_ctor_get(v___x_1529_, 1);
                leanh::lean_inc(v_startInclusive_1530_);
                v_endExclusive_1531_ = leanh::lean_ctor_get(v___x_1529_, 2);
                leanh::lean_inc(v_endExclusive_1531_);
                v___y_1496_ = v___y_1517_;
                v___y_1497_ = v___y_1519_;
                v___y_1498_ = v___y_1518_;
                v___y_1499_ = v___y_1521_;
                v___y_1500_ = v___y_1520_;
                v___y_1501_ = v___y_1523_;
                v___y_1502_ = v___y_1522_;
                v___y_1503_ = v___y_1524_;
                v___y_1504_ = v___y_1525_;
                v___y_1505_ = v___y_1526_;
                v___y_1506_ = v___y_1527_;
                v___y_1507_ = v___x_1529_;
                v_startInclusive_1508_ = v_startInclusive_1530_;
                v_endExclusive_1509_ = v_endExclusive_1531_;
                state = 11;
                continue;
            }
            13 => {
                v_lastFieldTailPos_x3f_1538_ = leanh::lean_ctor_get(v_val_1382_, 1);
                leanh::lean_inc(v_lastFieldTailPos_x3f_1538_);
                v_hasWith_1539_ = leanh::lean_ctor_get_uint8(
                    v_val_1382_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_numFields_1540_ = leanh::lean_ctor_get(v_val_1382_, 2);
                leanh::lean_inc(v_numFields_1540_);
                v_leaderPos_1541_ = leanh::lean_ctor_get(v_val_1382_, 4);
                leanh::lean_inc(v_leaderPos_1541_);
                v_leaderTailPos_1542_ = leanh::lean_ctor_get(v_val_1382_, 5);
                leanh::lean_inc(v_leaderTailPos_1542_);
                v_closingPos_1543_ = leanh::lean_ctor_get(v_val_1382_, 6);
                leanh::lean_inc(v_closingPos_1543_);
                leanh::lean_dec(v_val_1382_);
                leanh::lean_inc_ref_n(v___y_1533_, 2);
                v___x_1544_ = l_Lean_FileMap_utf8PosToLspPos(v___y_1533_, v_leaderPos_1541_);
                leanh::lean_dec(v_leaderPos_1541_);
                v_line_1545_ = leanh::lean_ctor_get(v___x_1544_, 0);
                leanh::lean_inc(v_line_1545_);
                leanh::lean_dec_ref(v___x_1544_);
                v___x_1546_ = l_Lean_FileMap_utf8PosToLspPos(v___y_1533_, v_closingPos_1543_);
                leanh::lean_dec(v_closingPos_1543_);
                v_line_1547_ = leanh::lean_ctor_get(v___x_1546_, 0);
                leanh::lean_inc(v_line_1547_);
                leanh::lean_dec_ref(v___x_1546_);
                v___x_1548_ = lean_nat_dec_lt(v_line_1545_, v_line_1547_);
                v___x_1549_ = leanh::lean_unsigned_to_nat(1);
                v___x_1550_ = lean_nat_add(v_line_1545_, v___x_1549_);
                leanh::lean_dec(v_line_1545_);
                v___x_1551_ = lean_nat_dec_le(v_line_1547_, v___x_1550_);
                leanh::lean_dec(v___x_1550_);
                leanh::lean_dec(v_line_1547_);
                if v___x_1551_ == 0 {
                    v_source_1552_ = leanh::lean_ctor_get(v___y_1533_, 0);
                    leanh::lean_inc_ref_n(v_source_1552_, 3);
                    leanh::lean_dec_ref(v___y_1533_);
                    v___x_1553_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd(v_source_1552_, v_leaderTailPos_1542_);
                    v___x_1554_ = lean_nat_add(v___y_1537_, v___x_1549_);
                    leanh::lean_inc(v___x_1553_);
                    v___x_1555_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___redArg(v_source_1552_, v___x_1554_, v___x_1553_);
                    v___x_1556_ = lean_string_utf8_next(v_source_1552_, v___x_1553_);
                    leanh::lean_dec(v___x_1553_);
                    v___x_1557_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd(v_source_1552_, v___x_1556_);
                    leanh::lean_dec(v___x_1556_);
                    v___x_1558_ = lean_string_is_valid_pos(v_source_1552_, v_leaderTailPos_1542_);
                    if v___x_1558_ == 0 {
                        leanh::lean_dec_ref(v_source_1552_);
                        v___y_1517_ = v___y_1537_;
                        v___y_1518_ = v_numFields_1540_;
                        v___y_1519_ = v_leaderTailPos_1542_;
                        v___y_1520_ = v___y_1534_;
                        v___y_1521_ = v___x_1557_;
                        v___y_1522_ = v_hasWith_1539_;
                        v___y_1523_ = v___x_1548_;
                        v___y_1524_ = v___x_1555_;
                        v___y_1525_ = v___y_1535_;
                        v___y_1526_ = v_lastFieldTailPos_x3f_1538_;
                        v___y_1527_ = v___y_1536_;
                        state = 12;
                        continue;
                    } else {
                        v___x_1559_ = lean_string_is_valid_pos(v_source_1552_, v___x_1557_);
                        if v___x_1559_ == 0 {
                            leanh::lean_dec_ref(v_source_1552_);
                            v___y_1517_ = v___y_1537_;
                            v___y_1518_ = v_numFields_1540_;
                            v___y_1519_ = v_leaderTailPos_1542_;
                            v___y_1520_ = v___y_1534_;
                            v___y_1521_ = v___x_1557_;
                            v___y_1522_ = v_hasWith_1539_;
                            v___y_1523_ = v___x_1548_;
                            v___y_1524_ = v___x_1555_;
                            v___y_1525_ = v___y_1535_;
                            v___y_1526_ = v_lastFieldTailPos_x3f_1538_;
                            v___y_1527_ = v___y_1536_;
                            state = 12;
                            continue;
                        } else {
                            v___x_1560_ = lean_nat_dec_le(v_leaderTailPos_1542_, v___x_1557_);
                            if v___x_1560_ == 0 {
                                leanh::lean_dec_ref(v_source_1552_);
                                v___y_1517_ = v___y_1537_;
                                v___y_1518_ = v_numFields_1540_;
                                v___y_1519_ = v_leaderTailPos_1542_;
                                v___y_1520_ = v___y_1534_;
                                v___y_1521_ = v___x_1557_;
                                v___y_1522_ = v_hasWith_1539_;
                                v___y_1523_ = v___x_1548_;
                                v___y_1524_ = v___x_1555_;
                                v___y_1525_ = v___y_1535_;
                                v___y_1526_ = v_lastFieldTailPos_x3f_1538_;
                                v___y_1527_ = v___y_1536_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc_n(v___x_1557_, 2);
                                leanh::lean_inc_n(v_leaderTailPos_1542_, 2);
                                v___x_1561_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                leanh::lean_ctor_set(v___x_1561_, 0, v_source_1552_);
                                leanh::lean_ctor_set(v___x_1561_, 1, v_leaderTailPos_1542_);
                                leanh::lean_ctor_set(v___x_1561_, 2, v___x_1557_);
                                v___y_1496_ = v___y_1537_;
                                v___y_1497_ = v_leaderTailPos_1542_;
                                v___y_1498_ = v_numFields_1540_;
                                v___y_1499_ = v___x_1557_;
                                v___y_1500_ = v___y_1534_;
                                v___y_1501_ = v___x_1548_;
                                v___y_1502_ = v_hasWith_1539_;
                                v___y_1503_ = v___x_1555_;
                                v___y_1504_ = v___y_1535_;
                                v___y_1505_ = v_lastFieldTailPos_x3f_1538_;
                                v___y_1506_ = v___y_1536_;
                                v___y_1507_ = v___x_1561_;
                                v_startInclusive_1508_ = v_leaderTailPos_1542_;
                                v_endExclusive_1509_ = v___x_1557_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_1533_);
                    v___x_1562_ = leanh::lean_box(0);
                    v___y_1468_ = v___y_1537_;
                    v___y_1469_ = v_numFields_1540_;
                    v___y_1470_ = v_leaderTailPos_1542_;
                    v___y_1471_ = v___y_1534_;
                    v___y_1472_ = v_hasWith_1539_;
                    v___y_1473_ = v___x_1548_;
                    v___y_1474_ = v___y_1535_;
                    v___y_1475_ = v_lastFieldTailPos_x3f_1538_;
                    v___y_1476_ = v___y_1536_;
                    v___y_1477_ = v___x_1562_;
                    state = 9;
                    continue;
                }
            }
            14 => {
                v___x_1569_ = leanh::lean_unsigned_to_nat(2);
                v___x_1570_ = lean_nat_add(v___y_1568_, v___x_1569_);
                leanh::lean_dec(v___y_1568_);
                v___y_1533_ = v___y_1564_;
                v___y_1534_ = v___y_1565_;
                v___y_1535_ = v___y_1566_;
                v___y_1536_ = v___y_1567_;
                v___y_1537_ = v___x_1570_;
                state = 13;
                continue;
            }
            15 => {
                v_fileMap_1573_ = leanh::lean_ctor_get(v_a_1378_, 1);
                v_options_1574_ = leanh::lean_ctor_get(v_a_1378_, 2);
                v_initFieldPos_x3f_1575_ = leanh::lean_ctor_get(v_val_1382_, 0);
                v_openingPos_1576_ = leanh::lean_ctor_get(v_val_1382_, 3);
                v_closingPos_1577_ = leanh::lean_ctor_get(v_val_1382_, 6);
                leanh::lean_inc_ref(v_fileMap_1573_);
                v___f_1578_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_1578_, 0, v_fileMap_1573_);
                if leanh::lean_obj_tag(v_initFieldPos_x3f_1575_) == 1 {
                    v_val_1579_ = leanh::lean_ctor_get(v_initFieldPos_x3f_1575_, 0);
                    leanh::lean_inc_ref_n(v_fileMap_1573_, 2);
                    v___x_1580_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(
                        v_fileMap_1573_,
                        v_val_1579_,
                    );
                    v___y_1533_ = v_fileMap_1573_;
                    v___y_1534_ = v___f_1578_;
                    v___y_1535_ = v___y_1572_;
                    v___y_1536_ = v_options_1574_;
                    v___y_1537_ = v___x_1580_;
                    state = 13;
                    continue;
                } else {
                    leanh::lean_inc_ref_n(v_fileMap_1573_, 2);
                    v___x_1581_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(
                        v_fileMap_1573_,
                        v_openingPos_1576_,
                    );
                    v___x_1582_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(
                        v_fileMap_1573_,
                        v_closingPos_1577_,
                    );
                    v___x_1583_ = lean_nat_dec_le(v___x_1581_, v___x_1582_);
                    if v___x_1583_ == 0 {
                        leanh::lean_dec(v___x_1581_);
                        leanh::lean_inc_ref(v_fileMap_1573_);
                        v___y_1564_ = v_fileMap_1573_;
                        v___y_1565_ = v___f_1578_;
                        v___y_1566_ = v___y_1572_;
                        v___y_1567_ = v_options_1574_;
                        v___y_1568_ = v___x_1582_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1582_);
                        leanh::lean_inc_ref(v_fileMap_1573_);
                        v___y_1564_ = v_fileMap_1573_;
                        v___y_1565_ = v___f_1578_;
                        v___y_1566_ = v___y_1572_;
                        v___y_1567_ = v_options_1574_;
                        v___y_1568_ = v___x_1581_;
                        state = 14;
                        continue;
                    }
                }
            }
            16 => {
                v___x_1586_ = 1;
                v___x_1587_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1587_, 0, v___y_1585_);
                leanh::lean_ctor_set_uint8(
                    v___x_1587_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1586_,
                );
                v___y_1572_ = v___x_1587_;
                state = 15;
                continue;
            }
            17 => {
                if v_isShared_1605_ == 0 {
                    v___x_1607_ = v___x_1604_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1608_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
                    v___x_1607_ = v_reuseFailAlloc_1608_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1607_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed(
    mut v_fields_1613_: *mut leanh::LeanObject,
    mut v_stx_1614_: *mut leanh::LeanObject,
    mut v_a_1615_: *mut leanh::LeanObject,
    mut v_a_1616_: *mut leanh::LeanObject,
    mut v_a_1617_: *mut leanh::LeanObject,
    mut v_a_1618_: *mut leanh::LeanObject,
    mut v_a_1619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1620_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint(
        v_fields_1613_,
        v_stx_1614_,
        v_a_1615_,
        v_a_1616_,
        v_a_1617_,
        v_a_1618_,
    );
    leanh::lean_dec(v_a_1618_);
    leanh::lean_dec_ref(v_a_1617_);
    leanh::lean_dec(v_a_1616_);
    leanh::lean_dec_ref(v_a_1615_);
    return v_res_1620_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4(
    mut v___x_1621_: *mut leanh::LeanObject,
    mut v_n_1622_: *mut leanh::LeanObject,
    mut v_j_1623_: *mut leanh::LeanObject,
    mut v_a_1624_: *mut leanh::LeanObject,
    mut v_a_1625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1626_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___redArg(v___x_1621_, v_j_1623_, v_a_1625_);
    return v___x_1626_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___boxed(
    mut v___x_1627_: *mut leanh::LeanObject,
    mut v_n_1628_: *mut leanh::LeanObject,
    mut v_j_1629_: *mut leanh::LeanObject,
    mut v_a_1630_: *mut leanh::LeanObject,
    mut v_a_1631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1632_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4(v___x_1627_, v_n_1628_, v_j_1629_, v_a_1630_, v_a_1631_);
    leanh::lean_dec(v_n_1628_);
    leanh::lean_dec_ref(v___x_1627_);
    return v_res_1632_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_StructInstHint(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Hint(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed__const__1 =
        _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed__const__1();
    leanh::lean_mark_persistent(
        l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed__const__1,
    );
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_StructInstHint(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_StructInstHint(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Hint(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_OrderInstances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_StructInstHint(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_StructInstHint(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_StructInstHint(builtin);
}