// Lean compiler output
// Module: Lean.DocString.Formatter
// Imports: Lean.PrettyPrinter.Formatter Lean.DocString.Parser
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_array_size, lean_array_to_list,
    lean_array_uget_borrowed, lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_string_append, lean_string_memcmp, lean_string_push, lean_string_utf8_byte_size,
    lean_string_utf8_extract, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
    lean_uint32_dec_eq, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Format::Syntax::l_Lean_Syntax_formatStx;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_decodeStrLit, l_Lean_TSyntax_getNat, l_Lean_TSyntax_getString,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getKind, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull,
};
use crate::r#gen::Lean::DocString::Parser::{
    initialize_Lean_DocString_Parser, l_Lean_Doc_Parser_metadataContents_formatter,
    runtime_initialize_Lean_DocString_Parser,
};
use crate::r#gen::Lean::PrettyPrinter::Formatter::{
    initialize_Lean_PrettyPrinter_Formatter, l_Lean_PrettyPrinter_Formatter_concat,
    l_Lean_PrettyPrinter_Formatter_push___redArg, l_Lean_PrettyPrinter_Formatter_pushLine___redArg,
    l_Lean_PrettyPrinter_Formatter_visitArgs, l_Lean_PrettyPrinter_Formatter_visitAtom,
    runtime_initialize_Lean_PrettyPrinter_Formatter,
};
use crate::r#gen::Lean::Syntax::l_Lean_Syntax_Traverser_left;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString___closed__0_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [78, 79, 78, 45, 65, 84, 79, 77, 32, 0],
};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString___closed__0_value:
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
    m_data: [78, 79, 78, 45, 73, 68, 69, 78, 84, 32, 0],
};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [10, 10, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [97, 114, 103, 95, 115, 116, 114, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 121, 110, 116, 97, 120, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [68, 111, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3_value) as *mut crate::leanh::LeanObject,16350384043721911836 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [97, 114, 103, 95, 110, 117, 109, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5_value) as *mut crate::leanh::LeanObject,14487455678410716942 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 114, 103, 95, 105, 100, 101, 110, 116, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7_value) as *mut crate::leanh::LeanObject,2451685894574911817 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [110, 97, 109, 101, 100, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9_value) as *mut crate::leanh::LeanObject,7954595750846190064 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [110, 97, 109, 101, 100, 95, 110, 111, 95, 112, 97, 114, 101, 110, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11_value) as *mut crate::leanh::LeanObject,1862588536603037236 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [102, 108, 97, 103, 95, 111, 110, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13_value) as *mut crate::leanh::LeanObject,3891920175377473180 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__15_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [102, 108, 97, 103, 95, 111, 102, 102, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__15_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__15_value) as *mut crate::leanh::LeanObject,16434802777007652893 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__17_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [97, 110, 111, 110, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__17_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__17_value) as *mut crate::leanh::LeanObject,4061692882929131159 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__19_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 101, 120, 116, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__19_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__19_value) as *mut crate::leanh::LeanObject,7633771195065472508 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__21_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [101, 109, 112, 104, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__21_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__21_value) as *mut crate::leanh::LeanObject,17275792779021629260 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__23_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [98, 111, 108, 100, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__23_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__23_value) as *mut crate::leanh::LeanObject,826132507934060761 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__25_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 105, 110, 107, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__25_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__25_value) as *mut crate::leanh::LeanObject,5786183721214523521 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__27_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 109, 97, 103, 101, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__27_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__27_value) as *mut crate::leanh::LeanObject,4431944511769375132 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__29_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [114, 111, 108, 101, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__29_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__29_value) as *mut crate::leanh::LeanObject,8038157434449897304 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__31_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 100, 101, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__31_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__31_value) as *mut crate::leanh::LeanObject,9119460824152039283 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__33_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [102, 111, 111, 116, 110, 111, 116, 101, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__33_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__33_value) as *mut crate::leanh::LeanObject,8931910793042548687 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__35_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 105, 110, 101, 98, 114, 101, 97, 107, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__35: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__35_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__35_value) as *mut crate::leanh::LeanObject,14934976377275135948 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__37_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 110, 108, 105, 110, 101, 95, 109, 97, 116, 104, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__37: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__37_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__37_value) as *mut crate::leanh::LeanObject,13146676051664452135 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__39_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [100, 105, 115, 112, 108, 97, 121, 95, 109, 97, 116, 104, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__39: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__39_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__39_value) as *mut crate::leanh::LeanObject,17625330591492572857 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__41_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [114, 101, 102, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__41: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__41_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__41_value) as *mut crate::leanh::LeanObject,9592559646838605213 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__43_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [117, 114, 108, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__43: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__43_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__43_value) as *mut crate::leanh::LeanObject,14879212058519956833 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__45_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [104, 101, 97, 100, 101, 114, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__45: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__45_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__45_value) as *mut crate::leanh::LeanObject,12106318518385607562 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__47_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 97, 114, 97, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__47: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__47_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__47_value) as *mut crate::leanh::LeanObject,10424585805673941106 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__49_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [117, 108, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__49: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__49_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__49_value) as *mut crate::leanh::LeanObject,6453691647374023416 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__51_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [111, 108, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__51: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__51_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__51_value) as *mut crate::leanh::LeanObject,12480416442879068486 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__53_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [98, 108, 111, 99, 107, 113, 117, 111, 116, 101, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__53: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__53_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__53_value) as *mut crate::leanh::LeanObject,16099003537413514650 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__55_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [99, 111, 100, 101, 98, 108, 111, 99, 107, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__55: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__55_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__55_value) as *mut crate::leanh::LeanObject,12761800624135336676 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__57_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 105, 114, 101, 99, 116, 105, 118, 101, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__57: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__57_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__57_value) as *mut crate::leanh::LeanObject,13115808082649082939 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__59_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__59: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__59_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__59_value) as *mut crate::leanh::LeanObject,5109585754862282403 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__61_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [123, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__61: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__61_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__62_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [125, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__62: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__62_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__63_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__63: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__63_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__64_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [62, 32, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__64: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__64_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__3_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [108, 105, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__3_value) as *mut crate::leanh::LeanObject,7179854397063619926 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [46, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__5_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [42, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__65_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [35, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__65: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__65_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__66_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [125, 91, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__66: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__66_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__67_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [115, 116, 114, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__67: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__67_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__68_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__67_value) as *mut crate::leanh::LeanObject,9232979286016572671 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__68: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__68_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__69_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__69: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__69_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__69_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__71_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__71: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__71_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__72_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 58, 61, 32, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__72: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__72_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__73_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__73: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__73_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__74_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 117, 109, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__74: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__74_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__75_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__74_value) as *mut crate::leanh::LeanObject,6110315075117401315 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__75: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__75_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [109, 101, 116, 97, 100, 97, 116, 97, 95, 98, 108, 111, 99, 107, 0]};
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,8539228228387540046 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,18444330650968222853 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,15635760689405348171 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_Parser_document_formatter___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Doc_Parser_document_formatter___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Doc_Parser_document_formatter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Parser_document_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(
    mut v_x_1744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stx_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: u8 = 0;
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: u8 = 0;
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1744_) {
                1 => {
                    v_args_1755_ = crate::leanh::lean_ctor_get(v_x_1744_, 2);
                    v___x_1756_ = lean_array_get_size(v_args_1755_);
                    v___x_1757_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1758_ = lean_nat_dec_eq(v___x_1756_, v___x_1757_);
                    if v___x_1758_ == 0 {
                        v_stx_1746_ = v_x_1744_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc_ref(v_args_1755_);
                        crate::leanh::lean_dec_ref_known(v_x_1744_, 3);
                        v___x_1759_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1760_ = lean_array_fget(v_args_1755_, v___x_1759_);
                        crate::leanh::lean_dec_ref(v_args_1755_);
                        v_x_1744_ = v___x_1760_;
                        state = 0;
                        continue;
                    }
                }
                2 => {
                    v_val_1762_ = crate::leanh::lean_ctor_get(v_x_1744_, 1);
                    crate::leanh::lean_inc_ref(v_val_1762_);
                    crate::leanh::lean_dec_ref_known(v_x_1744_, 2);
                    return v_val_1762_;
                }
                _ => {
                    v_stx_1746_ = v_x_1744_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_1747_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString___closed__0;
                v___x_1748_ = crate::leanh::lean_box(0);
                v___x_1749_ = 0;
                v___x_1750_ = l_Lean_Syntax_formatStx(v_stx_1746_, v___x_1748_, v___x_1749_);
                v___x_1751_ = l_Std_Format_defWidth;
                v___x_1752_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1753_ =
                    l_Std_Format_pretty(v___x_1750_, v___x_1751_, v___x_1752_, v___x_1752_);
                v___x_1754_ = lean_string_append(v___x_1747_, v___x_1753_);
                crate::leanh::lean_dec_ref(v___x_1753_);
                return v___x_1754_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(
    mut v___y_1763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stxTrav_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cur_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1765_ = lean_st_ref_get(v___y_1763_);
    v_stxTrav_1766_ = crate::leanh::lean_ctor_get(v___x_1765_, 0);
    crate::leanh::lean_inc_ref(v_stxTrav_1766_);
    crate::leanh::lean_dec(v___x_1765_);
    v_cur_1767_ = crate::leanh::lean_ctor_get(v_stxTrav_1766_, 0);
    crate::leanh::lean_inc(v_cur_1767_);
    crate::leanh::lean_dec_ref(v_stxTrav_1766_);
    v___x_1768_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1768_, 0, v_cur_1767_);
    return v___x_1768_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg___boxed(
    mut v___y_1769_: *mut crate::leanh::LeanObject,
    mut v___y_1770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1771_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v___y_1769_);
    crate::leanh::lean_dec(v___y_1769_);
    return v_res_1771_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0(
    mut v___y_1772_: *mut crate::leanh::LeanObject,
    mut v___y_1773_: *mut crate::leanh::LeanObject,
    mut v___y_1774_: *mut crate::leanh::LeanObject,
    mut v___y_1775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1777_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v___y_1773_);
    return v___x_1777_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___boxed(
    mut v___y_1778_: *mut crate::leanh::LeanObject,
    mut v___y_1779_: *mut crate::leanh::LeanObject,
    mut v___y_1780_: *mut crate::leanh::LeanObject,
    mut v___y_1781_: *mut crate::leanh::LeanObject,
    mut v___y_1782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1783_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0(v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
    crate::leanh::lean_dec(v___y_1781_);
    crate::leanh::lean_dec_ref(v___y_1780_);
    crate::leanh::lean_dec(v___y_1779_);
    crate::leanh::lean_dec_ref(v___y_1778_);
    return v_res_1783_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(
    mut v___y_1784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stxTrav_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leadWord_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leadWordIdent_1789_: u8 = 0;
    let mut v_isUngrouped_1790_: u8 = 0;
    let mut v_mustBeGrouped_1791_: u8 = 0;
    let mut v_stack_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1795_: u8 = 0;
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1803_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1786_ = lean_st_ref_take(v___y_1784_);
                v_stxTrav_1787_ = crate::leanh::lean_ctor_get(v___x_1786_, 0);
                v_leadWord_1788_ = crate::leanh::lean_ctor_get(v___x_1786_, 1);
                v_leadWordIdent_1789_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_1786_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_isUngrouped_1790_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_1786_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_mustBeGrouped_1791_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_1786_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
                );
                v_stack_1792_ = crate::leanh::lean_ctor_get(v___x_1786_, 2);
                v_isSharedCheck_1803_ = (!crate::leanh::lean_is_exclusive(v___x_1786_)) as u8;
                if v_isSharedCheck_1803_ == 0 {
                    v___x_1794_ = v___x_1786_;
                    v_isShared_1795_ = v_isSharedCheck_1803_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stack_1792_);
                    crate::leanh::lean_inc(v_leadWord_1788_);
                    crate::leanh::lean_inc(v_stxTrav_1787_);
                    crate::leanh::lean_dec(v___x_1786_);
                    v___x_1794_ = crate::leanh::lean_box(0);
                    v_isShared_1795_ = v_isSharedCheck_1803_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1796_ = l_Lean_Syntax_Traverser_left(v_stxTrav_1787_);
                if v_isShared_1795_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1794_, 0, v___x_1796_);
                    v___x_1798_ = v___x_1794_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1802_ = crate::leanh::lean_alloc_ctor(0, 3, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1796_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_leadWord_1788_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1802_, 2, v_stack_1792_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1802_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_leadWordIdent_1789_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1802_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_isUngrouped_1790_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1802_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
                        v_mustBeGrouped_1791_,
                    );
                    v___x_1798_ = v_reuseFailAlloc_1802_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1799_ = lean_st_ref_set(v___y_1784_, v___x_1798_);
                v___x_1800_ = crate::leanh::lean_box(0);
                v___x_1801_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1801_, 0, v___x_1800_);
                return v___x_1801_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg___boxed(
    mut v___y_1804_: *mut crate::leanh::LeanObject,
    mut v___y_1805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1806_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(v___y_1804_);
    crate::leanh::lean_dec(v___y_1804_);
    return v_res_1806_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1(
    mut v___y_1807_: *mut crate::leanh::LeanObject,
    mut v___y_1808_: *mut crate::leanh::LeanObject,
    mut v___y_1809_: *mut crate::leanh::LeanObject,
    mut v___y_1810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1812_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(v___y_1808_);
    return v___x_1812_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___boxed(
    mut v___y_1813_: *mut crate::leanh::LeanObject,
    mut v___y_1814_: *mut crate::leanh::LeanObject,
    mut v___y_1815_: *mut crate::leanh::LeanObject,
    mut v___y_1816_: *mut crate::leanh::LeanObject,
    mut v___y_1817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1818_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1(v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
    crate::leanh::lean_dec(v___y_1816_);
    crate::leanh::lean_dec_ref(v___y_1815_);
    crate::leanh::lean_dec(v___y_1814_);
    crate::leanh::lean_dec_ref(v___y_1813_);
    return v_res_1818_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString(
    mut v_a_1819_: *mut crate::leanh::LeanObject,
    mut v_a_1820_: *mut crate::leanh::LeanObject,
    mut v_a_1821_: *mut crate::leanh::LeanObject,
    mut v_a_1822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1828_: u8 = 0;
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1835_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1824_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v_a_1820_);
                v_a_1825_ = crate::leanh::lean_ctor_get(v___x_1824_, 0);
                v_isSharedCheck_1835_ = (!crate::leanh::lean_is_exclusive(v___x_1824_)) as u8;
                if v_isSharedCheck_1835_ == 0 {
                    v___x_1827_ = v___x_1824_;
                    v_isShared_1828_ = v_isSharedCheck_1835_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1825_);
                    crate::leanh::lean_dec(v___x_1824_);
                    v___x_1827_ = crate::leanh::lean_box(0);
                    v_isShared_1828_ = v_isSharedCheck_1835_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1829_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_a_1825_);
                if v_isShared_1828_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1827_, 3);
                    crate::leanh::lean_ctor_set(v___x_1827_, 0, v___x_1829_);
                    v___x_1831_ = v___x_1827_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1834_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1829_);
                    v___x_1831_ = v_reuseFailAlloc_1834_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1832_ = l_Lean_PrettyPrinter_Formatter_push___redArg(v___x_1831_, v_a_1820_);
                if crate::leanh::lean_obj_tag(v___x_1832_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1832_, 1);
                    v___x_1833_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(v_a_1820_);
                    return v___x_1833_;
                } else {
                    return v___x_1832_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString___boxed(
    mut v_a_1836_: *mut crate::leanh::LeanObject,
    mut v_a_1837_: *mut crate::leanh::LeanObject,
    mut v_a_1838_: *mut crate::leanh::LeanObject,
    mut v_a_1839_: *mut crate::leanh::LeanObject,
    mut v_a_1840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1841_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString(
        v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_,
    );
    crate::leanh::lean_dec(v_a_1839_);
    crate::leanh::lean_dec_ref(v_a_1838_);
    crate::leanh::lean_dec(v_a_1837_);
    crate::leanh::lean_dec_ref(v_a_1836_);
    return v_res_1841_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg(
    mut v_a_1843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1849_: u8 = 0;
    let mut v___y_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1845_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v_a_1843_);
                v_a_1846_ = crate::leanh::lean_ctor_get(v___x_1845_, 0);
                v_isSharedCheck_1861_ = (!crate::leanh::lean_is_exclusive(v___x_1845_)) as u8;
                if v_isSharedCheck_1861_ == 0 {
                    v___x_1848_ = v___x_1845_;
                    v_isShared_1849_ = v_isSharedCheck_1861_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1846_);
                    crate::leanh::lean_dec(v___x_1845_);
                    v___x_1848_ = crate::leanh::lean_box(0);
                    v_isShared_1849_ = v_isSharedCheck_1861_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1857_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_a_1846_);
                v___x_1858_ = l_Lean_Syntax_decodeStrLit(v___x_1857_);
                if crate::leanh::lean_obj_tag(v___x_1858_) == 0 {
                    v___x_1859_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
                    v___y_1851_ = v___x_1859_;
                    state = 2;
                    continue;
                } else {
                    v_val_1860_ = crate::leanh::lean_ctor_get(v___x_1858_, 0);
                    crate::leanh::lean_inc(v_val_1860_);
                    crate::leanh::lean_dec_ref_known(v___x_1858_, 1);
                    v___y_1851_ = v_val_1860_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1849_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1848_, 3);
                    crate::leanh::lean_ctor_set(v___x_1848_, 0, v___y_1851_);
                    v___x_1853_ = v___x_1848_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1856_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___y_1851_);
                    v___x_1853_ = v_reuseFailAlloc_1856_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1854_ = l_Lean_PrettyPrinter_Formatter_push___redArg(v___x_1853_, v_a_1843_);
                if crate::leanh::lean_obj_tag(v___x_1854_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1854_, 1);
                    v___x_1855_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(v_a_1843_);
                    return v___x_1855_;
                } else {
                    return v___x_1854_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___boxed(
    mut v_a_1862_: *mut crate::leanh::LeanObject,
    mut v_a_1863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1864_ =
        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg(v_a_1862_);
    crate::leanh::lean_dec(v_a_1862_);
    return v_res_1864_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit(
    mut v_a_1865_: *mut crate::leanh::LeanObject,
    mut v_a_1866_: *mut crate::leanh::LeanObject,
    mut v_a_1867_: *mut crate::leanh::LeanObject,
    mut v_a_1868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1870_ =
        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg(v_a_1866_);
    return v___x_1870_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___boxed(
    mut v_a_1871_: *mut crate::leanh::LeanObject,
    mut v_a_1872_: *mut crate::leanh::LeanObject,
    mut v_a_1873_: *mut crate::leanh::LeanObject,
    mut v_a_1874_: *mut crate::leanh::LeanObject,
    mut v_a_1875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1876_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit(
        v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_,
    );
    crate::leanh::lean_dec(v_a_1874_);
    crate::leanh::lean_dec_ref(v_a_1873_);
    crate::leanh::lean_dec(v_a_1872_);
    crate::leanh::lean_dec_ref(v_a_1871_);
    return v_res_1876_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(
    mut v_x_1878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stx_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: u8 = 0;
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: u8 = 0;
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: u8 = 0;
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1878_) {
                1 => {
                    v_args_1889_ = crate::leanh::lean_ctor_get(v_x_1878_, 2);
                    v___x_1890_ = lean_array_get_size(v_args_1889_);
                    v___x_1891_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1892_ = lean_nat_dec_eq(v___x_1890_, v___x_1891_);
                    if v___x_1892_ == 0 {
                        v_stx_1880_ = v_x_1878_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc_ref(v_args_1889_);
                        crate::leanh::lean_dec_ref_known(v_x_1878_, 3);
                        v___x_1893_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1894_ = lean_array_fget(v_args_1889_, v___x_1893_);
                        crate::leanh::lean_dec_ref(v_args_1889_);
                        v_x_1878_ = v___x_1894_;
                        state = 0;
                        continue;
                    }
                }
                3 => {
                    v_val_1896_ = crate::leanh::lean_ctor_get(v_x_1878_, 2);
                    crate::leanh::lean_inc(v_val_1896_);
                    crate::leanh::lean_dec_ref_known(v_x_1878_, 4);
                    v___x_1897_ = 1;
                    v___x_1898_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_val_1896_,
                        v___x_1897_,
                    );
                    return v___x_1898_;
                }
                _ => {
                    v_stx_1880_ = v_x_1878_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_1881_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString___closed__0;
                v___x_1882_ = crate::leanh::lean_box(0);
                v___x_1883_ = 0;
                v___x_1884_ = l_Lean_Syntax_formatStx(v_stx_1880_, v___x_1882_, v___x_1883_);
                v___x_1885_ = l_Std_Format_defWidth;
                v___x_1886_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1887_ =
                    l_Std_Format_pretty(v___x_1884_, v___x_1885_, v___x_1886_, v___x_1886_);
                v___x_1888_ = lean_string_append(v___x_1881_, v___x_1887_);
                crate::leanh::lean_dec_ref(v___x_1887_);
                return v___x_1888_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___redArg(
    mut v_a_1899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1905_: u8 = 0;
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1912_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1901_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v_a_1899_);
                v_a_1902_ = crate::leanh::lean_ctor_get(v___x_1901_, 0);
                v_isSharedCheck_1912_ = (!crate::leanh::lean_is_exclusive(v___x_1901_)) as u8;
                if v_isSharedCheck_1912_ == 0 {
                    v___x_1904_ = v___x_1901_;
                    v_isShared_1905_ = v_isSharedCheck_1912_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1902_);
                    crate::leanh::lean_dec(v___x_1901_);
                    v___x_1904_ = crate::leanh::lean_box(0);
                    v_isShared_1905_ = v_isSharedCheck_1912_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1906_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_a_1902_);
                if v_isShared_1905_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1904_, 3);
                    crate::leanh::lean_ctor_set(v___x_1904_, 0, v___x_1906_);
                    v___x_1908_ = v___x_1904_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1911_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1906_);
                    v___x_1908_ = v_reuseFailAlloc_1911_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1909_ = l_Lean_PrettyPrinter_Formatter_push___redArg(v___x_1908_, v_a_1899_);
                if crate::leanh::lean_obj_tag(v___x_1909_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1909_, 1);
                    v___x_1910_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(v_a_1899_);
                    return v___x_1910_;
                } else {
                    return v___x_1909_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___redArg___boxed(
    mut v_a_1913_: *mut crate::leanh::LeanObject,
    mut v_a_1914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1915_ =
        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___redArg(v_a_1913_);
    crate::leanh::lean_dec(v_a_1913_);
    return v_res_1915_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent(
    mut v_a_1916_: *mut crate::leanh::LeanObject,
    mut v_a_1917_: *mut crate::leanh::LeanObject,
    mut v_a_1918_: *mut crate::leanh::LeanObject,
    mut v_a_1919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1921_ =
        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___redArg(v_a_1917_);
    return v___x_1921_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___boxed(
    mut v_a_1922_: *mut crate::leanh::LeanObject,
    mut v_a_1923_: *mut crate::leanh::LeanObject,
    mut v_a_1924_: *mut crate::leanh::LeanObject,
    mut v_a_1925_: *mut crate::leanh::LeanObject,
    mut v_a_1926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1927_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent(
        v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_,
    );
    crate::leanh::lean_dec(v_a_1925_);
    crate::leanh::lean_dec_ref(v_a_1924_);
    crate::leanh::lean_dec(v_a_1923_);
    crate::leanh::lean_dec_ref(v_a_1922_);
    return v_res_1927_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___redArg(
    mut v_f_1928_: *mut crate::leanh::LeanObject,
    mut v_i_1929_: *mut crate::leanh::LeanObject,
    mut v___y_1930_: *mut crate::leanh::LeanObject,
    mut v___y_1931_: *mut crate::leanh::LeanObject,
    mut v___y_1932_: *mut crate::leanh::LeanObject,
    mut v___y_1933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1936_: u8 = 0;
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1935_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1936_ = lean_nat_dec_eq(v_i_1929_, v_zero_1935_);
                if v_isZero_1936_ == 1 {
                    crate::leanh::lean_dec(v_i_1929_);
                    crate::leanh::lean_dec_ref(v_f_1928_);
                    v___x_1937_ = crate::leanh::lean_box(0);
                    v___x_1938_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1938_, 0, v___x_1937_);
                    return v___x_1938_;
                } else {
                    crate::leanh::lean_inc_ref(v_f_1928_);
                    crate::leanh::lean_inc(v___y_1933_);
                    crate::leanh::lean_inc_ref(v___y_1932_);
                    crate::leanh::lean_inc(v___y_1931_);
                    crate::leanh::lean_inc_ref(v___y_1930_);
                    v___x_1939_ = crate::leanh::lean_apply_5(
                        v_f_1928_,
                        v___y_1930_,
                        v___y_1931_,
                        v___y_1932_,
                        v___y_1933_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_1939_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1939_, 1);
                        v_one_1940_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_n_1941_ = lean_nat_sub(v_i_1929_, v_one_1940_);
                        crate::leanh::lean_dec(v_i_1929_);
                        v_i_1929_ = v_n_1941_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_1929_);
                        crate::leanh::lean_dec_ref(v_f_1928_);
                        return v___x_1939_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___redArg___boxed(
    mut v_f_1943_: *mut crate::leanh::LeanObject,
    mut v_i_1944_: *mut crate::leanh::LeanObject,
    mut v___y_1945_: *mut crate::leanh::LeanObject,
    mut v___y_1946_: *mut crate::leanh::LeanObject,
    mut v___y_1947_: *mut crate::leanh::LeanObject,
    mut v___y_1948_: *mut crate::leanh::LeanObject,
    mut v___y_1949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1950_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___redArg(v_f_1943_, v_i_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
    crate::leanh::lean_dec(v___y_1948_);
    crate::leanh::lean_dec_ref(v___y_1947_);
    crate::leanh::lean_dec(v___y_1946_);
    crate::leanh::lean_dec_ref(v___y_1945_);
    return v_res_1950_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0(
    mut v_f_1951_: *mut crate::leanh::LeanObject,
    mut v_n_1952_: *mut crate::leanh::LeanObject,
    mut v_i_1953_: *mut crate::leanh::LeanObject,
    mut v_a_1954_: *mut crate::leanh::LeanObject,
    mut v___y_1955_: *mut crate::leanh::LeanObject,
    mut v___y_1956_: *mut crate::leanh::LeanObject,
    mut v___y_1957_: *mut crate::leanh::LeanObject,
    mut v___y_1958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1960_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___redArg(v_f_1951_, v_i_1953_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
    return v___x_1960_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___boxed(
    mut v_f_1961_: *mut crate::leanh::LeanObject,
    mut v_n_1962_: *mut crate::leanh::LeanObject,
    mut v_i_1963_: *mut crate::leanh::LeanObject,
    mut v_a_1964_: *mut crate::leanh::LeanObject,
    mut v___y_1965_: *mut crate::leanh::LeanObject,
    mut v___y_1966_: *mut crate::leanh::LeanObject,
    mut v___y_1967_: *mut crate::leanh::LeanObject,
    mut v___y_1968_: *mut crate::leanh::LeanObject,
    mut v___y_1969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1970_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0(v_f_1961_, v_n_1962_, v_i_1963_, v_a_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
    crate::leanh::lean_dec(v___y_1968_);
    crate::leanh::lean_dec_ref(v___y_1967_);
    crate::leanh::lean_dec(v___y_1966_);
    crate::leanh::lean_dec_ref(v___y_1965_);
    crate::leanh::lean_dec(v_n_1962_);
    return v_res_1970_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___lam__0(
    mut v_f_1971_: *mut crate::leanh::LeanObject,
    mut v___y_1972_: *mut crate::leanh::LeanObject,
    mut v___y_1973_: *mut crate::leanh::LeanObject,
    mut v___y_1974_: *mut crate::leanh::LeanObject,
    mut v___y_1975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_count_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1977_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v___y_1973_);
    v_a_1978_ = crate::leanh::lean_ctor_get(v___x_1977_, 0);
    crate::leanh::lean_inc(v_a_1978_);
    crate::leanh::lean_dec_ref(v___x_1977_);
    v___x_1979_ = l_Lean_Syntax_getArgs(v_a_1978_);
    crate::leanh::lean_dec(v_a_1978_);
    v_count_1980_ = lean_array_get_size(v___x_1979_);
    crate::leanh::lean_dec_ref(v___x_1979_);
    v___x_1981_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___boxed as *mut core::ffi::c_void, 9, 4);
    crate::leanh::lean_closure_set(v___x_1981_, 0, v_f_1971_);
    crate::leanh::lean_closure_set(v___x_1981_, 1, v_count_1980_);
    crate::leanh::lean_closure_set(v___x_1981_, 2, v_count_1980_);
    crate::leanh::lean_closure_set(v___x_1981_, 3, crate::leanh::lean_box(0));
    v___x_1982_ = l_Lean_PrettyPrinter_Formatter_visitArgs(
        v___x_1981_,
        v___y_1972_,
        v___y_1973_,
        v___y_1974_,
        v___y_1975_,
    );
    return v___x_1982_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___lam__0___boxed(
    mut v_f_1983_: *mut crate::leanh::LeanObject,
    mut v___y_1984_: *mut crate::leanh::LeanObject,
    mut v___y_1985_: *mut crate::leanh::LeanObject,
    mut v___y_1986_: *mut crate::leanh::LeanObject,
    mut v___y_1987_: *mut crate::leanh::LeanObject,
    mut v___y_1988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1989_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___lam__0(
        v_f_1983_,
        v___y_1984_,
        v___y_1985_,
        v___y_1986_,
        v___y_1987_,
    );
    crate::leanh::lean_dec(v___y_1987_);
    crate::leanh::lean_dec_ref(v___y_1986_);
    crate::leanh::lean_dec(v___y_1985_);
    crate::leanh::lean_dec_ref(v___y_1984_);
    return v_res_1989_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep(
    mut v_f_1990_: *mut crate::leanh::LeanObject,
    mut v_a_1991_: *mut crate::leanh::LeanObject,
    mut v_a_1992_: *mut crate::leanh::LeanObject,
    mut v_a_1993_: *mut crate::leanh::LeanObject,
    mut v_a_1994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1996_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___lam__0___boxed
            as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1996_, 0, v_f_1990_);
    v___x_1997_ = l_Lean_PrettyPrinter_Formatter_concat(
        v___f_1996_,
        v_a_1991_,
        v_a_1992_,
        v_a_1993_,
        v_a_1994_,
    );
    return v___x_1997_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___boxed(
    mut v_f_1998_: *mut crate::leanh::LeanObject,
    mut v_a_1999_: *mut crate::leanh::LeanObject,
    mut v_a_2000_: *mut crate::leanh::LeanObject,
    mut v_a_2001_: *mut crate::leanh::LeanObject,
    mut v_a_2002_: *mut crate::leanh::LeanObject,
    mut v_a_2003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2004_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep(
        v_f_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_,
    );
    crate::leanh::lean_dec(v_a_2002_);
    crate::leanh::lean_dec_ref(v_a_2001_);
    crate::leanh::lean_dec(v_a_2000_);
    crate::leanh::lean_dec_ref(v_a_1999_);
    return v_res_2004_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(
    mut v_s_2005_: *mut crate::leanh::LeanObject,
    mut v_a_2006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2007_ = crate::leanh::lean_box(0);
    v___x_2008_ = lean_string_append(v_a_2006_, v_s_2005_);
    v___x_2009_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2009_, 0, v___x_2007_);
    crate::leanh::lean_ctor_set(v___x_2009_, 1, v___x_2008_);
    return v___x_2009_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg___boxed(
    mut v_s_2010_: *mut crate::leanh::LeanObject,
    mut v_a_2011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2012_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v_s_2010_, v_a_2011_);
    crate::leanh::lean_dec_ref(v_s_2010_);
    return v_res_2012_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out(
    mut v_s_2013_: *mut crate::leanh::LeanObject,
    mut v_a_2014_: *mut crate::leanh::LeanObject,
    mut v_a_2015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2016_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v_s_2013_, v_a_2015_);
    return v___x_2016_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___boxed(
    mut v_s_2017_: *mut crate::leanh::LeanObject,
    mut v_a_2018_: *mut crate::leanh::LeanObject,
    mut v_a_2019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2020_ =
        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out(
            v_s_2017_, v_a_2018_, v_a_2019_,
        );
    crate::leanh::lean_dec(v_a_2018_);
    crate::leanh::lean_dec_ref(v_s_2017_);
    return v_res_2020_;
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(
    mut v_x_2021_: *mut crate::leanh::LeanObject,
    mut v_x_2022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2024_: u8 = 0;
    let mut v___x_2025_: u32 = 0;
    let mut v_one_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2023_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_2024_ = lean_nat_dec_eq(v_x_2021_, v_zero_2023_);
                if v_isZero_2024_ == 1 {
                    crate::leanh::lean_dec(v_x_2021_);
                    return v_x_2022_;
                } else {
                    v___x_2025_ = 32;
                    v_one_2026_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_2027_ = lean_nat_sub(v_x_2021_, v_one_2026_);
                    crate::leanh::lean_dec(v_x_2021_);
                    v___x_2028_ = lean_string_push(v_x_2022_, v___x_2025_);
                    v_x_2021_ = v_n_2027_;
                    v_x_2022_ = v___x_2028_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl(
    mut v_a_2031_: *mut crate::leanh::LeanObject,
    mut v_a_2032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2033_ = crate::leanh::lean_box(0);
    v___x_2034_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0;
    crate::leanh::lean_inc(v_a_2031_);
    v___x_2035_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(v_a_2031_, v___x_2034_);
    v___x_2036_ = lean_string_append(v_a_2032_, v___x_2035_);
    crate::leanh::lean_dec_ref(v___x_2035_);
    v___x_2037_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2037_, 0, v___x_2033_);
    crate::leanh::lean_ctor_set(v___x_2037_, 1, v___x_2036_);
    return v___x_2037_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___boxed(
    mut v_a_2038_: *mut crate::leanh::LeanObject,
    mut v_a_2039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2040_ =
        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl(
            v_a_2038_, v_a_2039_,
        );
    crate::leanh::lean_dec(v_a_2038_);
    return v_res_2040_;
}
pub unsafe fn _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2041_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0;
    v___x_2042_ = lean_string_utf8_byte_size(v___x_2041_);
    return v___x_2042_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(
    mut v_a_2043_: *mut crate::leanh::LeanObject,
    mut v_a_2044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: u8 = 0;
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: u8 = 0;
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2048_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0;
                v___x_2049_ = lean_string_utf8_byte_size(v_a_2044_);
                v___x_2050_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0), core::ptr::addr_of_mut!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0_once), _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0);
                v___x_2051_ = lean_nat_dec_le(v___x_2050_, v___x_2049_);
                if v___x_2051_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_2052_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2053_ = lean_nat_sub(v___x_2049_, v___x_2050_);
                    v___x_2054_ = lean_string_memcmp(
                        v_a_2044_,
                        v___x_2048_,
                        v___x_2053_,
                        v___x_2052_,
                        v___x_2050_,
                    );
                    crate::leanh::lean_dec(v___x_2053_);
                    if v___x_2054_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_2055_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
                        crate::leanh::lean_inc(v_a_2043_);
                        v___x_2056_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(v_a_2043_, v___x_2055_);
                        v___x_2057_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2056_, v_a_2044_);
                        crate::leanh::lean_dec_ref(v___x_2056_);
                        return v___x_2057_;
                    }
                }
            }
            1 => {
                v___x_2046_ = crate::leanh::lean_box(0);
                v___x_2047_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2047_, 0, v___x_2046_);
                crate::leanh::lean_ctor_set(v___x_2047_, 1, v_a_2044_);
                return v___x_2047_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___boxed(
    mut v_a_2058_: *mut crate::leanh::LeanObject,
    mut v_a_2059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2060_ =
        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(
            v_a_2058_, v_a_2059_,
        );
    crate::leanh::lean_dec(v_a_2058_);
    return v_res_2060_;
}
pub unsafe fn _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2062_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__0;
    v___x_2063_ = lean_string_utf8_byte_size(v___x_2062_);
    return v___x_2063_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(
    mut v_a_2064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: u8 = 0;
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: u8 = 0;
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: u8 = 0;
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: u8 = 0;
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2065_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__0;
                v___x_2077_ = lean_string_utf8_byte_size(v_a_2064_);
                v___x_2078_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1_once), _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1);
                v___x_2079_ = lean_nat_dec_le(v___x_2078_, v___x_2077_);
                if v___x_2079_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_2080_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2081_ = lean_nat_sub(v___x_2077_, v___x_2078_);
                    v___x_2082_ = lean_string_memcmp(
                        v_a_2064_,
                        v___x_2065_,
                        v___x_2081_,
                        v___x_2080_,
                        v___x_2078_,
                    );
                    crate::leanh::lean_dec(v___x_2081_);
                    if v___x_2082_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_2083_ = crate::leanh::lean_box(0);
                        v___x_2084_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2084_, 0, v___x_2083_);
                        crate::leanh::lean_ctor_set(v___x_2084_, 1, v_a_2064_);
                        return v___x_2084_;
                    }
                }
            }
            1 => {
                v___x_2067_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0;
                v___x_2068_ = lean_string_utf8_byte_size(v_a_2064_);
                v___x_2069_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0), core::ptr::addr_of_mut!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0_once), _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0);
                v___x_2070_ = lean_nat_dec_le(v___x_2069_, v___x_2068_);
                if v___x_2070_ == 0 {
                    v___x_2071_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2065_, v_a_2064_);
                    return v___x_2071_;
                } else {
                    v___x_2072_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2073_ = lean_nat_sub(v___x_2068_, v___x_2069_);
                    v___x_2074_ = lean_string_memcmp(
                        v_a_2064_,
                        v___x_2067_,
                        v___x_2073_,
                        v___x_2072_,
                        v___x_2069_,
                    );
                    crate::leanh::lean_dec(v___x_2073_);
                    if v___x_2074_ == 0 {
                        v___x_2075_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2065_, v_a_2064_);
                        return v___x_2075_;
                    } else {
                        v___x_2076_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2067_, v_a_2064_);
                        return v___x_2076_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock(
    mut v_a_2085_: *mut crate::leanh::LeanObject,
    mut v_a_2086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2087_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_a_2086_);
    return v___x_2087_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___boxed(
    mut v_a_2088_: *mut crate::leanh::LeanObject,
    mut v_a_2089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2090_ =
        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock(
            v_a_2088_, v_a_2089_,
        );
    crate::leanh::lean_dec(v_a_2088_);
    return v_res_2090_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(
    mut v_s_2093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2094_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___closed__0;
    return v___x_2094_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___boxed(
    mut v_s_2095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2096_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_s_2095_);
    crate::leanh::lean_dec_ref(v_s_2095_);
    return v_res_2096_;
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(
    mut v_x_2097_: *mut crate::leanh::LeanObject,
    mut v_x_2098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2100_: u8 = 0;
    let mut v___x_2101_: u32 = 0;
    let mut v_one_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2099_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_2100_ = lean_nat_dec_eq(v_x_2097_, v_zero_2099_);
                if v_isZero_2100_ == 1 {
                    crate::leanh::lean_dec(v_x_2097_);
                    return v_x_2098_;
                } else {
                    v___x_2101_ = 35;
                    v_one_2102_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_2103_ = lean_nat_sub(v_x_2097_, v_one_2102_);
                    crate::leanh::lean_dec(v_x_2097_);
                    v___x_2104_ = lean_string_push(v_x_2098_, v___x_2101_);
                    v_x_2097_ = v_n_2103_;
                    v_x_2098_ = v___x_2104_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg(
    mut v_a_2106_: *mut crate::leanh::LeanObject,
    mut v___y_2107_: *mut crate::leanh::LeanObject,
    mut v___x_2108_: *mut crate::leanh::LeanObject,
    mut v___x_2109_: *mut crate::leanh::LeanObject,
    mut v_a_2110_: *mut crate::leanh::LeanObject,
    mut v_b_2111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2126_: u8 = 0;
    let mut v_startInclusive_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: u8 = 0;
    let mut v___x_2131_: u32 = 0;
    let mut v___x_2132_: u32 = 0;
    let mut v___x_2133_: u8 = 0;
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2149_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2110_) == 0 {
                    v_currPos_2122_ = crate::leanh::lean_ctor_get(v_a_2110_, 0);
                    v_searcher_2123_ = crate::leanh::lean_ctor_get(v_a_2110_, 1);
                    v_isSharedCheck_2149_ = (!crate::leanh::lean_is_exclusive(v_a_2110_)) as u8;
                    if v_isSharedCheck_2149_ == 0 {
                        v___x_2125_ = v_a_2110_;
                        v_isShared_2126_ = v_isSharedCheck_2149_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_2123_);
                        crate::leanh::lean_inc(v_currPos_2122_);
                        crate::leanh::lean_dec(v_a_2110_);
                        v___x_2125_ = crate::leanh::lean_box(0);
                        v_isShared_2126_ = v_isSharedCheck_2149_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2109_);
                    return v_b_2111_;
                }
            }
            1 => {
                v___x_2116_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
                crate::leanh::lean_inc(v_a_2106_);
                v___x_2117_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(v_a_2106_, v___x_2116_);
                v___x_2118_ = lean_string_utf8_extract(
                    v___y_2107_,
                    v_startInclusive_2114_,
                    v_endExclusive_2115_,
                );
                crate::leanh::lean_dec(v_endExclusive_2115_);
                crate::leanh::lean_dec(v_startInclusive_2114_);
                v___x_2119_ = lean_string_append(v___x_2117_, v___x_2118_);
                crate::leanh::lean_dec_ref(v___x_2118_);
                v___x_2120_ = lean_array_push(v_b_2111_, v___x_2119_);
                v_a_2110_ = v_it_2113_;
                v_b_2111_ = v___x_2120_;
                state = 0;
                continue;
            }
            2 => {
                v_startInclusive_2127_ = crate::leanh::lean_ctor_get(v___x_2108_, 1);
                v_endExclusive_2128_ = crate::leanh::lean_ctor_get(v___x_2108_, 2);
                v___x_2129_ = lean_nat_sub(v_endExclusive_2128_, v_startInclusive_2127_);
                v___x_2130_ = lean_nat_dec_eq(v_searcher_2123_, v___x_2129_);
                crate::leanh::lean_dec(v___x_2129_);
                if v___x_2130_ == 0 {
                    v___x_2131_ = 10;
                    v___x_2132_ = lean_string_utf8_get_fast(v___y_2107_, v_searcher_2123_);
                    v___x_2133_ = lean_uint32_dec_eq(v___x_2132_, v___x_2131_);
                    if v___x_2133_ == 0 {
                        v___x_2134_ = lean_string_utf8_next_fast(v___y_2107_, v_searcher_2123_);
                        crate::leanh::lean_dec(v_searcher_2123_);
                        if v_isShared_2126_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2125_, 1, v___x_2134_);
                            v___x_2136_ = v___x_2125_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2138_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_currPos_2122_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2138_, 1, v___x_2134_);
                            v___x_2136_ = v_reuseFailAlloc_2138_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2139_ = lean_string_utf8_next_fast(v___y_2107_, v_searcher_2123_);
                        v___x_2140_ = lean_nat_sub(v___x_2139_, v_searcher_2123_);
                        v___x_2141_ = lean_nat_add(v_searcher_2123_, v___x_2140_);
                        crate::leanh::lean_dec(v___x_2140_);
                        v_slice_2142_ = l_String_Slice_subslice_x21(
                            v___x_2108_,
                            v_currPos_2122_,
                            v_searcher_2123_,
                        );
                        crate::leanh::lean_inc(v___x_2141_);
                        if v_isShared_2126_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2125_, 1, v___x_2141_);
                            crate::leanh::lean_ctor_set(v___x_2125_, 0, v___x_2141_);
                            v_nextIt_2144_ = v___x_2125_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2147_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2141_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2147_, 1, v___x_2141_);
                            v_nextIt_2144_ = v_reuseFailAlloc_2147_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2125_);
                    crate::leanh::lean_dec(v_searcher_2123_);
                    v___x_2148_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc(v___x_2109_);
                    v_it_2113_ = v___x_2148_;
                    v_startInclusive_2114_ = v_currPos_2122_;
                    v_endExclusive_2115_ = v___x_2109_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_2110_ = v___x_2136_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_2145_ = crate::leanh::lean_ctor_get(v_slice_2142_, 0);
                crate::leanh::lean_inc(v_startInclusive_2145_);
                v_endExclusive_2146_ = crate::leanh::lean_ctor_get(v_slice_2142_, 1);
                crate::leanh::lean_inc(v_endExclusive_2146_);
                crate::leanh::lean_dec_ref(v_slice_2142_);
                v_it_2113_ = v_nextIt_2144_;
                v_startInclusive_2114_ = v_startInclusive_2145_;
                v_endExclusive_2115_ = v_endExclusive_2146_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg___boxed(
    mut v_a_2150_: *mut crate::leanh::LeanObject,
    mut v___y_2151_: *mut crate::leanh::LeanObject,
    mut v___x_2152_: *mut crate::leanh::LeanObject,
    mut v___x_2153_: *mut crate::leanh::LeanObject,
    mut v_a_2154_: *mut crate::leanh::LeanObject,
    mut v_b_2155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2156_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg(v_a_2150_, v___y_2151_, v___x_2152_, v___x_2153_, v_a_2154_, v_b_2155_);
    crate::leanh::lean_dec_ref(v___x_2152_);
    crate::leanh::lean_dec_ref(v___y_2151_);
    crate::leanh::lean_dec(v_a_2150_);
    return v_res_2156_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(
    mut v_as_2340_: *mut crate::leanh::LeanObject,
    mut v_sz_2341_: usize,
    mut v_i_2342_: usize,
    mut v_b_2343_: *mut crate::leanh::LeanObject,
    mut v___y_2344_: *mut crate::leanh::LeanObject,
    mut v___y_2345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2346_: u8 = 0;
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: usize = 0;
    let mut v___x_2356_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2346_ = lean_usize_dec_lt(v_i_2342_, v_sz_2341_);
                if v___x_2346_ == 0 {
                    v___x_2347_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2347_, 0, v_b_2343_);
                    crate::leanh::lean_ctor_set(v___x_2347_, 1, v___y_2345_);
                    return v___x_2347_;
                } else {
                    v___x_2348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0;
                    v___x_2349_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2348_, v___y_2345_);
                    v_snd_2350_ = crate::leanh::lean_ctor_get(v___x_2349_, 1);
                    crate::leanh::lean_inc(v_snd_2350_);
                    crate::leanh::lean_dec_ref(v___x_2349_);
                    v_a_2351_ = lean_array_uget_borrowed(v_as_2340_, v_i_2342_);
                    crate::leanh::lean_inc(v_a_2351_);
                    v___x_2352_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_a_2351_, v___y_2344_, v_snd_2350_);
                    v_snd_2353_ = crate::leanh::lean_ctor_get(v___x_2352_, 1);
                    crate::leanh::lean_inc(v_snd_2353_);
                    crate::leanh::lean_dec_ref(v___x_2352_);
                    v___x_2354_ = crate::leanh::lean_box(0);
                    v___x_2355_ = 1usize;
                    v___x_2356_ = lean_usize_add(v_i_2342_, v___x_2355_);
                    v_i_2342_ = v___x_2356_;
                    v_b_2343_ = v___x_2354_;
                    v___y_2345_ = v_snd_2353_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__1(
    mut v_as_2359_: *mut crate::leanh::LeanObject,
    mut v_sz_2360_: usize,
    mut v_i_2361_: usize,
    mut v_b_2362_: *mut crate::leanh::LeanObject,
    mut v___y_2363_: *mut crate::leanh::LeanObject,
    mut v___y_2364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2365_: u8 = 0;
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: usize = 0;
    let mut v___x_2375_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2365_ = lean_usize_dec_lt(v_i_2361_, v_sz_2360_);
                if v___x_2365_ == 0 {
                    v___x_2366_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2366_, 0, v_b_2362_);
                    crate::leanh::lean_ctor_set(v___x_2366_, 1, v___y_2364_);
                    return v___x_2366_;
                } else {
                    v___x_2367_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0;
                    v___x_2368_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2367_, v___y_2364_);
                    v_snd_2369_ = crate::leanh::lean_ctor_get(v___x_2368_, 1);
                    crate::leanh::lean_inc(v_snd_2369_);
                    crate::leanh::lean_dec_ref(v___x_2368_);
                    v_a_2370_ = lean_array_uget_borrowed(v_as_2359_, v_i_2361_);
                    crate::leanh::lean_inc(v_a_2370_);
                    v___x_2371_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_a_2370_, v___y_2363_, v_snd_2369_);
                    v_snd_2372_ = crate::leanh::lean_ctor_get(v___x_2371_, 1);
                    crate::leanh::lean_inc(v_snd_2372_);
                    crate::leanh::lean_dec_ref(v___x_2371_);
                    v___x_2373_ = crate::leanh::lean_box(0);
                    v___x_2374_ = 1usize;
                    v___x_2375_ = lean_usize_add(v_i_2361_, v___x_2374_);
                    v_i_2361_ = v___x_2375_;
                    v_b_2362_ = v___x_2373_;
                    v___y_2364_ = v_snd_2372_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(
    mut v_as_2387_: *mut crate::leanh::LeanObject,
    mut v_sz_2388_: usize,
    mut v_i_2389_: usize,
    mut v_b_2390_: *mut crate::leanh::LeanObject,
    mut v___y_2391_: *mut crate::leanh::LeanObject,
    mut v___y_2392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: usize = 0;
    let mut v___x_2397_: usize = 0;
    let mut v___x_2399_: u8 = 0;
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: u8 = 0;
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: u8 = 0;
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: u8 = 0;
    let mut v___x_2427_: usize = 0;
    let mut v___x_2428_: usize = 0;
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: usize = 0;
    let mut v___x_2431_: usize = 0;
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2399_ = lean_usize_dec_lt(v_i_2389_, v_sz_2388_);
                if v___x_2399_ == 0 {
                    v___x_2400_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2400_, 0, v_b_2390_);
                    crate::leanh::lean_ctor_set(v___x_2400_, 1, v___y_2392_);
                    return v___x_2400_;
                } else {
                    v_a_2401_ = lean_array_uget_borrowed(v_as_2387_, v_i_2389_);
                    v___x_2402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4;
                    crate::leanh::lean_inc(v_a_2401_);
                    v___x_2403_ = l_Lean_Syntax_isOfKind(v_a_2401_, v___x_2402_);
                    if v___x_2403_ == 0 {
                        v_a_2394_ = v_b_2390_;
                        v_snd_2395_ = v___y_2392_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_b_2390_);
                        v___x_2404_ = l_Nat_reprFast(v_b_2390_);
                        v___x_2405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___closed__0;
                        v___x_2406_ = lean_string_append(v___x_2404_, v___x_2405_);
                        v___x_2407_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2406_, v___y_2392_);
                        crate::leanh::lean_dec_ref(v___x_2406_);
                        v_snd_2408_ = crate::leanh::lean_ctor_get(v___x_2407_, 1);
                        crate::leanh::lean_inc(v_snd_2408_);
                        crate::leanh::lean_dec_ref(v___x_2407_);
                        v___x_2409_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2418_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2419_ = l_Lean_Syntax_getArg(v_a_2401_, v___x_2409_);
                        v___x_2420_ = l_Lean_Syntax_getArgs(v___x_2419_);
                        crate::leanh::lean_dec(v___x_2419_);
                        v___x_2421_ = lean_array_get_size(v___x_2420_);
                        v___x_2422_ = lean_nat_dec_lt(v___x_2418_, v___x_2421_);
                        if v___x_2422_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2420_);
                            v_snd_2411_ = v_snd_2408_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2423_ = crate::leanh::lean_unsigned_to_nat(2);
                            v___x_2424_ = lean_nat_add(v___y_2391_, v___x_2423_);
                            v___x_2425_ = crate::leanh::lean_box(0);
                            v___x_2426_ = lean_nat_dec_le(v___x_2421_, v___x_2421_);
                            if v___x_2426_ == 0 {
                                if v___x_2422_ == 0 {
                                    crate::leanh::lean_dec(v___x_2424_);
                                    crate::leanh::lean_dec_ref(v___x_2420_);
                                    v_snd_2411_ = v_snd_2408_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_2427_ = 0usize;
                                    v___x_2428_ = lean_usize_of_nat(v___x_2421_);
                                    v___x_2429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_2420_, v___x_2427_, v___x_2428_, v___x_2425_, v___x_2424_, v_snd_2408_);
                                    crate::leanh::lean_dec(v___x_2424_);
                                    crate::leanh::lean_dec_ref(v___x_2420_);
                                    v___y_2416_ = v___x_2429_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                v___x_2430_ = 0usize;
                                v___x_2431_ = lean_usize_of_nat(v___x_2421_);
                                v___x_2432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_2420_, v___x_2430_, v___x_2431_, v___x_2425_, v___x_2424_, v_snd_2408_);
                                crate::leanh::lean_dec(v___x_2424_);
                                crate::leanh::lean_dec_ref(v___x_2420_);
                                v___y_2416_ = v___x_2432_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2396_ = 1usize;
                v___x_2397_ = lean_usize_add(v_i_2389_, v___x_2396_);
                v_i_2389_ = v___x_2397_;
                v_b_2390_ = v_a_2394_;
                v___y_2392_ = v_snd_2395_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2412_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2411_);
                v_snd_2413_ = crate::leanh::lean_ctor_get(v___x_2412_, 1);
                crate::leanh::lean_inc(v_snd_2413_);
                crate::leanh::lean_dec_ref(v___x_2412_);
                v___x_2414_ = lean_nat_add(v_b_2390_, v___x_2409_);
                crate::leanh::lean_dec(v_b_2390_);
                v_a_2394_ = v___x_2414_;
                v_snd_2395_ = v_snd_2413_;
                state = 1;
                continue;
            }
            3 => {
                v_snd_2417_ = crate::leanh::lean_ctor_get(v___y_2416_, 1);
                crate::leanh::lean_inc(v_snd_2417_);
                crate::leanh::lean_dec_ref(v___y_2416_);
                v_snd_2411_ = v_snd_2417_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(
    mut v_as_2434_: *mut crate::leanh::LeanObject,
    mut v_i_2435_: usize,
    mut v_stop_2436_: usize,
    mut v_b_2437_: *mut crate::leanh::LeanObject,
    mut v___y_2438_: *mut crate::leanh::LeanObject,
    mut v___y_2439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: usize = 0;
    let mut v___x_2444_: usize = 0;
    let mut v___y_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: u8 = 0;
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: u8 = 0;
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: u8 = 0;
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: u8 = 0;
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: usize = 0;
    let mut v___x_2475_: usize = 0;
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: usize = 0;
    let mut v___x_2478_: usize = 0;
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2454_ = lean_usize_dec_eq(v_i_2435_, v_stop_2436_);
                if v___x_2454_ == 0 {
                    v___x_2455_ = lean_array_uget_borrowed(v_as_2434_, v_i_2435_);
                    v___x_2456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4;
                    crate::leanh::lean_inc(v___x_2455_);
                    v___x_2457_ = l_Lean_Syntax_isOfKind(v___x_2455_, v___x_2456_);
                    if v___x_2457_ == 0 {
                        v___x_2458_ = crate::leanh::lean_box(0);
                        v_fst_2441_ = v___x_2458_;
                        v_snd_2442_ = v___y_2439_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__5;
                        v___x_2460_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2459_, v___y_2439_);
                        v_snd_2461_ = crate::leanh::lean_ctor_get(v___x_2460_, 1);
                        crate::leanh::lean_inc(v_snd_2461_);
                        crate::leanh::lean_dec_ref(v___x_2460_);
                        v___x_2462_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2463_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2464_ = l_Lean_Syntax_getArg(v___x_2455_, v___x_2462_);
                        v___x_2465_ = l_Lean_Syntax_getArgs(v___x_2464_);
                        crate::leanh::lean_dec(v___x_2464_);
                        v___x_2466_ = lean_array_get_size(v___x_2465_);
                        v___x_2467_ = lean_nat_dec_lt(v___x_2463_, v___x_2466_);
                        if v___x_2467_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2465_);
                            v___x_2468_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2461_);
                            v___y_2447_ = v___x_2468_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2469_ = crate::leanh::lean_unsigned_to_nat(2);
                            v___x_2470_ = lean_nat_add(v___y_2438_, v___x_2469_);
                            v___x_2471_ = crate::leanh::lean_box(0);
                            v___x_2472_ = lean_nat_dec_le(v___x_2466_, v___x_2466_);
                            if v___x_2472_ == 0 {
                                if v___x_2467_ == 0 {
                                    crate::leanh::lean_dec(v___x_2470_);
                                    crate::leanh::lean_dec_ref(v___x_2465_);
                                    v___x_2473_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2461_);
                                    v___y_2447_ = v___x_2473_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_2474_ = 0usize;
                                    v___x_2475_ = lean_usize_of_nat(v___x_2466_);
                                    v___x_2476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_2465_, v___x_2474_, v___x_2475_, v___x_2471_, v___x_2470_, v_snd_2461_);
                                    crate::leanh::lean_dec(v___x_2470_);
                                    crate::leanh::lean_dec_ref(v___x_2465_);
                                    v___y_2451_ = v___x_2476_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                v___x_2477_ = 0usize;
                                v___x_2478_ = lean_usize_of_nat(v___x_2466_);
                                v___x_2479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_2465_, v___x_2477_, v___x_2478_, v___x_2471_, v___x_2470_, v_snd_2461_);
                                crate::leanh::lean_dec(v___x_2470_);
                                crate::leanh::lean_dec_ref(v___x_2465_);
                                v___y_2451_ = v___x_2479_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_2480_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2480_, 0, v_b_2437_);
                    crate::leanh::lean_ctor_set(v___x_2480_, 1, v___y_2439_);
                    return v___x_2480_;
                }
            }
            1 => {
                v___x_2443_ = 1usize;
                v___x_2444_ = lean_usize_add(v_i_2435_, v___x_2443_);
                v_i_2435_ = v___x_2444_;
                v_b_2437_ = v_fst_2441_;
                v___y_2439_ = v_snd_2442_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_2448_ = crate::leanh::lean_ctor_get(v___y_2447_, 0);
                crate::leanh::lean_inc(v_fst_2448_);
                v_snd_2449_ = crate::leanh::lean_ctor_get(v___y_2447_, 1);
                crate::leanh::lean_inc(v_snd_2449_);
                crate::leanh::lean_dec_ref(v___y_2447_);
                v_fst_2441_ = v_fst_2448_;
                v_snd_2442_ = v_snd_2449_;
                state = 1;
                continue;
            }
            3 => {
                v_snd_2452_ = crate::leanh::lean_ctor_get(v___y_2451_, 1);
                crate::leanh::lean_inc(v_snd_2452_);
                crate::leanh::lean_dec_ref(v___y_2451_);
                v___x_2453_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2452_);
                v___y_2447_ = v___x_2453_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(
    mut v_stx_2495_: *mut crate::leanh::LeanObject,
    mut v_a_2496_: *mut crate::leanh::LeanObject,
    mut v_a_2497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: u8 = 0;
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: u8 = 0;
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: u8 = 0;
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: u8 = 0;
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: u8 = 0;
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: u8 = 0;
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: u8 = 0;
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: u8 = 0;
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: u8 = 0;
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: u8 = 0;
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: u8 = 0;
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: u8 = 0;
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: u8 = 0;
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: u8 = 0;
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: u8 = 0;
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: u8 = 0;
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: u8 = 0;
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: u8 = 0;
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: u8 = 0;
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: u8 = 0;
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: u8 = 0;
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: u8 = 0;
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: u8 = 0;
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: u8 = 0;
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: u8 = 0;
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: u8 = 0;
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: u8 = 0;
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: u8 = 0;
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: u8 = 0;
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: u8 = 0;
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2602_: usize = 0;
    let mut v___x_2603_: usize = 0;
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2629_: usize = 0;
    let mut v___x_2630_: usize = 0;
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_blks_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: u8 = 0;
    let mut v___x_2656_: u8 = 0;
    let mut v___x_2657_: usize = 0;
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: usize = 0;
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: u8 = 0;
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2685_: usize = 0;
    let mut v___x_2686_: usize = 0;
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_blks_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: u8 = 0;
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: u8 = 0;
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: usize = 0;
    let mut v___x_2737_: usize = 0;
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: usize = 0;
    let mut v___x_2740_: usize = 0;
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2750_: usize = 0;
    let mut v___x_2751_: usize = 0;
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: u8 = 0;
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: u8 = 0;
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: usize = 0;
    let mut v___x_2768_: usize = 0;
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: usize = 0;
    let mut v___x_2771_: usize = 0;
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inl_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: u8 = 0;
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: u8 = 0;
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: usize = 0;
    let mut v___x_2786_: usize = 0;
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: usize = 0;
    let mut v___x_2789_: usize = 0;
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inl_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: u8 = 0;
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: u8 = 0;
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: usize = 0;
    let mut v___x_2811_: usize = 0;
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: usize = 0;
    let mut v___x_2814_: usize = 0;
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: u8 = 0;
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk3_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: u8 = 0;
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk3_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2974_: usize = 0;
    let mut v___x_2975_: usize = 0;
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inls_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: u8 = 0;
    let mut v___x_2987_: u8 = 0;
    let mut v___x_2988_: usize = 0;
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: usize = 0;
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inl_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: u8 = 0;
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: u8 = 0;
    let mut v___x_3040_: usize = 0;
    let mut v___x_3041_: usize = 0;
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: usize = 0;
    let mut v___x_3044_: usize = 0;
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inl_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: u8 = 0;
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: u8 = 0;
    let mut v___x_3067_: usize = 0;
    let mut v___x_3068_: usize = 0;
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: usize = 0;
    let mut v___x_3071_: usize = 0;
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inl_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: u8 = 0;
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: u8 = 0;
    let mut v___x_3094_: usize = 0;
    let mut v___x_3095_: usize = 0;
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: usize = 0;
    let mut v___x_3098_: usize = 0;
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: u8 = 0;
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: u8 = 0;
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: u8 = 0;
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: u8 = 0;
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: u8 = 0;
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: u8 = 0;
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: u8 = 0;
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: u8 = 0;
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: u8 = 0;
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: usize = 0;
    let mut v___x_3231_: usize = 0;
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: usize = 0;
    let mut v___x_3234_: usize = 0;
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_stx_2495_);
                v___x_2521_ = l_Lean_Syntax_getKind(v_stx_2495_);
                v___x_2522_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__2;
                v___x_2523_ = lean_name_eq(v___x_2521_, v___x_2522_);
                crate::leanh::lean_dec(v___x_2521_);
                if v___x_2523_ == 0 {
                    v___x_2524_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4;
                    crate::leanh::lean_inc(v_stx_2495_);
                    v___x_2525_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2524_);
                    if v___x_2525_ == 0 {
                        v___x_2526_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6;
                        crate::leanh::lean_inc(v_stx_2495_);
                        v___x_2527_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2526_);
                        if v___x_2527_ == 0 {
                            v___x_2528_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8;
                            crate::leanh::lean_inc(v_stx_2495_);
                            v___x_2529_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2528_);
                            if v___x_2529_ == 0 {
                                v___x_2530_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10;
                                crate::leanh::lean_inc(v_stx_2495_);
                                v___x_2531_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2530_);
                                if v___x_2531_ == 0 {
                                    v___x_2532_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12;
                                    crate::leanh::lean_inc(v_stx_2495_);
                                    v___x_2533_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2532_);
                                    if v___x_2533_ == 0 {
                                        v___x_2534_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14;
                                        crate::leanh::lean_inc(v_stx_2495_);
                                        v___x_2535_ =
                                            l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2534_);
                                        if v___x_2535_ == 0 {
                                            v___x_2536_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16;
                                            crate::leanh::lean_inc(v_stx_2495_);
                                            v___x_2537_ =
                                                l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2536_);
                                            if v___x_2537_ == 0 {
                                                v___x_2538_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18;
                                                crate::leanh::lean_inc(v_stx_2495_);
                                                v___x_2539_ = l_Lean_Syntax_isOfKind(
                                                    v_stx_2495_,
                                                    v___x_2538_,
                                                );
                                                if v___x_2539_ == 0 {
                                                    v___x_2540_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20;
                                                    crate::leanh::lean_inc(v_stx_2495_);
                                                    v___x_2541_ = l_Lean_Syntax_isOfKind(
                                                        v_stx_2495_,
                                                        v___x_2540_,
                                                    );
                                                    if v___x_2541_ == 0 {
                                                        v___x_2542_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22;
                                                        crate::leanh::lean_inc(v_stx_2495_);
                                                        v___x_2543_ = l_Lean_Syntax_isOfKind(
                                                            v_stx_2495_,
                                                            v___x_2542_,
                                                        );
                                                        if v___x_2543_ == 0 {
                                                            v___x_2544_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24;
                                                            crate::leanh::lean_inc(v_stx_2495_);
                                                            v___x_2545_ = l_Lean_Syntax_isOfKind(
                                                                v_stx_2495_,
                                                                v___x_2544_,
                                                            );
                                                            if v___x_2545_ == 0 {
                                                                v___x_2546_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26;
                                                                crate::leanh::lean_inc(v_stx_2495_);
                                                                v___x_2547_ =
                                                                    l_Lean_Syntax_isOfKind(
                                                                        v_stx_2495_,
                                                                        v___x_2546_,
                                                                    );
                                                                if v___x_2547_ == 0 {
                                                                    v___x_2548_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28;
                                                                    crate::leanh::lean_inc(
                                                                        v_stx_2495_,
                                                                    );
                                                                    v___x_2549_ =
                                                                        l_Lean_Syntax_isOfKind(
                                                                            v_stx_2495_,
                                                                            v___x_2548_,
                                                                        );
                                                                    if v___x_2549_ == 0 {
                                                                        v___x_2550_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30;
                                                                        crate::leanh::lean_inc(
                                                                            v_stx_2495_,
                                                                        );
                                                                        v___x_2551_ =
                                                                            l_Lean_Syntax_isOfKind(
                                                                                v_stx_2495_,
                                                                                v___x_2550_,
                                                                            );
                                                                        if v___x_2551_ == 0 {
                                                                            v___x_2552_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32;
                                                                            crate::leanh::lean_inc(
                                                                                v_stx_2495_,
                                                                            );
                                                                            v___x_2553_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2552_);
                                                                            if v___x_2553_ == 0 {
                                                                                v___x_2554_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34;
                                                                                crate::leanh::lean_inc(v_stx_2495_);
                                                                                v___x_2555_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2554_);
                                                                                if v___x_2555_ == 0
                                                                                {
                                                                                    v___x_2556_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36;
                                                                                    crate::leanh::lean_inc(v_stx_2495_);
                                                                                    v___x_2557_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2556_);
                                                                                    if v___x_2557_
                                                                                        == 0
                                                                                    {
                                                                                        v___x_2558_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38;
                                                                                        crate::leanh::lean_inc(v_stx_2495_);
                                                                                        v___x_2559_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2558_);
                                                                                        if v___x_2559_ == 0 {
v___x_2560_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40;
crate::leanh::lean_inc(v_stx_2495_);
v___x_2561_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2560_);
if v___x_2561_ == 0 {
v___x_2562_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42;
crate::leanh::lean_inc(v_stx_2495_);
v___x_2563_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2562_);
if v___x_2563_ == 0 {
v___x_2564_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44;
crate::leanh::lean_inc(v_stx_2495_);
v___x_2565_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2564_);
if v___x_2565_ == 0 {
v___x_2566_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46;
crate::leanh::lean_inc(v_stx_2495_);
v___x_2567_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2566_);
if v___x_2567_ == 0 {
v___x_2568_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48;
crate::leanh::lean_inc(v_stx_2495_);
v___x_2569_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2568_);
if v___x_2569_ == 0 {
v___x_2570_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50;
crate::leanh::lean_inc(v_stx_2495_);
v___x_2571_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2570_);
if v___x_2571_ == 0 {
v___x_2572_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52;
crate::leanh::lean_inc(v_stx_2495_);
v___x_2573_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2572_);
if v___x_2573_ == 0 {
v___x_2574_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54;
crate::leanh::lean_inc(v_stx_2495_);
v___x_2575_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2574_);
if v___x_2575_ == 0 {
v___x_2576_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56;
crate::leanh::lean_inc(v_stx_2495_);
v___x_2577_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2576_);
if v___x_2577_ == 0 {
v___x_2578_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58;
crate::leanh::lean_inc(v_stx_2495_);
v___x_2579_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2578_);
if v___x_2579_ == 0 {
v___x_2580_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60;
crate::leanh::lean_inc(v_stx_2495_);
v___x_2581_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2580_);
if v___x_2581_ == 0 {
v___x_2582_ = crate::leanh::lean_box(0);
v___x_2583_ = l_Lean_Syntax_formatStx(v_stx_2495_, v___x_2582_, v___x_2581_);
v___x_2584_ = l_Std_Format_defWidth;
v___x_2585_ = crate::leanh::lean_unsigned_to_nat(0);
v___x_2586_ = l_Std_Format_pretty(v___x_2583_, v___x_2584_, v___x_2585_, v___x_2585_);
v___x_2587_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2586_, v_a_2497_);
crate::leanh::lean_dec_ref(v___x_2586_);
return v___x_2587_;
} else {
v___x_2588_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_2496_, v_a_2497_);
v_snd_2589_ = crate::leanh::lean_ctor_get(v___x_2588_, 1);
crate::leanh::lean_inc(v_snd_2589_);
crate::leanh::lean_dec_ref(v___x_2588_);
v___x_2590_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__61;
v___x_2591_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2590_, v_snd_2589_);
v_snd_2592_ = crate::leanh::lean_ctor_get(v___x_2591_, 1);
crate::leanh::lean_inc(v_snd_2592_);
crate::leanh::lean_dec_ref(v___x_2591_);
v___x_2593_ = crate::leanh::lean_unsigned_to_nat(1);
v___x_2594_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2593_);
v___x_2595_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_2594_);
v___x_2596_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2595_, v_snd_2592_);
crate::leanh::lean_dec_ref(v___x_2595_);
v_snd_2597_ = crate::leanh::lean_ctor_get(v___x_2596_, 1);
crate::leanh::lean_inc(v_snd_2597_);
crate::leanh::lean_dec_ref(v___x_2596_);
v___x_2598_ = crate::leanh::lean_unsigned_to_nat(2);
v___x_2599_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2598_);
crate::leanh::lean_dec(v_stx_2495_);
v_args_2600_ = l_Lean_Syntax_getArgs(v___x_2599_);
crate::leanh::lean_dec(v___x_2599_);
v___x_2601_ = crate::leanh::lean_box(0);
v_sz_2602_ = lean_array_size(v_args_2600_);
v___x_2603_ = 0usize;
v___x_2604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(v_args_2600_, v_sz_2602_, v___x_2603_, v___x_2601_, v_a_2496_, v_snd_2597_);
crate::leanh::lean_dec_ref(v_args_2600_);
v_snd_2605_ = crate::leanh::lean_ctor_get(v___x_2604_, 1);
crate::leanh::lean_inc(v_snd_2605_);
crate::leanh::lean_dec_ref(v___x_2604_);
v___x_2606_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__62;
v___x_2607_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2606_, v_snd_2605_);
v_snd_2608_ = crate::leanh::lean_ctor_get(v___x_2607_, 1);
crate::leanh::lean_inc(v_snd_2608_);
crate::leanh::lean_dec_ref(v___x_2607_);
v___x_2609_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2608_);
return v___x_2609_;
}
} else {
v___x_2610_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_2496_, v_a_2497_);
v_snd_2611_ = crate::leanh::lean_ctor_get(v___x_2610_, 1);
crate::leanh::lean_inc(v_snd_2611_);
crate::leanh::lean_dec_ref(v___x_2610_);
v___x_2612_ = crate::leanh::lean_unsigned_to_nat(0);
v_tk1_2613_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2612_);
v___x_2614_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_2613_);
v___x_2615_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2614_, v_snd_2611_);
crate::leanh::lean_dec_ref(v___x_2614_);
v_snd_2616_ = crate::leanh::lean_ctor_get(v___x_2615_, 1);
crate::leanh::lean_inc(v_snd_2616_);
crate::leanh::lean_dec_ref(v___x_2615_);
v___x_2617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0;
v___x_2618_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2617_, v_snd_2616_);
v_snd_2619_ = crate::leanh::lean_ctor_get(v___x_2618_, 1);
crate::leanh::lean_inc(v_snd_2619_);
crate::leanh::lean_dec_ref(v___x_2618_);
v___x_2620_ = crate::leanh::lean_unsigned_to_nat(1);
v___x_2621_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2620_);
v___x_2622_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_2621_);
v___x_2623_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2622_, v_snd_2619_);
crate::leanh::lean_dec_ref(v___x_2622_);
v_snd_2624_ = crate::leanh::lean_ctor_get(v___x_2623_, 1);
crate::leanh::lean_inc(v_snd_2624_);
crate::leanh::lean_dec_ref(v___x_2623_);
v___x_2625_ = crate::leanh::lean_unsigned_to_nat(2);
v___x_2626_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2625_);
v_args_2627_ = l_Lean_Syntax_getArgs(v___x_2626_);
crate::leanh::lean_dec(v___x_2626_);
v___x_2628_ = crate::leanh::lean_box(0);
v_sz_2629_ = lean_array_size(v_args_2627_);
v___x_2630_ = 0usize;
v___x_2631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__1(v_args_2627_, v_sz_2629_, v___x_2630_, v___x_2628_, v_a_2496_, v_snd_2624_);
crate::leanh::lean_dec_ref(v_args_2627_);
v_snd_2632_ = crate::leanh::lean_ctor_get(v___x_2631_, 1);
crate::leanh::lean_inc(v_snd_2632_);
crate::leanh::lean_dec_ref(v___x_2631_);
v___x_2633_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0;
v___x_2634_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2633_, v_snd_2632_);
v_snd_2635_ = crate::leanh::lean_ctor_get(v___x_2634_, 1);
crate::leanh::lean_inc(v_snd_2635_);
crate::leanh::lean_dec_ref(v___x_2634_);
v___x_2636_ = crate::leanh::lean_unsigned_to_nat(4);
v___x_2637_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2636_);
v___x_2638_ = crate::leanh::lean_unsigned_to_nat(5);
v_tk2_2639_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2638_);
crate::leanh::lean_dec(v_stx_2495_);
v_blks_2653_ = l_Lean_Syntax_getArgs(v___x_2637_);
crate::leanh::lean_dec(v___x_2637_);
v___x_2654_ = lean_array_get_size(v_blks_2653_);
v___x_2655_ = lean_nat_dec_lt(v___x_2612_, v___x_2654_);
if v___x_2655_ == 0 {
crate::leanh::lean_dec_ref(v_blks_2653_);
v_snd_2641_ = v_snd_2635_;
state = 7; continue;
} else {
v___x_2656_ = lean_nat_dec_le(v___x_2654_, v___x_2654_);
if v___x_2656_ == 0 {
if v___x_2655_ == 0 {
crate::leanh::lean_dec_ref(v_blks_2653_);
v_snd_2641_ = v_snd_2635_;
state = 7; continue;
} else {
v___x_2657_ = lean_usize_of_nat(v___x_2654_);
v___x_2658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_blks_2653_, v___x_2630_, v___x_2657_, v___x_2628_, v_a_2496_, v_snd_2635_);
crate::leanh::lean_dec_ref(v_blks_2653_);
v___y_2651_ = v___x_2658_;
state = 8; continue;
}
} else {
v___x_2659_ = lean_usize_of_nat(v___x_2654_);
v___x_2660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_blks_2653_, v___x_2630_, v___x_2659_, v___x_2628_, v_a_2496_, v_snd_2635_);
crate::leanh::lean_dec_ref(v_blks_2653_);
v___y_2651_ = v___x_2660_;
state = 8; continue;
}
}
}
} else {
v___x_2661_ = crate::leanh::lean_unsigned_to_nat(1);
v___x_2662_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2661_);
v___x_2663_ = crate::leanh::lean_unsigned_to_nat(2);
crate::leanh::lean_inc(v___x_2662_);
v___x_2664_ = l_Lean_Syntax_matchesNull(v___x_2662_, v___x_2663_);
if v___x_2664_ == 0 {
crate::leanh::lean_dec(v___x_2662_);
v___x_2665_ = crate::leanh::lean_box(0);
v___x_2666_ = l_Lean_Syntax_formatStx(v_stx_2495_, v___x_2665_, v___x_2664_);
v___x_2667_ = l_Std_Format_defWidth;
v___x_2668_ = crate::leanh::lean_unsigned_to_nat(0);
v___x_2669_ = l_Std_Format_pretty(v___x_2666_, v___x_2667_, v___x_2668_, v___x_2668_);
v___x_2670_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2669_, v_a_2497_);
crate::leanh::lean_dec_ref(v___x_2669_);
return v___x_2670_;
} else {
v___x_2671_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_2496_, v_a_2497_);
v_snd_2672_ = crate::leanh::lean_ctor_get(v___x_2671_, 1);
crate::leanh::lean_inc(v_snd_2672_);
crate::leanh::lean_dec_ref(v___x_2671_);
v___x_2673_ = crate::leanh::lean_unsigned_to_nat(0);
v_tk1_2674_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2673_);
v___x_2675_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_2674_);
v___x_2676_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2675_, v_snd_2672_);
crate::leanh::lean_dec_ref(v___x_2675_);
v_snd_2677_ = crate::leanh::lean_ctor_get(v___x_2676_, 1);
crate::leanh::lean_inc(v_snd_2677_);
crate::leanh::lean_dec_ref(v___x_2676_);
v___x_2678_ = l_Lean_Syntax_getArg(v___x_2662_, v___x_2673_);
v___x_2679_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_2678_);
v___x_2680_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2679_, v_snd_2677_);
crate::leanh::lean_dec_ref(v___x_2679_);
v_snd_2681_ = crate::leanh::lean_ctor_get(v___x_2680_, 1);
crate::leanh::lean_inc(v_snd_2681_);
crate::leanh::lean_dec_ref(v___x_2680_);
v___x_2682_ = l_Lean_Syntax_getArg(v___x_2662_, v___x_2661_);
crate::leanh::lean_dec(v___x_2662_);
v_args_2683_ = l_Lean_Syntax_getArgs(v___x_2682_);
crate::leanh::lean_dec(v___x_2682_);
v___x_2684_ = crate::leanh::lean_box(0);
v_sz_2685_ = lean_array_size(v_args_2683_);
v___x_2686_ = 0usize;
v___x_2687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(v_args_2683_, v_sz_2685_, v___x_2686_, v___x_2684_, v_a_2496_, v_snd_2681_);
crate::leanh::lean_dec_ref(v_args_2683_);
v_snd_2688_ = crate::leanh::lean_ctor_get(v___x_2687_, 1);
crate::leanh::lean_inc(v_snd_2688_);
crate::leanh::lean_dec_ref(v___x_2687_);
v___x_2689_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0;
v___x_2690_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2689_, v_snd_2688_);
v_snd_2691_ = crate::leanh::lean_ctor_get(v___x_2690_, 1);
crate::leanh::lean_inc(v_snd_2691_);
crate::leanh::lean_dec_ref(v___x_2690_);
v___x_2692_ = crate::leanh::lean_unsigned_to_nat(3);
v___x_2693_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2692_);
v___x_2694_ = crate::leanh::lean_unsigned_to_nat(4);
v_tk2_2695_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2694_);
crate::leanh::lean_dec(v_stx_2495_);
v___x_2715_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_2693_);
v___x_2716_ = l_Lean_Syntax_decodeStrLit(v___x_2715_);
if crate::leanh::lean_obj_tag(v___x_2716_) == 0 {
v___x_2717_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
v___y_2697_ = v___x_2717_;
state = 9; continue;
} else {
v_val_2718_ = crate::leanh::lean_ctor_get(v___x_2716_, 0);
crate::leanh::lean_inc(v_val_2718_);
crate::leanh::lean_dec_ref_known(v___x_2716_, 1);
v___y_2697_ = v_val_2718_;
state = 9; continue;
}
}
}
} else {
v___x_2719_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_2496_, v_a_2497_);
v_snd_2720_ = crate::leanh::lean_ctor_get(v___x_2719_, 1);
crate::leanh::lean_inc(v_snd_2720_);
crate::leanh::lean_dec_ref(v___x_2719_);
v___x_2721_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__64;
v___x_2722_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2721_, v_snd_2720_);
v_snd_2723_ = crate::leanh::lean_ctor_get(v___x_2722_, 1);
crate::leanh::lean_inc(v_snd_2723_);
crate::leanh::lean_dec_ref(v___x_2722_);
v___x_2724_ = crate::leanh::lean_unsigned_to_nat(0);
v___x_2725_ = crate::leanh::lean_unsigned_to_nat(1);
v___x_2726_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2725_);
crate::leanh::lean_dec(v_stx_2495_);
v_blks_2727_ = l_Lean_Syntax_getArgs(v___x_2726_);
crate::leanh::lean_dec(v___x_2726_);
v___x_2728_ = lean_array_get_size(v_blks_2727_);
v___x_2729_ = lean_nat_dec_lt(v___x_2724_, v___x_2728_);
if v___x_2729_ == 0 {
crate::leanh::lean_dec_ref(v_blks_2727_);
v___x_2730_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2723_);
return v___x_2730_;
} else {
v___x_2731_ = crate::leanh::lean_unsigned_to_nat(2);
v___x_2732_ = lean_nat_add(v_a_2496_, v___x_2731_);
v___x_2733_ = crate::leanh::lean_box(0);
v___x_2734_ = lean_nat_dec_le(v___x_2728_, v___x_2728_);
if v___x_2734_ == 0 {
if v___x_2729_ == 0 {
crate::leanh::lean_dec(v___x_2732_);
crate::leanh::lean_dec_ref(v_blks_2727_);
v___x_2735_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2723_);
return v___x_2735_;
} else {
v___x_2736_ = 0usize;
v___x_2737_ = lean_usize_of_nat(v___x_2728_);
v___x_2738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_blks_2727_, v___x_2736_, v___x_2737_, v___x_2733_, v___x_2732_, v_snd_2723_);
crate::leanh::lean_dec(v___x_2732_);
crate::leanh::lean_dec_ref(v_blks_2727_);
v___y_2518_ = v___x_2738_;
state = 6; continue;
}
} else {
v___x_2739_ = 0usize;
v___x_2740_ = lean_usize_of_nat(v___x_2728_);
v___x_2741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_blks_2727_, v___x_2739_, v___x_2740_, v___x_2733_, v___x_2732_, v_snd_2723_);
crate::leanh::lean_dec(v___x_2732_);
crate::leanh::lean_dec_ref(v_blks_2727_);
v___y_2518_ = v___x_2741_;
state = 6; continue;
}
}
}
} else {
v___x_2742_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_2496_, v_a_2497_);
v_snd_2743_ = crate::leanh::lean_ctor_get(v___x_2742_, 1);
crate::leanh::lean_inc(v_snd_2743_);
crate::leanh::lean_dec_ref(v___x_2742_);
v___x_2744_ = crate::leanh::lean_unsigned_to_nat(1);
v_n_2745_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2744_);
v___x_2746_ = crate::leanh::lean_unsigned_to_nat(4);
v___x_2747_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2746_);
crate::leanh::lean_dec(v_stx_2495_);
v_items_2748_ = l_Lean_Syntax_getArgs(v___x_2747_);
crate::leanh::lean_dec(v___x_2747_);
v___x_2749_ = l_Lean_TSyntax_getNat(v_n_2745_);
crate::leanh::lean_dec(v_n_2745_);
v_sz_2750_ = lean_array_size(v_items_2748_);
v___x_2751_ = 0usize;
v___x_2752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(v_items_2748_, v_sz_2750_, v___x_2751_, v___x_2749_, v_a_2496_, v_snd_2743_);
crate::leanh::lean_dec_ref(v_items_2748_);
v_snd_2753_ = crate::leanh::lean_ctor_get(v___x_2752_, 1);
crate::leanh::lean_inc(v_snd_2753_);
crate::leanh::lean_dec_ref(v___x_2752_);
v___x_2754_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2753_);
return v___x_2754_;
}
} else {
v___x_2755_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_2496_, v_a_2497_);
v_snd_2756_ = crate::leanh::lean_ctor_get(v___x_2755_, 1);
crate::leanh::lean_inc(v_snd_2756_);
crate::leanh::lean_dec_ref(v___x_2755_);
v___x_2757_ = crate::leanh::lean_unsigned_to_nat(0);
v___x_2758_ = crate::leanh::lean_unsigned_to_nat(1);
v___x_2759_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2758_);
crate::leanh::lean_dec(v_stx_2495_);
v_items_2760_ = l_Lean_Syntax_getArgs(v___x_2759_);
crate::leanh::lean_dec(v___x_2759_);
v___x_2761_ = lean_array_get_size(v_items_2760_);
v___x_2762_ = lean_nat_dec_lt(v___x_2757_, v___x_2761_);
if v___x_2762_ == 0 {
crate::leanh::lean_dec_ref(v_items_2760_);
v___x_2763_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2756_);
return v___x_2763_;
} else {
v___x_2764_ = crate::leanh::lean_box(0);
v___x_2765_ = lean_nat_dec_le(v___x_2761_, v___x_2761_);
if v___x_2765_ == 0 {
if v___x_2762_ == 0 {
crate::leanh::lean_dec_ref(v_items_2760_);
v___x_2766_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2756_);
return v___x_2766_;
} else {
v___x_2767_ = 0usize;
v___x_2768_ = lean_usize_of_nat(v___x_2761_);
v___x_2769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v_items_2760_, v___x_2767_, v___x_2768_, v___x_2764_, v_a_2496_, v_snd_2756_);
crate::leanh::lean_dec_ref(v_items_2760_);
v___y_2514_ = v___x_2769_;
state = 5; continue;
}
} else {
v___x_2770_ = 0usize;
v___x_2771_ = lean_usize_of_nat(v___x_2761_);
v___x_2772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v_items_2760_, v___x_2770_, v___x_2771_, v___x_2764_, v_a_2496_, v_snd_2756_);
crate::leanh::lean_dec_ref(v_items_2760_);
v___y_2514_ = v___x_2772_;
state = 5; continue;
}
}
}
} else {
v___x_2773_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_2496_, v_a_2497_);
v_snd_2774_ = crate::leanh::lean_ctor_get(v___x_2773_, 1);
crate::leanh::lean_inc(v_snd_2774_);
crate::leanh::lean_dec_ref(v___x_2773_);
v___x_2775_ = crate::leanh::lean_unsigned_to_nat(0);
v___x_2776_ = crate::leanh::lean_unsigned_to_nat(1);
v___x_2777_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2776_);
crate::leanh::lean_dec(v_stx_2495_);
v_inl_2778_ = l_Lean_Syntax_getArgs(v___x_2777_);
crate::leanh::lean_dec(v___x_2777_);
v___x_2779_ = lean_array_get_size(v_inl_2778_);
v___x_2780_ = lean_nat_dec_lt(v___x_2775_, v___x_2779_);
if v___x_2780_ == 0 {
crate::leanh::lean_dec_ref(v_inl_2778_);
v___x_2781_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2774_);
return v___x_2781_;
} else {
v___x_2782_ = crate::leanh::lean_box(0);
v___x_2783_ = lean_nat_dec_le(v___x_2779_, v___x_2779_);
if v___x_2783_ == 0 {
if v___x_2780_ == 0 {
crate::leanh::lean_dec_ref(v_inl_2778_);
v___x_2784_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2774_);
return v___x_2784_;
} else {
v___x_2785_ = 0usize;
v___x_2786_ = lean_usize_of_nat(v___x_2779_);
v___x_2787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_2778_, v___x_2785_, v___x_2786_, v___x_2782_, v_a_2496_, v_snd_2774_);
crate::leanh::lean_dec_ref(v_inl_2778_);
v___y_2510_ = v___x_2787_;
state = 4; continue;
}
} else {
v___x_2788_ = 0usize;
v___x_2789_ = lean_usize_of_nat(v___x_2779_);
v___x_2790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_2778_, v___x_2788_, v___x_2789_, v___x_2782_, v_a_2496_, v_snd_2774_);
crate::leanh::lean_dec_ref(v_inl_2778_);
v___y_2510_ = v___x_2790_;
state = 4; continue;
}
}
}
} else {
v___x_2791_ = crate::leanh::lean_unsigned_to_nat(1);
v_n_2792_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2791_);
v___x_2793_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__65;
v___x_2794_ = l_Lean_TSyntax_getNat(v_n_2792_);
crate::leanh::lean_dec(v_n_2792_);
v___x_2795_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(v___x_2794_, v___x_2793_);
v___x_2796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0;
v___x_2797_ = lean_string_append(v___x_2795_, v___x_2796_);
v___x_2798_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2797_, v_a_2497_);
crate::leanh::lean_dec_ref(v___x_2797_);
v_snd_2799_ = crate::leanh::lean_ctor_get(v___x_2798_, 1);
crate::leanh::lean_inc(v_snd_2799_);
crate::leanh::lean_dec_ref(v___x_2798_);
v___x_2800_ = crate::leanh::lean_unsigned_to_nat(0);
v___x_2801_ = crate::leanh::lean_unsigned_to_nat(4);
v___x_2802_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2801_);
crate::leanh::lean_dec(v_stx_2495_);
v_inl_2803_ = l_Lean_Syntax_getArgs(v___x_2802_);
crate::leanh::lean_dec(v___x_2802_);
v___x_2804_ = lean_array_get_size(v_inl_2803_);
v___x_2805_ = lean_nat_dec_lt(v___x_2800_, v___x_2804_);
if v___x_2805_ == 0 {
crate::leanh::lean_dec_ref(v_inl_2803_);
v___x_2806_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2799_);
return v___x_2806_;
} else {
v___x_2807_ = crate::leanh::lean_box(0);
v___x_2808_ = lean_nat_dec_le(v___x_2804_, v___x_2804_);
if v___x_2808_ == 0 {
if v___x_2805_ == 0 {
crate::leanh::lean_dec_ref(v_inl_2803_);
v___x_2809_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2799_);
return v___x_2809_;
} else {
v___x_2810_ = 0usize;
v___x_2811_ = lean_usize_of_nat(v___x_2804_);
v___x_2812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_2803_, v___x_2810_, v___x_2811_, v___x_2807_, v_a_2496_, v_snd_2799_);
crate::leanh::lean_dec_ref(v_inl_2803_);
v___y_2506_ = v___x_2812_;
state = 3; continue;
}
} else {
v___x_2813_ = 0usize;
v___x_2814_ = lean_usize_of_nat(v___x_2804_);
v___x_2815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_2803_, v___x_2813_, v___x_2814_, v___x_2807_, v_a_2496_, v_snd_2799_);
crate::leanh::lean_dec_ref(v_inl_2803_);
v___y_2506_ = v___x_2815_;
state = 3; continue;
}
}
}
} else {
v___x_2816_ = crate::leanh::lean_unsigned_to_nat(0);
v_tk1_2817_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2816_);
v___x_2818_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_2817_);
v___x_2819_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2818_, v_a_2497_);
crate::leanh::lean_dec_ref(v___x_2818_);
v_snd_2820_ = crate::leanh::lean_ctor_get(v___x_2819_, 1);
crate::leanh::lean_inc(v_snd_2820_);
crate::leanh::lean_dec_ref(v___x_2819_);
v___x_2821_ = crate::leanh::lean_unsigned_to_nat(1);
v___x_2822_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2821_);
v___x_2823_ = crate::leanh::lean_unsigned_to_nat(2);
v_tk2_2824_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2823_);
crate::leanh::lean_dec(v_stx_2495_);
v___x_2831_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_2822_);
v___x_2832_ = l_Lean_Syntax_decodeStrLit(v___x_2831_);
if crate::leanh::lean_obj_tag(v___x_2832_) == 0 {
v___x_2833_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
v___y_2826_ = v___x_2833_;
state = 10; continue;
} else {
v_val_2834_ = crate::leanh::lean_ctor_get(v___x_2832_, 0);
crate::leanh::lean_inc(v_val_2834_);
crate::leanh::lean_dec_ref_known(v___x_2832_, 1);
v___y_2826_ = v_val_2834_;
state = 10; continue;
}
}
} else {
v___x_2835_ = crate::leanh::lean_unsigned_to_nat(0);
v_tk1_2836_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2835_);
v___x_2837_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_2836_);
v___x_2838_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2837_, v_a_2497_);
crate::leanh::lean_dec_ref(v___x_2837_);
v_snd_2839_ = crate::leanh::lean_ctor_get(v___x_2838_, 1);
crate::leanh::lean_inc(v_snd_2839_);
crate::leanh::lean_dec_ref(v___x_2838_);
v___x_2840_ = crate::leanh::lean_unsigned_to_nat(1);
v___x_2841_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2840_);
v___x_2842_ = crate::leanh::lean_unsigned_to_nat(2);
v_tk2_2843_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2842_);
crate::leanh::lean_dec(v_stx_2495_);
v___x_2850_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_2841_);
v___x_2851_ = l_Lean_Syntax_decodeStrLit(v___x_2850_);
if crate::leanh::lean_obj_tag(v___x_2851_) == 0 {
v___x_2852_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
v___y_2845_ = v___x_2852_;
state = 11; continue;
} else {
v_val_2853_ = crate::leanh::lean_ctor_get(v___x_2851_, 0);
crate::leanh::lean_inc(v_val_2853_);
crate::leanh::lean_dec_ref_known(v___x_2851_, 1);
v___y_2845_ = v_val_2853_;
state = 11; continue;
}
}
} else {
v___x_2854_ = crate::leanh::lean_unsigned_to_nat(1);
v___x_2855_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2854_);
crate::leanh::lean_inc(v___x_2855_);
v___x_2856_ = l_Lean_Syntax_isOfKind(v___x_2855_, v___x_2552_);
if v___x_2856_ == 0 {
crate::leanh::lean_dec(v___x_2855_);
v___x_2857_ = crate::leanh::lean_box(0);
v___x_2858_ = l_Lean_Syntax_formatStx(v_stx_2495_, v___x_2857_, v___x_2856_);
v___x_2859_ = l_Std_Format_defWidth;
v___x_2860_ = crate::leanh::lean_unsigned_to_nat(0);
v___x_2861_ = l_Std_Format_pretty(v___x_2858_, v___x_2859_, v___x_2860_, v___x_2860_);
v___x_2862_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2861_, v_a_2497_);
crate::leanh::lean_dec_ref(v___x_2861_);
return v___x_2862_;
} else {
v___x_2863_ = crate::leanh::lean_unsigned_to_nat(0);
v_tk1_2864_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2863_);
crate::leanh::lean_dec(v_stx_2495_);
v___x_2865_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_2864_);
v___x_2866_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2865_, v_a_2497_);
crate::leanh::lean_dec_ref(v___x_2865_);
v_snd_2867_ = crate::leanh::lean_ctor_get(v___x_2866_, 1);
crate::leanh::lean_inc(v_snd_2867_);
crate::leanh::lean_dec_ref(v___x_2866_);
v_tk2_2868_ = l_Lean_Syntax_getArg(v___x_2855_, v___x_2863_);
v___x_2869_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_2868_);
v___x_2870_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2869_, v_snd_2867_);
crate::leanh::lean_dec_ref(v___x_2869_);
v_snd_2871_ = crate::leanh::lean_ctor_get(v___x_2870_, 1);
crate::leanh::lean_inc(v_snd_2871_);
crate::leanh::lean_dec_ref(v___x_2870_);
v___x_2872_ = l_Lean_Syntax_getArg(v___x_2855_, v___x_2854_);
v___x_2873_ = crate::leanh::lean_unsigned_to_nat(2);
v_tk3_2874_ = l_Lean_Syntax_getArg(v___x_2855_, v___x_2873_);
crate::leanh::lean_dec(v___x_2855_);
v___x_2881_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_2872_);
v___x_2882_ = l_Lean_Syntax_decodeStrLit(v___x_2881_);
if crate::leanh::lean_obj_tag(v___x_2882_) == 0 {
v___x_2883_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
v___y_2876_ = v___x_2883_;
state = 12; continue;
} else {
v_val_2884_ = crate::leanh::lean_ctor_get(v___x_2882_, 0);
crate::leanh::lean_inc(v_val_2884_);
crate::leanh::lean_dec_ref_known(v___x_2882_, 1);
v___y_2876_ = v_val_2884_;
state = 12; continue;
}
}
}
} else {
v___x_2885_ = crate::leanh::lean_unsigned_to_nat(1);
v___x_2886_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2885_);
crate::leanh::lean_inc(v___x_2886_);
v___x_2887_ = l_Lean_Syntax_isOfKind(v___x_2886_, v___x_2552_);
if v___x_2887_ == 0 {
crate::leanh::lean_dec(v___x_2886_);
v___x_2888_ = crate::leanh::lean_box(0);
v___x_2889_ = l_Lean_Syntax_formatStx(v_stx_2495_, v___x_2888_, v___x_2887_);
v___x_2890_ = l_Std_Format_defWidth;
v___x_2891_ = crate::leanh::lean_unsigned_to_nat(0);
v___x_2892_ = l_Std_Format_pretty(v___x_2889_, v___x_2890_, v___x_2891_, v___x_2891_);
v___x_2893_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2892_, v_a_2497_);
crate::leanh::lean_dec_ref(v___x_2892_);
return v___x_2893_;
} else {
v___x_2894_ = crate::leanh::lean_unsigned_to_nat(0);
v_tk1_2895_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2894_);
crate::leanh::lean_dec(v_stx_2495_);
v___x_2896_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_2895_);
v___x_2897_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2896_, v_a_2497_);
crate::leanh::lean_dec_ref(v___x_2896_);
v_snd_2898_ = crate::leanh::lean_ctor_get(v___x_2897_, 1);
crate::leanh::lean_inc(v_snd_2898_);
crate::leanh::lean_dec_ref(v___x_2897_);
v_tk2_2899_ = l_Lean_Syntax_getArg(v___x_2886_, v___x_2894_);
v___x_2900_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_2899_);
v___x_2901_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2900_, v_snd_2898_);
crate::leanh::lean_dec_ref(v___x_2900_);
v_snd_2902_ = crate::leanh::lean_ctor_get(v___x_2901_, 1);
crate::leanh::lean_inc(v_snd_2902_);
crate::leanh::lean_dec_ref(v___x_2901_);
v___x_2903_ = l_Lean_Syntax_getArg(v___x_2886_, v___x_2885_);
v___x_2904_ = crate::leanh::lean_unsigned_to_nat(2);
v_tk3_2905_ = l_Lean_Syntax_getArg(v___x_2886_, v___x_2904_);
crate::leanh::lean_dec(v___x_2886_);
v___x_2912_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_2903_);
v___x_2913_ = l_Lean_Syntax_decodeStrLit(v___x_2912_);
if crate::leanh::lean_obj_tag(v___x_2913_) == 0 {
v___x_2914_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
v___y_2907_ = v___x_2914_;
state = 13; continue;
} else {
v_val_2915_ = crate::leanh::lean_ctor_get(v___x_2913_, 0);
crate::leanh::lean_inc(v_val_2915_);
crate::leanh::lean_dec_ref_known(v___x_2913_, 1);
v___y_2907_ = v_val_2915_;
state = 13; continue;
}
}
}
                                                                                    } else {
                                                                                        v___x_2916_ = crate::leanh::lean_unsigned_to_nat(1);
                                                                                        v___x_2917_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2916_);
                                                                                        crate::leanh::lean_dec(v_stx_2495_);
                                                                                        v___x_2918_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_2917_);
                                                                                        v___x_2919_ = l_Lean_Syntax_decodeStrLit(v___x_2918_);
                                                                                        if crate::leanh::lean_obj_tag(v___x_2919_) == 0 {
v___x_2920_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
v___x_2921_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2920_, v_a_2497_);
return v___x_2921_;
} else {
v_val_2922_ = crate::leanh::lean_ctor_get(v___x_2919_, 0);
crate::leanh::lean_inc(v_val_2922_);
crate::leanh::lean_dec_ref_known(v___x_2919_, 1);
v___x_2923_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v_val_2922_, v_a_2497_);
crate::leanh::lean_dec(v_val_2922_);
return v___x_2923_;
}
                                                                                    }
                                                                                } else {
                                                                                    v___x_2924_ = crate::leanh::lean_unsigned_to_nat(0);
                                                                                    v_tk1_2925_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2924_);
                                                                                    v___x_2926_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_2925_);
                                                                                    v___x_2927_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2926_, v_a_2497_);
                                                                                    crate::leanh::lean_dec_ref(v___x_2926_);
                                                                                    v_snd_2928_ = crate::leanh::lean_ctor_get(v___x_2927_, 1);
                                                                                    crate::leanh::lean_inc(v_snd_2928_);
                                                                                    crate::leanh::lean_dec_ref(v___x_2927_);
                                                                                    v___x_2929_ = crate::leanh::lean_unsigned_to_nat(1);
                                                                                    v___x_2930_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2929_);
                                                                                    v___x_2931_ = crate::leanh::lean_unsigned_to_nat(2);
                                                                                    v_tk2_2932_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2931_);
                                                                                    crate::leanh::lean_dec(v_stx_2495_);
                                                                                    v___x_2939_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_2930_);
                                                                                    v___x_2940_ = l_Lean_Syntax_decodeStrLit(v___x_2939_);
                                                                                    if crate::leanh::lean_obj_tag(v___x_2940_) == 0 {
v___x_2941_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
v___y_2934_ = v___x_2941_;
state = 14; continue;
} else {
v_val_2942_ = crate::leanh::lean_ctor_get(v___x_2940_, 0);
crate::leanh::lean_inc(v_val_2942_);
crate::leanh::lean_dec_ref_known(v___x_2940_, 1);
v___y_2934_ = v_val_2942_;
state = 14; continue;
}
                                                                                }
                                                                            } else {
                                                                                v___x_2943_ = crate::leanh::lean_unsigned_to_nat(0);
                                                                                v_tk1_2944_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2943_);
                                                                                v___x_2945_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_2944_);
                                                                                v___x_2946_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2945_, v_a_2497_);
                                                                                crate::leanh::lean_dec_ref(v___x_2945_);
                                                                                v_snd_2947_ = crate::leanh::lean_ctor_get(v___x_2946_, 1);
                                                                                crate::leanh::lean_inc(v_snd_2947_);
                                                                                crate::leanh::lean_dec_ref(v___x_2946_);
                                                                                v___x_2948_ = crate::leanh::lean_unsigned_to_nat(1);
                                                                                v___x_2949_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2948_);
                                                                                v___x_2950_ = crate::leanh::lean_unsigned_to_nat(2);
                                                                                v_tk2_2951_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2950_);
                                                                                crate::leanh::lean_dec(v_stx_2495_);
                                                                                v___x_2958_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_2949_);
                                                                                v___x_2959_ = l_Lean_Syntax_decodeStrLit(v___x_2958_);
                                                                                if crate::leanh::lean_obj_tag(v___x_2959_) == 0 {
v___x_2960_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
v___y_2953_ = v___x_2960_;
state = 15; continue;
} else {
v_val_2961_ = crate::leanh::lean_ctor_get(v___x_2959_, 0);
crate::leanh::lean_inc(v_val_2961_);
crate::leanh::lean_dec_ref_known(v___x_2959_, 1);
v___y_2953_ = v_val_2961_;
state = 15; continue;
}
                                                                            }
                                                                        } else {
                                                                            v___x_2962_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__61;
                                                                            v___x_2963_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2962_, v_a_2497_);
                                                                            v_snd_2964_ = crate::leanh::lean_ctor_get(v___x_2963_, 1);
                                                                            crate::leanh::lean_inc(
                                                                                v_snd_2964_,
                                                                            );
                                                                            crate::leanh::lean_dec_ref(v___x_2963_);
                                                                            v___x_2965_ = crate::leanh::lean_unsigned_to_nat(1);
                                                                            v___x_2966_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2965_);
                                                                            v___x_2967_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_2966_);
                                                                            v___x_2968_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2967_, v_snd_2964_);
                                                                            crate::leanh::lean_dec_ref(v___x_2967_);
                                                                            v_snd_2969_ = crate::leanh::lean_ctor_get(v___x_2968_, 1);
                                                                            crate::leanh::lean_inc(
                                                                                v_snd_2969_,
                                                                            );
                                                                            crate::leanh::lean_dec_ref(v___x_2968_);
                                                                            v___x_2970_ = crate::leanh::lean_unsigned_to_nat(2);
                                                                            v___x_2971_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2970_);
                                                                            v_args_2972_ = l_Lean_Syntax_getArgs(v___x_2971_);
                                                                            crate::leanh::lean_dec(
                                                                                v___x_2971_,
                                                                            );
                                                                            v___x_2973_ = crate::leanh::lean_box(0);
                                                                            v_sz_2974_ =
                                                                                lean_array_size(
                                                                                    v_args_2972_,
                                                                                );
                                                                            v___x_2975_ = 0usize;
                                                                            v___x_2976_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(v_args_2972_, v_sz_2974_, v___x_2975_, v___x_2973_, v_a_2496_, v_snd_2969_);
                                                                            crate::leanh::lean_dec_ref(v_args_2972_);
                                                                            v_snd_2977_ = crate::leanh::lean_ctor_get(v___x_2976_, 1);
                                                                            crate::leanh::lean_inc(
                                                                                v_snd_2977_,
                                                                            );
                                                                            crate::leanh::lean_dec_ref(v___x_2976_);
                                                                            v___x_2978_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__66;
                                                                            v___x_2979_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2978_, v_snd_2977_);
                                                                            v_snd_2980_ = crate::leanh::lean_ctor_get(v___x_2979_, 1);
                                                                            crate::leanh::lean_inc(
                                                                                v_snd_2980_,
                                                                            );
                                                                            crate::leanh::lean_dec_ref(v___x_2979_);
                                                                            v___x_2981_ = crate::leanh::lean_unsigned_to_nat(0);
                                                                            v___x_2982_ = crate::leanh::lean_unsigned_to_nat(5);
                                                                            v___x_2983_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2982_);
                                                                            crate::leanh::lean_dec(
                                                                                v_stx_2495_,
                                                                            );
                                                                            v_inls_2984_ = l_Lean_Syntax_getArgs(v___x_2983_);
                                                                            crate::leanh::lean_dec(
                                                                                v___x_2983_,
                                                                            );
                                                                            v___x_2985_ =
                                                                                lean_array_get_size(
                                                                                    v_inls_2984_,
                                                                                );
                                                                            v___x_2986_ =
                                                                                lean_nat_dec_lt(
                                                                                    v___x_2981_,
                                                                                    v___x_2985_,
                                                                                );
                                                                            if v___x_2986_ == 0 {
                                                                                crate::leanh::lean_dec_ref(v_inls_2984_);
                                                                                v_snd_2499_ =
                                                                                    v_snd_2980_;
                                                                                state = 1;
                                                                                continue;
                                                                            } else {
                                                                                v___x_2987_ =
                                                                                    lean_nat_dec_le(
                                                                                        v___x_2985_,
                                                                                        v___x_2985_,
                                                                                    );
                                                                                if v___x_2987_ == 0
                                                                                {
                                                                                    if v___x_2986_
                                                                                        == 0
                                                                                    {
                                                                                        crate::leanh::lean_dec_ref(v_inls_2984_);
                                                                                        v_snd_2499_ = v_snd_2980_;
                                                                                        state = 1;
                                                                                        continue;
                                                                                    } else {
                                                                                        v___x_2988_ = lean_usize_of_nat(v___x_2985_);
                                                                                        v___x_2989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inls_2984_, v___x_2975_, v___x_2988_, v___x_2973_, v_a_2496_, v_snd_2980_);
                                                                                        crate::leanh::lean_dec_ref(v_inls_2984_);
                                                                                        v___y_2503_ = v___x_2989_;
                                                                                        state = 2;
                                                                                        continue;
                                                                                    }
                                                                                } else {
                                                                                    v___x_2990_ = lean_usize_of_nat(v___x_2985_);
                                                                                    v___x_2991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inls_2984_, v___x_2975_, v___x_2990_, v___x_2973_, v_a_2496_, v_snd_2980_);
                                                                                    crate::leanh::lean_dec_ref(v_inls_2984_);
                                                                                    v___y_2503_ =
                                                                                        v___x_2991_;
                                                                                    state = 2;
                                                                                    continue;
                                                                                }
                                                                            }
                                                                        }
                                                                    } else {
                                                                        v___x_2992_ = crate::leanh::lean_unsigned_to_nat(0);
                                                                        v_tk1_2993_ =
                                                                            l_Lean_Syntax_getArg(
                                                                                v_stx_2495_,
                                                                                v___x_2992_,
                                                                            );
                                                                        v___x_2994_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_2993_);
                                                                        v___x_2995_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2994_, v_a_2497_);
                                                                        crate::leanh::lean_dec_ref(
                                                                            v___x_2994_,
                                                                        );
                                                                        v_snd_2996_ = crate::leanh::lean_ctor_get(v___x_2995_, 1);
                                                                        crate::leanh::lean_inc(
                                                                            v_snd_2996_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v___x_2995_,
                                                                        );
                                                                        v___x_2997_ = crate::leanh::lean_unsigned_to_nat(1);
                                                                        v___x_2998_ =
                                                                            l_Lean_Syntax_getArg(
                                                                                v_stx_2495_,
                                                                                v___x_2997_,
                                                                            );
                                                                        v___x_2999_ = crate::leanh::lean_unsigned_to_nat(2);
                                                                        v_tk2_3000_ =
                                                                            l_Lean_Syntax_getArg(
                                                                                v_stx_2495_,
                                                                                v___x_2999_,
                                                                            );
                                                                        v___x_3001_ = crate::leanh::lean_unsigned_to_nat(3);
                                                                        v___x_3002_ =
                                                                            l_Lean_Syntax_getArg(
                                                                                v_stx_2495_,
                                                                                v___x_3001_,
                                                                            );
                                                                        crate::leanh::lean_dec(
                                                                            v_stx_2495_,
                                                                        );
                                                                        v___x_3011_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_2998_);
                                                                        v___x_3012_ = l_Lean_Syntax_decodeStrLit(v___x_3011_);
                                                                        if crate::leanh::lean_obj_tag(v___x_3012_) == 0 {
v___x_3013_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
v___y_3004_ = v___x_3013_;
state = 16; continue;
} else {
v_val_3014_ = crate::leanh::lean_ctor_get(v___x_3012_, 0);
crate::leanh::lean_inc(v_val_3014_);
crate::leanh::lean_dec_ref_known(v___x_3012_, 1);
v___y_3004_ = v_val_3014_;
state = 16; continue;
}
                                                                    }
                                                                } else {
                                                                    v___x_3015_ = crate::leanh::lean_unsigned_to_nat(0);
                                                                    v_tk1_3016_ =
                                                                        l_Lean_Syntax_getArg(
                                                                            v_stx_2495_,
                                                                            v___x_3015_,
                                                                        );
                                                                    v___x_3017_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_3016_);
                                                                    v___x_3018_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3017_, v_a_2497_);
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___x_3017_,
                                                                    );
                                                                    v_snd_3019_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_3018_,
                                                                            1,
                                                                        );
                                                                    crate::leanh::lean_inc(
                                                                        v_snd_3019_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___x_3018_,
                                                                    );
                                                                    v___x_3020_ = crate::leanh::lean_unsigned_to_nat(1);
                                                                    v___x_3021_ =
                                                                        l_Lean_Syntax_getArg(
                                                                            v_stx_2495_,
                                                                            v___x_3020_,
                                                                        );
                                                                    v___x_3022_ = crate::leanh::lean_unsigned_to_nat(2);
                                                                    v_tk2_3023_ =
                                                                        l_Lean_Syntax_getArg(
                                                                            v_stx_2495_,
                                                                            v___x_3022_,
                                                                        );
                                                                    v___x_3024_ = crate::leanh::lean_unsigned_to_nat(3);
                                                                    v___x_3025_ =
                                                                        l_Lean_Syntax_getArg(
                                                                            v_stx_2495_,
                                                                            v___x_3024_,
                                                                        );
                                                                    crate::leanh::lean_dec(
                                                                        v_stx_2495_,
                                                                    );
                                                                    v_inl_3035_ =
                                                                        l_Lean_Syntax_getArgs(
                                                                            v___x_3021_,
                                                                        );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_3021_,
                                                                    );
                                                                    v___x_3036_ =
                                                                        lean_array_get_size(
                                                                            v_inl_3035_,
                                                                        );
                                                                    v___x_3037_ = lean_nat_dec_lt(
                                                                        v___x_3015_,
                                                                        v___x_3036_,
                                                                    );
                                                                    if v___x_3037_ == 0 {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_inl_3035_,
                                                                        );
                                                                        v_snd_3027_ = v_snd_3019_;
                                                                        state = 17;
                                                                        continue;
                                                                    } else {
                                                                        v___x_3038_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v___x_3039_ =
                                                                            lean_nat_dec_le(
                                                                                v___x_3036_,
                                                                                v___x_3036_,
                                                                            );
                                                                        if v___x_3039_ == 0 {
                                                                            if v___x_3037_ == 0 {
                                                                                crate::leanh::lean_dec_ref(v_inl_3035_);
                                                                                v_snd_3027_ =
                                                                                    v_snd_3019_;
                                                                                state = 17;
                                                                                continue;
                                                                            } else {
                                                                                v___x_3040_ =
                                                                                    0usize;
                                                                                v___x_3041_ = lean_usize_of_nat(v___x_3036_);
                                                                                v___x_3042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_3035_, v___x_3040_, v___x_3041_, v___x_3038_, v_a_2496_, v_snd_3019_);
                                                                                crate::leanh::lean_dec_ref(v_inl_3035_);
                                                                                v___y_3033_ =
                                                                                    v___x_3042_;
                                                                                state = 18;
                                                                                continue;
                                                                            }
                                                                        } else {
                                                                            v___x_3043_ = 0usize;
                                                                            v___x_3044_ =
                                                                                lean_usize_of_nat(
                                                                                    v___x_3036_,
                                                                                );
                                                                            v___x_3045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_3035_, v___x_3043_, v___x_3044_, v___x_3038_, v_a_2496_, v_snd_3019_);
                                                                            crate::leanh::lean_dec_ref(v_inl_3035_);
                                                                            v___y_3033_ =
                                                                                v___x_3045_;
                                                                            state = 18;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                v___x_3046_ = crate::leanh::lean_unsigned_to_nat(0);
                                                                v_tk1_3047_ = l_Lean_Syntax_getArg(
                                                                    v_stx_2495_,
                                                                    v___x_3046_,
                                                                );
                                                                v___x_3048_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_3047_);
                                                                v___x_3049_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3048_, v_a_2497_);
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_3048_,
                                                                );
                                                                v_snd_3050_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_3049_,
                                                                        1,
                                                                    );
                                                                crate::leanh::lean_inc(v_snd_3050_);
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_3049_,
                                                                );
                                                                v___x_3051_ = crate::leanh::lean_unsigned_to_nat(1);
                                                                v___x_3052_ = l_Lean_Syntax_getArg(
                                                                    v_stx_2495_,
                                                                    v___x_3051_,
                                                                );
                                                                v___x_3053_ = crate::leanh::lean_unsigned_to_nat(2);
                                                                v_tk2_3054_ = l_Lean_Syntax_getArg(
                                                                    v_stx_2495_,
                                                                    v___x_3053_,
                                                                );
                                                                crate::leanh::lean_dec(v_stx_2495_);
                                                                v_inl_3062_ = l_Lean_Syntax_getArgs(
                                                                    v___x_3052_,
                                                                );
                                                                crate::leanh::lean_dec(v___x_3052_);
                                                                v___x_3063_ = lean_array_get_size(
                                                                    v_inl_3062_,
                                                                );
                                                                v___x_3064_ = lean_nat_dec_lt(
                                                                    v___x_3046_,
                                                                    v___x_3063_,
                                                                );
                                                                if v___x_3064_ == 0 {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_inl_3062_,
                                                                    );
                                                                    v_snd_3056_ = v_snd_3050_;
                                                                    state = 19;
                                                                    continue;
                                                                } else {
                                                                    v___x_3065_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v___x_3066_ = lean_nat_dec_le(
                                                                        v___x_3063_,
                                                                        v___x_3063_,
                                                                    );
                                                                    if v___x_3066_ == 0 {
                                                                        if v___x_3064_ == 0 {
                                                                            crate::leanh::lean_dec_ref(v_inl_3062_);
                                                                            v_snd_3056_ =
                                                                                v_snd_3050_;
                                                                            state = 19;
                                                                            continue;
                                                                        } else {
                                                                            v___x_3067_ = 0usize;
                                                                            v___x_3068_ =
                                                                                lean_usize_of_nat(
                                                                                    v___x_3063_,
                                                                                );
                                                                            v___x_3069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_3062_, v___x_3067_, v___x_3068_, v___x_3065_, v_a_2496_, v_snd_3050_);
                                                                            crate::leanh::lean_dec_ref(v_inl_3062_);
                                                                            v___y_3060_ =
                                                                                v___x_3069_;
                                                                            state = 20;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        v___x_3070_ = 0usize;
                                                                        v___x_3071_ =
                                                                            lean_usize_of_nat(
                                                                                v___x_3063_,
                                                                            );
                                                                        v___x_3072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_3062_, v___x_3070_, v___x_3071_, v___x_3065_, v_a_2496_, v_snd_3050_);
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_inl_3062_,
                                                                        );
                                                                        v___y_3060_ = v___x_3072_;
                                                                        state = 20;
                                                                        continue;
                                                                    }
                                                                }
                                                            }
                                                        } else {
                                                            v___x_3073_ =
                                                                crate::leanh::lean_unsigned_to_nat(
                                                                    0,
                                                                );
                                                            v_tk1_3074_ = l_Lean_Syntax_getArg(
                                                                v_stx_2495_,
                                                                v___x_3073_,
                                                            );
                                                            v___x_3075_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_3074_);
                                                            v___x_3076_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3075_, v_a_2497_);
                                                            crate::leanh::lean_dec_ref(v___x_3075_);
                                                            v_snd_3077_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v___x_3076_,
                                                                    1,
                                                                );
                                                            crate::leanh::lean_inc(v_snd_3077_);
                                                            crate::leanh::lean_dec_ref(v___x_3076_);
                                                            v___x_3078_ =
                                                                crate::leanh::lean_unsigned_to_nat(
                                                                    1,
                                                                );
                                                            v___x_3079_ = l_Lean_Syntax_getArg(
                                                                v_stx_2495_,
                                                                v___x_3078_,
                                                            );
                                                            v___x_3080_ =
                                                                crate::leanh::lean_unsigned_to_nat(
                                                                    2,
                                                                );
                                                            v_tk2_3081_ = l_Lean_Syntax_getArg(
                                                                v_stx_2495_,
                                                                v___x_3080_,
                                                            );
                                                            crate::leanh::lean_dec(v_stx_2495_);
                                                            v_inl_3089_ =
                                                                l_Lean_Syntax_getArgs(v___x_3079_);
                                                            crate::leanh::lean_dec(v___x_3079_);
                                                            v___x_3090_ =
                                                                lean_array_get_size(v_inl_3089_);
                                                            v___x_3091_ = lean_nat_dec_lt(
                                                                v___x_3073_,
                                                                v___x_3090_,
                                                            );
                                                            if v___x_3091_ == 0 {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_inl_3089_,
                                                                );
                                                                v_snd_3083_ = v_snd_3077_;
                                                                state = 21;
                                                                continue;
                                                            } else {
                                                                v___x_3092_ =
                                                                    crate::leanh::lean_box(0);
                                                                v___x_3093_ = lean_nat_dec_le(
                                                                    v___x_3090_,
                                                                    v___x_3090_,
                                                                );
                                                                if v___x_3093_ == 0 {
                                                                    if v___x_3091_ == 0 {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_inl_3089_,
                                                                        );
                                                                        v_snd_3083_ = v_snd_3077_;
                                                                        state = 21;
                                                                        continue;
                                                                    } else {
                                                                        v___x_3094_ = 0usize;
                                                                        v___x_3095_ =
                                                                            lean_usize_of_nat(
                                                                                v___x_3090_,
                                                                            );
                                                                        v___x_3096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_3089_, v___x_3094_, v___x_3095_, v___x_3092_, v_a_2496_, v_snd_3077_);
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_inl_3089_,
                                                                        );
                                                                        v___y_3087_ = v___x_3096_;
                                                                        state = 22;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    v___x_3097_ = 0usize;
                                                                    v___x_3098_ = lean_usize_of_nat(
                                                                        v___x_3090_,
                                                                    );
                                                                    v___x_3099_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_3089_, v___x_3097_, v___x_3098_, v___x_3092_, v_a_2496_, v_snd_3077_);
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_inl_3089_,
                                                                    );
                                                                    v___y_3087_ = v___x_3099_;
                                                                    state = 22;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    } else {
                                                        v___x_3100_ =
                                                            crate::leanh::lean_unsigned_to_nat(0);
                                                        v_s_3101_ = l_Lean_Syntax_getArg(
                                                            v_stx_2495_,
                                                            v___x_3100_,
                                                        );
                                                        v___x_3102_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__68;
                                                        crate::leanh::lean_inc(v_s_3101_);
                                                        v___x_3103_ = l_Lean_Syntax_isOfKind(
                                                            v_s_3101_,
                                                            v___x_3102_,
                                                        );
                                                        if v___x_3103_ == 0 {
                                                            crate::leanh::lean_dec(v_s_3101_);
                                                            v___x_3104_ = crate::leanh::lean_box(0);
                                                            v___x_3105_ = l_Lean_Syntax_formatStx(
                                                                v_stx_2495_,
                                                                v___x_3104_,
                                                                v___x_3103_,
                                                            );
                                                            v___x_3106_ = l_Std_Format_defWidth;
                                                            v___x_3107_ = l_Std_Format_pretty(
                                                                v___x_3105_,
                                                                v___x_3106_,
                                                                v___x_3100_,
                                                                v___x_3100_,
                                                            );
                                                            v___x_3108_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3107_, v_a_2497_);
                                                            crate::leanh::lean_dec_ref(v___x_3107_);
                                                            return v___x_3108_;
                                                        } else {
                                                            crate::leanh::lean_dec(v_stx_2495_);
                                                            v___x_3109_ =
                                                                l_Lean_TSyntax_getString(v_s_3101_);
                                                            crate::leanh::lean_dec(v_s_3101_);
                                                            v___x_3110_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3109_, v_a_2497_);
                                                            crate::leanh::lean_dec_ref(v___x_3109_);
                                                            return v___x_3110_;
                                                        }
                                                    }
                                                } else {
                                                    v___x_3111_ =
                                                        crate::leanh::lean_unsigned_to_nat(0);
                                                    v___x_3112_ = l_Lean_Syntax_getArg(
                                                        v_stx_2495_,
                                                        v___x_3111_,
                                                    );
                                                    crate::leanh::lean_dec(v_stx_2495_);
                                                    v_stx_2495_ = v___x_3112_;
                                                    state = 0;
                                                    continue;
                                                }
                                            } else {
                                                v___x_3114_ = crate::leanh::lean_unsigned_to_nat(1);
                                                v___x_3115_ =
                                                    l_Lean_Syntax_getArg(v_stx_2495_, v___x_3114_);
                                                v___x_3116_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70;
                                                crate::leanh::lean_inc(v___x_3115_);
                                                v___x_3117_ = l_Lean_Syntax_isOfKind(
                                                    v___x_3115_,
                                                    v___x_3116_,
                                                );
                                                if v___x_3117_ == 0 {
                                                    crate::leanh::lean_dec(v___x_3115_);
                                                    v___x_3118_ = crate::leanh::lean_box(0);
                                                    v___x_3119_ = l_Lean_Syntax_formatStx(
                                                        v_stx_2495_,
                                                        v___x_3118_,
                                                        v___x_3117_,
                                                    );
                                                    v___x_3120_ = l_Std_Format_defWidth;
                                                    v___x_3121_ =
                                                        crate::leanh::lean_unsigned_to_nat(0);
                                                    v___x_3122_ = l_Std_Format_pretty(
                                                        v___x_3119_,
                                                        v___x_3120_,
                                                        v___x_3121_,
                                                        v___x_3121_,
                                                    );
                                                    v___x_3123_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3122_, v_a_2497_);
                                                    crate::leanh::lean_dec_ref(v___x_3122_);
                                                    return v___x_3123_;
                                                } else {
                                                    v___x_3124_ =
                                                        crate::leanh::lean_unsigned_to_nat(0);
                                                    v_tk_3125_ = l_Lean_Syntax_getArg(
                                                        v_stx_2495_,
                                                        v___x_3124_,
                                                    );
                                                    crate::leanh::lean_dec(v_stx_2495_);
                                                    v___x_3126_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk_3125_);
                                                    v___x_3127_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3126_, v_a_2497_);
                                                    crate::leanh::lean_dec_ref(v___x_3126_);
                                                    v_snd_3128_ =
                                                        crate::leanh::lean_ctor_get(v___x_3127_, 1);
                                                    crate::leanh::lean_inc(v_snd_3128_);
                                                    crate::leanh::lean_dec_ref(v___x_3127_);
                                                    v___x_3129_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_3115_);
                                                    v___x_3130_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3129_, v_snd_3128_);
                                                    crate::leanh::lean_dec_ref(v___x_3129_);
                                                    return v___x_3130_;
                                                }
                                            }
                                        } else {
                                            v___x_3131_ = crate::leanh::lean_unsigned_to_nat(1);
                                            v___x_3132_ =
                                                l_Lean_Syntax_getArg(v_stx_2495_, v___x_3131_);
                                            v___x_3133_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70;
                                            crate::leanh::lean_inc(v___x_3132_);
                                            v___x_3134_ =
                                                l_Lean_Syntax_isOfKind(v___x_3132_, v___x_3133_);
                                            if v___x_3134_ == 0 {
                                                crate::leanh::lean_dec(v___x_3132_);
                                                v___x_3135_ = crate::leanh::lean_box(0);
                                                v___x_3136_ = l_Lean_Syntax_formatStx(
                                                    v_stx_2495_,
                                                    v___x_3135_,
                                                    v___x_3134_,
                                                );
                                                v___x_3137_ = l_Std_Format_defWidth;
                                                v___x_3138_ = crate::leanh::lean_unsigned_to_nat(0);
                                                v___x_3139_ = l_Std_Format_pretty(
                                                    v___x_3136_,
                                                    v___x_3137_,
                                                    v___x_3138_,
                                                    v___x_3138_,
                                                );
                                                v___x_3140_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3139_, v_a_2497_);
                                                crate::leanh::lean_dec_ref(v___x_3139_);
                                                return v___x_3140_;
                                            } else {
                                                v___x_3141_ = crate::leanh::lean_unsigned_to_nat(0);
                                                v_tk_3142_ =
                                                    l_Lean_Syntax_getArg(v_stx_2495_, v___x_3141_);
                                                crate::leanh::lean_dec(v_stx_2495_);
                                                v___x_3143_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk_3142_);
                                                v___x_3144_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3143_, v_a_2497_);
                                                crate::leanh::lean_dec_ref(v___x_3143_);
                                                v_snd_3145_ =
                                                    crate::leanh::lean_ctor_get(v___x_3144_, 1);
                                                crate::leanh::lean_inc(v_snd_3145_);
                                                crate::leanh::lean_dec_ref(v___x_3144_);
                                                v___x_3146_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_3132_);
                                                v___x_3147_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3146_, v_snd_3145_);
                                                crate::leanh::lean_dec_ref(v___x_3146_);
                                                return v___x_3147_;
                                            }
                                        }
                                    } else {
                                        v___x_3148_ = crate::leanh::lean_unsigned_to_nat(0);
                                        v___x_3149_ =
                                            l_Lean_Syntax_getArg(v_stx_2495_, v___x_3148_);
                                        v___x_3150_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70;
                                        crate::leanh::lean_inc(v___x_3149_);
                                        v___x_3151_ =
                                            l_Lean_Syntax_isOfKind(v___x_3149_, v___x_3150_);
                                        if v___x_3151_ == 0 {
                                            crate::leanh::lean_dec(v___x_3149_);
                                            v___x_3152_ = crate::leanh::lean_box(0);
                                            v___x_3153_ = l_Lean_Syntax_formatStx(
                                                v_stx_2495_,
                                                v___x_3152_,
                                                v___x_3151_,
                                            );
                                            v___x_3154_ = l_Std_Format_defWidth;
                                            v___x_3155_ = l_Std_Format_pretty(
                                                v___x_3153_,
                                                v___x_3154_,
                                                v___x_3148_,
                                                v___x_3148_,
                                            );
                                            v___x_3156_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3155_, v_a_2497_);
                                            crate::leanh::lean_dec_ref(v___x_3155_);
                                            return v___x_3156_;
                                        } else {
                                            v___x_3157_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__71;
                                            v___x_3158_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3157_, v_a_2497_);
                                            v_snd_3159_ =
                                                crate::leanh::lean_ctor_get(v___x_3158_, 1);
                                            crate::leanh::lean_inc(v_snd_3159_);
                                            crate::leanh::lean_dec_ref(v___x_3158_);
                                            v___x_3160_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_3149_);
                                            v___x_3161_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3160_, v_snd_3159_);
                                            crate::leanh::lean_dec_ref(v___x_3160_);
                                            v_snd_3162_ =
                                                crate::leanh::lean_ctor_get(v___x_3161_, 1);
                                            crate::leanh::lean_inc(v_snd_3162_);
                                            crate::leanh::lean_dec_ref(v___x_3161_);
                                            v___x_3163_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__72;
                                            v___x_3164_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3163_, v_snd_3162_);
                                            v_snd_3165_ =
                                                crate::leanh::lean_ctor_get(v___x_3164_, 1);
                                            crate::leanh::lean_inc(v_snd_3165_);
                                            crate::leanh::lean_dec_ref(v___x_3164_);
                                            v___x_3166_ = crate::leanh::lean_unsigned_to_nat(2);
                                            v___x_3167_ =
                                                l_Lean_Syntax_getArg(v_stx_2495_, v___x_3166_);
                                            crate::leanh::lean_dec(v_stx_2495_);
                                            v___x_3168_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v___x_3167_, v_a_2496_, v_snd_3165_);
                                            v_snd_3169_ =
                                                crate::leanh::lean_ctor_get(v___x_3168_, 1);
                                            crate::leanh::lean_inc(v_snd_3169_);
                                            crate::leanh::lean_dec_ref(v___x_3168_);
                                            v___x_3170_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__73;
                                            v___x_3171_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3170_, v_snd_3169_);
                                            return v___x_3171_;
                                        }
                                    }
                                } else {
                                    v___x_3172_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__71;
                                    v___x_3173_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3172_, v_a_2497_);
                                    v_snd_3174_ = crate::leanh::lean_ctor_get(v___x_3173_, 1);
                                    crate::leanh::lean_inc(v_snd_3174_);
                                    crate::leanh::lean_dec_ref(v___x_3173_);
                                    v___x_3175_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_3176_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_3175_);
                                    v___x_3177_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_3176_);
                                    v___x_3178_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3177_, v_snd_3174_);
                                    crate::leanh::lean_dec_ref(v___x_3177_);
                                    v_snd_3179_ = crate::leanh::lean_ctor_get(v___x_3178_, 1);
                                    crate::leanh::lean_inc(v_snd_3179_);
                                    crate::leanh::lean_dec_ref(v___x_3178_);
                                    v___x_3180_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__72;
                                    v___x_3181_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3180_, v_snd_3179_);
                                    v_snd_3182_ = crate::leanh::lean_ctor_get(v___x_3181_, 1);
                                    crate::leanh::lean_inc(v_snd_3182_);
                                    crate::leanh::lean_dec_ref(v___x_3181_);
                                    v___x_3183_ = crate::leanh::lean_unsigned_to_nat(3);
                                    v___x_3184_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_3183_);
                                    crate::leanh::lean_dec(v_stx_2495_);
                                    v___x_3185_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v___x_3184_, v_a_2496_, v_snd_3182_);
                                    v_snd_3186_ = crate::leanh::lean_ctor_get(v___x_3185_, 1);
                                    crate::leanh::lean_inc(v_snd_3186_);
                                    crate::leanh::lean_dec_ref(v___x_3185_);
                                    v___x_3187_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__73;
                                    v___x_3188_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3187_, v_snd_3186_);
                                    return v___x_3188_;
                                }
                            } else {
                                v___x_3189_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_3190_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_3189_);
                                v___x_3191_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70;
                                crate::leanh::lean_inc(v___x_3190_);
                                v___x_3192_ = l_Lean_Syntax_isOfKind(v___x_3190_, v___x_3191_);
                                if v___x_3192_ == 0 {
                                    crate::leanh::lean_dec(v___x_3190_);
                                    v___x_3193_ = crate::leanh::lean_box(0);
                                    v___x_3194_ = l_Lean_Syntax_formatStx(
                                        v_stx_2495_,
                                        v___x_3193_,
                                        v___x_3192_,
                                    );
                                    v___x_3195_ = l_Std_Format_defWidth;
                                    v___x_3196_ = l_Std_Format_pretty(
                                        v___x_3194_,
                                        v___x_3195_,
                                        v___x_3189_,
                                        v___x_3189_,
                                    );
                                    v___x_3197_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3196_, v_a_2497_);
                                    crate::leanh::lean_dec_ref(v___x_3196_);
                                    return v___x_3197_;
                                } else {
                                    crate::leanh::lean_dec(v_stx_2495_);
                                    v___x_3198_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_3190_);
                                    v___x_3199_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3198_, v_a_2497_);
                                    crate::leanh::lean_dec_ref(v___x_3198_);
                                    return v___x_3199_;
                                }
                            }
                        } else {
                            v___x_3200_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_3201_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_3200_);
                            v___x_3202_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__75;
                            crate::leanh::lean_inc(v___x_3201_);
                            v___x_3203_ = l_Lean_Syntax_isOfKind(v___x_3201_, v___x_3202_);
                            if v___x_3203_ == 0 {
                                crate::leanh::lean_dec(v___x_3201_);
                                v___x_3204_ = crate::leanh::lean_box(0);
                                v___x_3205_ =
                                    l_Lean_Syntax_formatStx(v_stx_2495_, v___x_3204_, v___x_3203_);
                                v___x_3206_ = l_Std_Format_defWidth;
                                v___x_3207_ = l_Std_Format_pretty(
                                    v___x_3205_,
                                    v___x_3206_,
                                    v___x_3200_,
                                    v___x_3200_,
                                );
                                v___x_3208_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3207_, v_a_2497_);
                                crate::leanh::lean_dec_ref(v___x_3207_);
                                return v___x_3208_;
                            } else {
                                crate::leanh::lean_dec(v_stx_2495_);
                                v___x_3209_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_3201_);
                                v___x_3210_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3209_, v_a_2497_);
                                crate::leanh::lean_dec_ref(v___x_3209_);
                                return v___x_3210_;
                            }
                        }
                    } else {
                        v___x_3211_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_3212_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_3211_);
                        v___x_3213_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__68;
                        crate::leanh::lean_inc(v___x_3212_);
                        v___x_3214_ = l_Lean_Syntax_isOfKind(v___x_3212_, v___x_3213_);
                        if v___x_3214_ == 0 {
                            crate::leanh::lean_dec(v___x_3212_);
                            v___x_3215_ = crate::leanh::lean_box(0);
                            v___x_3216_ =
                                l_Lean_Syntax_formatStx(v_stx_2495_, v___x_3215_, v___x_3214_);
                            v___x_3217_ = l_Std_Format_defWidth;
                            v___x_3218_ = l_Std_Format_pretty(
                                v___x_3216_,
                                v___x_3217_,
                                v___x_3211_,
                                v___x_3211_,
                            );
                            v___x_3219_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3218_, v_a_2497_);
                            crate::leanh::lean_dec_ref(v___x_3218_);
                            return v___x_3219_;
                        } else {
                            crate::leanh::lean_dec(v_stx_2495_);
                            v___x_3220_ =
                                l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(
                                    v___x_3212_,
                                );
                            v___x_3221_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3220_, v_a_2497_);
                            crate::leanh::lean_dec_ref(v___x_3220_);
                            return v___x_3221_;
                        }
                    }
                } else {
                    v___x_3222_ = l_Lean_Syntax_getArgs(v_stx_2495_);
                    crate::leanh::lean_dec(v_stx_2495_);
                    v___x_3223_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3224_ = lean_array_get_size(v___x_3222_);
                    v___x_3225_ = crate::leanh::lean_box(0);
                    v___x_3226_ = lean_nat_dec_lt(v___x_3223_, v___x_3224_);
                    if v___x_3226_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_3222_);
                        v___x_3227_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3227_, 0, v___x_3225_);
                        crate::leanh::lean_ctor_set(v___x_3227_, 1, v_a_2497_);
                        return v___x_3227_;
                    } else {
                        v___x_3228_ = lean_nat_dec_le(v___x_3224_, v___x_3224_);
                        if v___x_3228_ == 0 {
                            if v___x_3226_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_3222_);
                                v___x_3229_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3229_, 0, v___x_3225_);
                                crate::leanh::lean_ctor_set(v___x_3229_, 1, v_a_2497_);
                                return v___x_3229_;
                            } else {
                                v___x_3230_ = 0usize;
                                v___x_3231_ = lean_usize_of_nat(v___x_3224_);
                                v___x_3232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_3222_, v___x_3230_, v___x_3231_, v___x_3225_, v_a_2496_, v_a_2497_);
                                crate::leanh::lean_dec_ref(v___x_3222_);
                                return v___x_3232_;
                            }
                        } else {
                            v___x_3233_ = 0usize;
                            v___x_3234_ = lean_usize_of_nat(v___x_3224_);
                            v___x_3235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_3222_, v___x_3233_, v___x_3234_, v___x_3225_, v_a_2496_, v_a_2497_);
                            crate::leanh::lean_dec_ref(v___x_3222_);
                            return v___x_3235_;
                        }
                    }
                }
            }
            1 => {
                v___x_2500_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0;
                v___x_2501_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2500_, v_snd_2499_);
                return v___x_2501_;
            }
            2 => {
                v_snd_2504_ = crate::leanh::lean_ctor_get(v___y_2503_, 1);
                crate::leanh::lean_inc(v_snd_2504_);
                crate::leanh::lean_dec_ref(v___y_2503_);
                v_snd_2499_ = v_snd_2504_;
                state = 1;
                continue;
            }
            3 => {
                v_snd_2507_ = crate::leanh::lean_ctor_get(v___y_2506_, 1);
                crate::leanh::lean_inc(v_snd_2507_);
                crate::leanh::lean_dec_ref(v___y_2506_);
                v___x_2508_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2507_);
                return v___x_2508_;
            }
            4 => {
                v_snd_2511_ = crate::leanh::lean_ctor_get(v___y_2510_, 1);
                crate::leanh::lean_inc(v_snd_2511_);
                crate::leanh::lean_dec_ref(v___y_2510_);
                v___x_2512_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2511_);
                return v___x_2512_;
            }
            5 => {
                v_snd_2515_ = crate::leanh::lean_ctor_get(v___y_2514_, 1);
                crate::leanh::lean_inc(v_snd_2515_);
                crate::leanh::lean_dec_ref(v___y_2514_);
                v___x_2516_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2515_);
                return v___x_2516_;
            }
            6 => {
                v_snd_2519_ = crate::leanh::lean_ctor_get(v___y_2518_, 1);
                crate::leanh::lean_inc(v_snd_2519_);
                crate::leanh::lean_dec_ref(v___y_2518_);
                v___x_2520_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2519_);
                return v___x_2520_;
            }
            7 => {
                v___x_2642_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
                crate::leanh::lean_inc(v_a_2496_);
                v___x_2643_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(v_a_2496_, v___x_2642_);
                v___x_2644_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2643_, v_snd_2641_);
                crate::leanh::lean_dec_ref(v___x_2643_);
                v_snd_2645_ = crate::leanh::lean_ctor_get(v___x_2644_, 1);
                crate::leanh::lean_inc(v_snd_2645_);
                crate::leanh::lean_dec_ref(v___x_2644_);
                v___x_2646_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_2639_);
                v___x_2647_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2646_, v_snd_2645_);
                crate::leanh::lean_dec_ref(v___x_2646_);
                v_snd_2648_ = crate::leanh::lean_ctor_get(v___x_2647_, 1);
                crate::leanh::lean_inc(v_snd_2648_);
                crate::leanh::lean_dec_ref(v___x_2647_);
                v___x_2649_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2648_);
                return v___x_2649_;
            }
            8 => {
                v_snd_2652_ = crate::leanh::lean_ctor_get(v___y_2651_, 1);
                crate::leanh::lean_inc(v_snd_2652_);
                crate::leanh::lean_dec_ref(v___y_2651_);
                v_snd_2641_ = v_snd_2652_;
                state = 7;
                continue;
            }
            9 => {
                v___x_2698_ = lean_string_utf8_byte_size(v___y_2697_);
                crate::leanh::lean_inc_ref(v___y_2697_);
                v___x_2699_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2699_, 0, v___y_2697_);
                crate::leanh::lean_ctor_set(v___x_2699_, 1, v___x_2673_);
                crate::leanh::lean_ctor_set(v___x_2699_, 2, v___x_2698_);
                v___x_2700_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v___x_2699_);
                v___x_2701_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__63;
                v___x_2702_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg(v_a_2496_, v___y_2697_, v___x_2699_, v___x_2698_, v___x_2700_, v___x_2701_);
                crate::leanh::lean_dec_ref_known(v___x_2699_, 3);
                crate::leanh::lean_dec_ref(v___y_2697_);
                v___x_2703_ = lean_array_to_list(v___x_2702_);
                v___x_2704_ = l_String_intercalate(v___x_2689_, v___x_2703_);
                v___x_2705_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2704_, v_snd_2691_);
                crate::leanh::lean_dec_ref(v___x_2704_);
                v_snd_2706_ = crate::leanh::lean_ctor_get(v___x_2705_, 1);
                crate::leanh::lean_inc(v_snd_2706_);
                crate::leanh::lean_dec_ref(v___x_2705_);
                v___x_2707_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
                crate::leanh::lean_inc(v_a_2496_);
                v___x_2708_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(v_a_2496_, v___x_2707_);
                v___x_2709_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2708_, v_snd_2706_);
                crate::leanh::lean_dec_ref(v___x_2708_);
                v_snd_2710_ = crate::leanh::lean_ctor_get(v___x_2709_, 1);
                crate::leanh::lean_inc(v_snd_2710_);
                crate::leanh::lean_dec_ref(v___x_2709_);
                v___x_2711_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_2695_);
                v___x_2712_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2711_, v_snd_2710_);
                crate::leanh::lean_dec_ref(v___x_2711_);
                v_snd_2713_ = crate::leanh::lean_ctor_get(v___x_2712_, 1);
                crate::leanh::lean_inc(v_snd_2713_);
                crate::leanh::lean_dec_ref(v___x_2712_);
                v___x_2714_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2713_);
                return v___x_2714_;
            }
            10 => {
                v___x_2827_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_2826_, v_snd_2820_);
                crate::leanh::lean_dec_ref(v___y_2826_);
                v_snd_2828_ = crate::leanh::lean_ctor_get(v___x_2827_, 1);
                crate::leanh::lean_inc(v_snd_2828_);
                crate::leanh::lean_dec_ref(v___x_2827_);
                v___x_2829_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_2824_);
                v___x_2830_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2829_, v_snd_2828_);
                crate::leanh::lean_dec_ref(v___x_2829_);
                return v___x_2830_;
            }
            11 => {
                v___x_2846_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_2845_, v_snd_2839_);
                crate::leanh::lean_dec_ref(v___y_2845_);
                v_snd_2847_ = crate::leanh::lean_ctor_get(v___x_2846_, 1);
                crate::leanh::lean_inc(v_snd_2847_);
                crate::leanh::lean_dec_ref(v___x_2846_);
                v___x_2848_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_2843_);
                v___x_2849_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2848_, v_snd_2847_);
                crate::leanh::lean_dec_ref(v___x_2848_);
                return v___x_2849_;
            }
            12 => {
                v___x_2877_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_2876_, v_snd_2871_);
                crate::leanh::lean_dec_ref(v___y_2876_);
                v_snd_2878_ = crate::leanh::lean_ctor_get(v___x_2877_, 1);
                crate::leanh::lean_inc(v_snd_2878_);
                crate::leanh::lean_dec_ref(v___x_2877_);
                v___x_2879_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk3_2874_);
                v___x_2880_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2879_, v_snd_2878_);
                crate::leanh::lean_dec_ref(v___x_2879_);
                return v___x_2880_;
            }
            13 => {
                v___x_2908_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_2907_, v_snd_2902_);
                crate::leanh::lean_dec_ref(v___y_2907_);
                v_snd_2909_ = crate::leanh::lean_ctor_get(v___x_2908_, 1);
                crate::leanh::lean_inc(v_snd_2909_);
                crate::leanh::lean_dec_ref(v___x_2908_);
                v___x_2910_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk3_2905_);
                v___x_2911_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2910_, v_snd_2909_);
                crate::leanh::lean_dec_ref(v___x_2910_);
                return v___x_2911_;
            }
            14 => {
                v___x_2935_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_2934_, v_snd_2928_);
                crate::leanh::lean_dec_ref(v___y_2934_);
                v_snd_2936_ = crate::leanh::lean_ctor_get(v___x_2935_, 1);
                crate::leanh::lean_inc(v_snd_2936_);
                crate::leanh::lean_dec_ref(v___x_2935_);
                v___x_2937_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_2932_);
                v___x_2938_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2937_, v_snd_2936_);
                crate::leanh::lean_dec_ref(v___x_2937_);
                return v___x_2938_;
            }
            15 => {
                v___x_2954_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_2953_, v_snd_2947_);
                crate::leanh::lean_dec_ref(v___y_2953_);
                v_snd_2955_ = crate::leanh::lean_ctor_get(v___x_2954_, 1);
                crate::leanh::lean_inc(v_snd_2955_);
                crate::leanh::lean_dec_ref(v___x_2954_);
                v___x_2956_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_2951_);
                v___x_2957_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2956_, v_snd_2955_);
                crate::leanh::lean_dec_ref(v___x_2956_);
                return v___x_2957_;
            }
            16 => {
                v___x_3005_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_3004_, v_snd_2996_);
                crate::leanh::lean_dec_ref(v___y_3004_);
                v_snd_3006_ = crate::leanh::lean_ctor_get(v___x_3005_, 1);
                crate::leanh::lean_inc(v_snd_3006_);
                crate::leanh::lean_dec_ref(v___x_3005_);
                v___x_3007_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_3000_);
                v___x_3008_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3007_, v_snd_3006_);
                crate::leanh::lean_dec_ref(v___x_3007_);
                v_snd_3009_ = crate::leanh::lean_ctor_get(v___x_3008_, 1);
                crate::leanh::lean_inc(v_snd_3009_);
                crate::leanh::lean_dec_ref(v___x_3008_);
                v_stx_2495_ = v___x_3002_;
                v_a_2497_ = v_snd_3009_;
                state = 0;
                continue;
            }
            17 => {
                v___x_3028_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_3023_);
                v___x_3029_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3028_, v_snd_3027_);
                crate::leanh::lean_dec_ref(v___x_3028_);
                v_snd_3030_ = crate::leanh::lean_ctor_get(v___x_3029_, 1);
                crate::leanh::lean_inc(v_snd_3030_);
                crate::leanh::lean_dec_ref(v___x_3029_);
                v_stx_2495_ = v___x_3025_;
                v_a_2497_ = v_snd_3030_;
                state = 0;
                continue;
            }
            18 => {
                v_snd_3034_ = crate::leanh::lean_ctor_get(v___y_3033_, 1);
                crate::leanh::lean_inc(v_snd_3034_);
                crate::leanh::lean_dec_ref(v___y_3033_);
                v_snd_3027_ = v_snd_3034_;
                state = 17;
                continue;
            }
            19 => {
                v___x_3057_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_3054_);
                v___x_3058_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3057_, v_snd_3056_);
                crate::leanh::lean_dec_ref(v___x_3057_);
                return v___x_3058_;
            }
            20 => {
                v_snd_3061_ = crate::leanh::lean_ctor_get(v___y_3060_, 1);
                crate::leanh::lean_inc(v_snd_3061_);
                crate::leanh::lean_dec_ref(v___y_3060_);
                v_snd_3056_ = v_snd_3061_;
                state = 19;
                continue;
            }
            21 => {
                v___x_3084_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_3081_);
                v___x_3085_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3084_, v_snd_3083_);
                crate::leanh::lean_dec_ref(v___x_3084_);
                return v___x_3085_;
            }
            22 => {
                v_snd_3088_ = crate::leanh::lean_ctor_get(v___y_3087_, 1);
                crate::leanh::lean_inc(v_snd_3088_);
                crate::leanh::lean_dec_ref(v___y_3087_);
                v_snd_3083_ = v_snd_3088_;
                state = 21;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(
    mut v_as_3236_: *mut crate::leanh::LeanObject,
    mut v_i_3237_: usize,
    mut v_stop_3238_: usize,
    mut v_b_3239_: *mut crate::leanh::LeanObject,
    mut v___y_3240_: *mut crate::leanh::LeanObject,
    mut v___y_3241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3242_: u8 = 0;
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: usize = 0;
    let mut v___x_3248_: usize = 0;
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3242_ = lean_usize_dec_eq(v_i_3237_, v_stop_3238_);
                if v___x_3242_ == 0 {
                    v___x_3243_ = lean_array_uget_borrowed(v_as_3236_, v_i_3237_);
                    crate::leanh::lean_inc(v___x_3243_);
                    v___x_3244_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v___x_3243_, v___y_3240_, v___y_3241_);
                    v_fst_3245_ = crate::leanh::lean_ctor_get(v___x_3244_, 0);
                    crate::leanh::lean_inc(v_fst_3245_);
                    v_snd_3246_ = crate::leanh::lean_ctor_get(v___x_3244_, 1);
                    crate::leanh::lean_inc(v_snd_3246_);
                    crate::leanh::lean_dec_ref(v___x_3244_);
                    v___x_3247_ = 1usize;
                    v___x_3248_ = lean_usize_add(v_i_3237_, v___x_3247_);
                    v_i_3237_ = v___x_3248_;
                    v_b_3239_ = v_fst_3245_;
                    v___y_3241_ = v_snd_3246_;
                    state = 0;
                    continue;
                } else {
                    v___x_3250_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3250_, 0, v_b_3239_);
                    crate::leanh::lean_ctor_set(v___x_3250_, 1, v___y_3241_);
                    return v___x_3250_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2___boxed(
    mut v_as_3251_: *mut crate::leanh::LeanObject,
    mut v_i_3252_: *mut crate::leanh::LeanObject,
    mut v_stop_3253_: *mut crate::leanh::LeanObject,
    mut v_b_3254_: *mut crate::leanh::LeanObject,
    mut v___y_3255_: *mut crate::leanh::LeanObject,
    mut v___y_3256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3257_: usize = 0;
    let mut v_stop_boxed_3258_: usize = 0;
    let mut v_res_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3257_ = crate::leanh::lean_unbox_usize(v_i_3252_);
    crate::leanh::lean_dec(v_i_3252_);
    v_stop_boxed_3258_ = crate::leanh::lean_unbox_usize(v_stop_3253_);
    crate::leanh::lean_dec(v_stop_3253_);
    v_res_3259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_as_3251_, v_i_boxed_3257_, v_stop_boxed_3258_, v_b_3254_, v___y_3255_, v___y_3256_);
    crate::leanh::lean_dec(v___y_3255_);
    crate::leanh::lean_dec_ref(v_as_3251_);
    return v_res_3259_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___boxed(
    mut v_as_3260_: *mut crate::leanh::LeanObject,
    mut v_sz_3261_: *mut crate::leanh::LeanObject,
    mut v_i_3262_: *mut crate::leanh::LeanObject,
    mut v_b_3263_: *mut crate::leanh::LeanObject,
    mut v___y_3264_: *mut crate::leanh::LeanObject,
    mut v___y_3265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3266_: usize = 0;
    let mut v_i_boxed_3267_: usize = 0;
    let mut v_res_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3266_ = crate::leanh::lean_unbox_usize(v_sz_3261_);
    crate::leanh::lean_dec(v_sz_3261_);
    v_i_boxed_3267_ = crate::leanh::lean_unbox_usize(v_i_3262_);
    crate::leanh::lean_dec(v_i_3262_);
    v_res_3268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(v_as_3260_, v_sz_boxed_3266_, v_i_boxed_3267_, v_b_3263_, v___y_3264_, v___y_3265_);
    crate::leanh::lean_dec(v___y_3264_);
    crate::leanh::lean_dec_ref(v_as_3260_);
    return v_res_3268_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__1___boxed(
    mut v_as_3269_: *mut crate::leanh::LeanObject,
    mut v_sz_3270_: *mut crate::leanh::LeanObject,
    mut v_i_3271_: *mut crate::leanh::LeanObject,
    mut v_b_3272_: *mut crate::leanh::LeanObject,
    mut v___y_3273_: *mut crate::leanh::LeanObject,
    mut v___y_3274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3275_: usize = 0;
    let mut v_i_boxed_3276_: usize = 0;
    let mut v_res_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3275_ = crate::leanh::lean_unbox_usize(v_sz_3270_);
    crate::leanh::lean_dec(v_sz_3270_);
    v_i_boxed_3276_ = crate::leanh::lean_unbox_usize(v_i_3271_);
    crate::leanh::lean_dec(v_i_3271_);
    v_res_3277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__1(v_as_3269_, v_sz_boxed_3275_, v_i_boxed_3276_, v_b_3272_, v___y_3273_, v___y_3274_);
    crate::leanh::lean_dec(v___y_3273_);
    crate::leanh::lean_dec_ref(v_as_3269_);
    return v_res_3277_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___boxed(
    mut v_as_3278_: *mut crate::leanh::LeanObject,
    mut v_i_3279_: *mut crate::leanh::LeanObject,
    mut v_stop_3280_: *mut crate::leanh::LeanObject,
    mut v_b_3281_: *mut crate::leanh::LeanObject,
    mut v___y_3282_: *mut crate::leanh::LeanObject,
    mut v___y_3283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3284_: usize = 0;
    let mut v_stop_boxed_3285_: usize = 0;
    let mut v_res_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3284_ = crate::leanh::lean_unbox_usize(v_i_3279_);
    crate::leanh::lean_dec(v_i_3279_);
    v_stop_boxed_3285_ = crate::leanh::lean_unbox_usize(v_stop_3280_);
    crate::leanh::lean_dec(v_stop_3280_);
    v_res_3286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v_as_3278_, v_i_boxed_3284_, v_stop_boxed_3285_, v_b_3281_, v___y_3282_, v___y_3283_);
    crate::leanh::lean_dec(v___y_3282_);
    crate::leanh::lean_dec_ref(v_as_3278_);
    return v_res_3286_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___boxed(
    mut v_as_3287_: *mut crate::leanh::LeanObject,
    mut v_sz_3288_: *mut crate::leanh::LeanObject,
    mut v_i_3289_: *mut crate::leanh::LeanObject,
    mut v_b_3290_: *mut crate::leanh::LeanObject,
    mut v___y_3291_: *mut crate::leanh::LeanObject,
    mut v___y_3292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3293_: usize = 0;
    let mut v_i_boxed_3294_: usize = 0;
    let mut v_res_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3293_ = crate::leanh::lean_unbox_usize(v_sz_3288_);
    crate::leanh::lean_dec(v_sz_3288_);
    v_i_boxed_3294_ = crate::leanh::lean_unbox_usize(v_i_3289_);
    crate::leanh::lean_dec(v_i_3289_);
    v_res_3295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(v_as_3287_, v_sz_boxed_3293_, v_i_boxed_3294_, v_b_3290_, v___y_3291_, v___y_3292_);
    crate::leanh::lean_dec(v___y_3291_);
    crate::leanh::lean_dec_ref(v_as_3287_);
    return v_res_3295_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___boxed(
    mut v_stx_3296_: *mut crate::leanh::LeanObject,
    mut v_a_3297_: *mut crate::leanh::LeanObject,
    mut v_a_3298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3299_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(
        v_stx_3296_,
        v_a_3297_,
        v_a_3298_,
    );
    crate::leanh::lean_dec(v_a_3297_);
    return v_res_3299_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(
    mut v_a_3300_: *mut crate::leanh::LeanObject,
    mut v___y_3301_: *mut crate::leanh::LeanObject,
    mut v___x_3302_: *mut crate::leanh::LeanObject,
    mut v___x_3303_: *mut crate::leanh::LeanObject,
    mut v_inst_3304_: *mut crate::leanh::LeanObject,
    mut v_R_3305_: *mut crate::leanh::LeanObject,
    mut v_a_3306_: *mut crate::leanh::LeanObject,
    mut v_b_3307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3308_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg(v_a_3300_, v___y_3301_, v___x_3302_, v___x_3303_, v_a_3306_, v_b_3307_);
    return v___x_3308_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___boxed(
    mut v_a_3309_: *mut crate::leanh::LeanObject,
    mut v___y_3310_: *mut crate::leanh::LeanObject,
    mut v___x_3311_: *mut crate::leanh::LeanObject,
    mut v___x_3312_: *mut crate::leanh::LeanObject,
    mut v_inst_3313_: *mut crate::leanh::LeanObject,
    mut v_R_3314_: *mut crate::leanh::LeanObject,
    mut v_a_3315_: *mut crate::leanh::LeanObject,
    mut v_b_3316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3317_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v_a_3309_, v___y_3310_, v___x_3311_, v___x_3312_, v_inst_3313_, v_R_3314_, v_a_3315_, v_b_3316_);
    crate::leanh::lean_dec_ref(v___x_3311_);
    crate::leanh::lean_dec_ref(v___y_3310_);
    crate::leanh::lean_dec(v_a_3309_);
    return v_res_3317_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___lam__0(
    mut v___y_3318_: *mut crate::leanh::LeanObject,
    mut v___y_3319_: *mut crate::leanh::LeanObject,
    mut v___y_3320_: *mut crate::leanh::LeanObject,
    mut v___y_3321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3323_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_3319_);
    if crate::leanh::lean_obj_tag(v___x_3323_) == 0 {
        let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_3323_, 1);
        v___x_3324_ = crate::leanh::lean_box(0);
        v___x_3325_ = l_Lean_PrettyPrinter_Formatter_visitAtom(
            v___x_3324_,
            v___y_3318_,
            v___y_3319_,
            v___y_3320_,
            v___y_3321_,
        );
        if crate::leanh::lean_obj_tag(v___x_3325_) == 0 {
            let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_3325_, 1);
            v___x_3326_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_3319_);
            if crate::leanh::lean_obj_tag(v___x_3326_) == 0 {
                let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref_known(v___x_3326_, 1);
                v___x_3327_ = l_Lean_Doc_Parser_metadataContents_formatter(
                    v___y_3318_,
                    v___y_3319_,
                    v___y_3320_,
                    v___y_3321_,
                );
                if crate::leanh::lean_obj_tag(v___x_3327_) == 0 {
                    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref_known(v___x_3327_, 1);
                    v___x_3328_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_3319_);
                    if crate::leanh::lean_obj_tag(v___x_3328_) == 0 {
                        let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec_ref_known(v___x_3328_, 1);
                        v___x_3329_ = l_Lean_PrettyPrinter_Formatter_visitAtom(
                            v___x_3324_,
                            v___y_3318_,
                            v___y_3319_,
                            v___y_3320_,
                            v___y_3321_,
                        );
                        return v___x_3329_;
                    } else {
                        return v___x_3328_;
                    }
                } else {
                    return v___x_3327_;
                }
            } else {
                return v___x_3326_;
            }
        } else {
            return v___x_3325_;
        }
    } else {
        return v___x_3323_;
    }
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___lam__0___boxed(
    mut v___y_3330_: *mut crate::leanh::LeanObject,
    mut v___y_3331_: *mut crate::leanh::LeanObject,
    mut v___y_3332_: *mut crate::leanh::LeanObject,
    mut v___y_3333_: *mut crate::leanh::LeanObject,
    mut v___y_3334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3335_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___lam__0(
        v___y_3330_,
        v___y_3331_,
        v___y_3332_,
        v___y_3333_,
    );
    crate::leanh::lean_dec(v___y_3333_);
    crate::leanh::lean_dec_ref(v___y_3332_);
    crate::leanh::lean_dec(v___y_3331_);
    crate::leanh::lean_dec_ref(v___y_3330_);
    return v_res_3335_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata(
    mut v_a_3337_: *mut crate::leanh::LeanObject,
    mut v_a_3338_: *mut crate::leanh::LeanObject,
    mut v_a_3339_: *mut crate::leanh::LeanObject,
    mut v_a_3340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3342_ =
        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___closed__0;
    v___x_3343_ = l_Lean_PrettyPrinter_Formatter_visitArgs(
        v___f_3342_,
        v_a_3337_,
        v_a_3338_,
        v_a_3339_,
        v_a_3340_,
    );
    return v___x_3343_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___boxed(
    mut v_a_3344_: *mut crate::leanh::LeanObject,
    mut v_a_3345_: *mut crate::leanh::LeanObject,
    mut v_a_3346_: *mut crate::leanh::LeanObject,
    mut v_a_3347_: *mut crate::leanh::LeanObject,
    mut v_a_3348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3349_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata(
        v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_,
    );
    crate::leanh::lean_dec(v_a_3347_);
    crate::leanh::lean_dec_ref(v_a_3346_);
    crate::leanh::lean_dec(v_a_3345_);
    crate::leanh::lean_dec_ref(v_a_3344_);
    return v_res_3349_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString(
    mut v_stx_3350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3351_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3352_ =
        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
    v___x_3353_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(
        v_stx_3350_,
        v___x_3351_,
        v___x_3352_,
    );
    v_snd_3354_ = crate::leanh::lean_ctor_get(v___x_3353_, 1);
    crate::leanh::lean_inc(v_snd_3354_);
    crate::leanh::lean_dec_ref(v___x_3353_);
    return v_snd_3354_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(
    mut v_range_3361_: *mut crate::leanh::LeanObject,
    mut v_b_3362_: *mut crate::leanh::LeanObject,
    mut v_i_3363_: *mut crate::leanh::LeanObject,
    mut v___y_3364_: *mut crate::leanh::LeanObject,
    mut v___y_3365_: *mut crate::leanh::LeanObject,
    mut v___y_3366_: *mut crate::leanh::LeanObject,
    mut v___y_3367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stop_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: u8 = 0;
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3377_: u8 = 0;
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: u8 = 0;
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3392_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_3369_ = crate::leanh::lean_ctor_get(v_range_3361_, 1);
                v_step_3370_ = crate::leanh::lean_ctor_get(v_range_3361_, 2);
                v___x_3371_ = lean_nat_dec_lt(v_i_3363_, v_stop_3369_);
                if v___x_3371_ == 0 {
                    crate::leanh::lean_dec(v_i_3363_);
                    v___x_3372_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3372_, 0, v_b_3362_);
                    return v___x_3372_;
                } else {
                    v___x_3373_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v___y_3365_);
                    v_a_3374_ = crate::leanh::lean_ctor_get(v___x_3373_, 0);
                    v_isSharedCheck_3392_ = (!crate::leanh::lean_is_exclusive(v___x_3373_)) as u8;
                    if v_isSharedCheck_3392_ == 0 {
                        v___x_3376_ = v___x_3373_;
                        v_isShared_3377_ = v_isSharedCheck_3392_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3374_);
                        crate::leanh::lean_dec(v___x_3373_);
                        v___x_3376_ = crate::leanh::lean_box(0);
                        v_isShared_3377_ = v_isSharedCheck_3392_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3378_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_a_3374_);
                v___x_3382_ = l_Lean_Syntax_getKind(v_a_3374_);
                v___x_3383_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1;
                v___x_3384_ = lean_name_eq(v___x_3382_, v___x_3383_);
                crate::leanh::lean_dec(v___x_3382_);
                if v___x_3384_ == 0 {
                    v___x_3385_ =
                        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString(
                            v_a_3374_,
                        );
                    if v_isShared_3377_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3376_, 3);
                        crate::leanh::lean_ctor_set(v___x_3376_, 0, v___x_3385_);
                        v___x_3387_ = v___x_3376_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3390_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3385_);
                        v___x_3387_ = v_reuseFailAlloc_3390_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3376_);
                    crate::leanh::lean_dec(v_a_3374_);
                    v___x_3391_ =
                        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata(
                            v___y_3364_,
                            v___y_3365_,
                            v___y_3366_,
                            v___y_3367_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_3391_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3391_, 1);
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_3363_);
                        return v___x_3391_;
                    }
                }
            }
            2 => {
                v___x_3380_ = lean_nat_add(v_i_3363_, v_step_3370_);
                crate::leanh::lean_dec(v_i_3363_);
                v_b_3362_ = v___x_3378_;
                v_i_3363_ = v___x_3380_;
                state = 0;
                continue;
            }
            3 => {
                v___x_3388_ =
                    l_Lean_PrettyPrinter_Formatter_push___redArg(v___x_3387_, v___y_3365_);
                if crate::leanh::lean_obj_tag(v___x_3388_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3388_, 1);
                    v___x_3389_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(v___y_3365_);
                    crate::leanh::lean_dec_ref(v___x_3389_);
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_i_3363_);
                    return v___x_3388_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___boxed(
    mut v_range_3393_: *mut crate::leanh::LeanObject,
    mut v_b_3394_: *mut crate::leanh::LeanObject,
    mut v_i_3395_: *mut crate::leanh::LeanObject,
    mut v___y_3396_: *mut crate::leanh::LeanObject,
    mut v___y_3397_: *mut crate::leanh::LeanObject,
    mut v___y_3398_: *mut crate::leanh::LeanObject,
    mut v___y_3399_: *mut crate::leanh::LeanObject,
    mut v___y_3400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3401_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v_range_3393_, v_b_3394_, v_i_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
    crate::leanh::lean_dec(v___y_3399_);
    crate::leanh::lean_dec_ref(v___y_3398_);
    crate::leanh::lean_dec(v___y_3397_);
    crate::leanh::lean_dec_ref(v___y_3396_);
    crate::leanh::lean_dec_ref(v_range_3393_);
    return v_res_3401_;
}
pub unsafe fn l_Lean_Doc_Parser_document_formatter___lam__0(
    mut v___x_3402_: *mut crate::leanh::LeanObject,
    mut v___x_3403_: *mut crate::leanh::LeanObject,
    mut v___x_3404_: *mut crate::leanh::LeanObject,
    mut v___y_3405_: *mut crate::leanh::LeanObject,
    mut v___y_3406_: *mut crate::leanh::LeanObject,
    mut v___y_3407_: *mut crate::leanh::LeanObject,
    mut v___y_3408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3413_: u8 = 0;
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3417_: u8 = 0;
    let mut v_unused_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3410_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v___x_3402_, v___x_3403_, v___x_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_);
                if crate::leanh::lean_obj_tag(v___x_3410_) == 0 {
                    v_isSharedCheck_3417_ = (!crate::leanh::lean_is_exclusive(v___x_3410_)) as u8;
                    if v_isSharedCheck_3417_ == 0 {
                        v_unused_3418_ = crate::leanh::lean_ctor_get(v___x_3410_, 0);
                        crate::leanh::lean_dec(v_unused_3418_);
                        v___x_3412_ = v___x_3410_;
                        v_isShared_3413_ = v_isSharedCheck_3417_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3410_);
                        v___x_3412_ = crate::leanh::lean_box(0);
                        v_isShared_3413_ = v_isSharedCheck_3417_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_3410_;
                }
            }
            1 => {
                if v_isShared_3413_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3412_, 0, v___x_3403_);
                    v___x_3415_ = v___x_3412_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3416_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3403_);
                    v___x_3415_ = v_reuseFailAlloc_3416_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3415_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_Parser_document_formatter___lam__0___boxed(
    mut v___x_3419_: *mut crate::leanh::LeanObject,
    mut v___x_3420_: *mut crate::leanh::LeanObject,
    mut v___x_3421_: *mut crate::leanh::LeanObject,
    mut v___y_3422_: *mut crate::leanh::LeanObject,
    mut v___y_3423_: *mut crate::leanh::LeanObject,
    mut v___y_3424_: *mut crate::leanh::LeanObject,
    mut v___y_3425_: *mut crate::leanh::LeanObject,
    mut v___y_3426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3427_ = l_Lean_Doc_Parser_document_formatter___lam__0(
        v___x_3419_,
        v___x_3420_,
        v___x_3421_,
        v___y_3422_,
        v___y_3423_,
        v___y_3424_,
        v___y_3425_,
    );
    crate::leanh::lean_dec(v___y_3425_);
    crate::leanh::lean_dec_ref(v___y_3424_);
    crate::leanh::lean_dec(v___y_3423_);
    crate::leanh::lean_dec_ref(v___y_3422_);
    crate::leanh::lean_dec_ref(v___x_3419_);
    return v_res_3427_;
}
pub unsafe fn l_Lean_Doc_Parser_document_formatter___lam__1(
    mut v___y_3428_: *mut crate::leanh::LeanObject,
    mut v___y_3429_: *mut crate::leanh::LeanObject,
    mut v___y_3430_: *mut crate::leanh::LeanObject,
    mut v___y_3431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3433_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v___y_3429_);
    v_a_3434_ = crate::leanh::lean_ctor_get(v___x_3433_, 0);
    crate::leanh::lean_inc(v_a_3434_);
    crate::leanh::lean_dec_ref(v___x_3433_);
    v___x_3435_ = l_Lean_Syntax_getArgs(v_a_3434_);
    crate::leanh::lean_dec(v_a_3434_);
    v_i_3436_ = lean_array_get_size(v___x_3435_);
    crate::leanh::lean_dec_ref(v___x_3435_);
    v___x_3437_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3438_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3439_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3439_, 0, v___x_3437_);
    crate::leanh::lean_ctor_set(v___x_3439_, 1, v_i_3436_);
    crate::leanh::lean_ctor_set(v___x_3439_, 2, v___x_3438_);
    v___x_3440_ = crate::leanh::lean_box(0);
    v___f_3441_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_Parser_document_formatter___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___f_3441_, 0, v___x_3439_);
    crate::leanh::lean_closure_set(v___f_3441_, 1, v___x_3440_);
    crate::leanh::lean_closure_set(v___f_3441_, 2, v___x_3437_);
    v___x_3442_ = l_Lean_PrettyPrinter_Formatter_visitArgs(
        v___f_3441_,
        v___y_3428_,
        v___y_3429_,
        v___y_3430_,
        v___y_3431_,
    );
    return v___x_3442_;
}
pub unsafe fn l_Lean_Doc_Parser_document_formatter___lam__1___boxed(
    mut v___y_3443_: *mut crate::leanh::LeanObject,
    mut v___y_3444_: *mut crate::leanh::LeanObject,
    mut v___y_3445_: *mut crate::leanh::LeanObject,
    mut v___y_3446_: *mut crate::leanh::LeanObject,
    mut v___y_3447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3448_ = l_Lean_Doc_Parser_document_formatter___lam__1(
        v___y_3443_,
        v___y_3444_,
        v___y_3445_,
        v___y_3446_,
    );
    crate::leanh::lean_dec(v___y_3446_);
    crate::leanh::lean_dec_ref(v___y_3445_);
    crate::leanh::lean_dec(v___y_3444_);
    crate::leanh::lean_dec_ref(v___y_3443_);
    return v_res_3448_;
}
pub unsafe fn l_Lean_Doc_Parser_document_formatter(
    mut v_a_3450_: *mut crate::leanh::LeanObject,
    mut v_a_3451_: *mut crate::leanh::LeanObject,
    mut v_a_3452_: *mut crate::leanh::LeanObject,
    mut v_a_3453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3455_ = l_Lean_Doc_Parser_document_formatter___closed__0;
    v___x_3456_ = l_Lean_PrettyPrinter_Formatter_concat(
        v___f_3455_,
        v_a_3450_,
        v_a_3451_,
        v_a_3452_,
        v_a_3453_,
    );
    return v___x_3456_;
}
pub unsafe fn l_Lean_Doc_Parser_document_formatter___boxed(
    mut v_a_3457_: *mut crate::leanh::LeanObject,
    mut v_a_3458_: *mut crate::leanh::LeanObject,
    mut v_a_3459_: *mut crate::leanh::LeanObject,
    mut v_a_3460_: *mut crate::leanh::LeanObject,
    mut v_a_3461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3462_ = l_Lean_Doc_Parser_document_formatter(v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
    crate::leanh::lean_dec(v_a_3460_);
    crate::leanh::lean_dec_ref(v_a_3459_);
    crate::leanh::lean_dec(v_a_3458_);
    crate::leanh::lean_dec_ref(v_a_3457_);
    return v_res_3462_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0(
    mut v_range_3463_: *mut crate::leanh::LeanObject,
    mut v_b_3464_: *mut crate::leanh::LeanObject,
    mut v_i_3465_: *mut crate::leanh::LeanObject,
    mut v_hs_3466_: *mut crate::leanh::LeanObject,
    mut v_hl_3467_: *mut crate::leanh::LeanObject,
    mut v___y_3468_: *mut crate::leanh::LeanObject,
    mut v___y_3469_: *mut crate::leanh::LeanObject,
    mut v___y_3470_: *mut crate::leanh::LeanObject,
    mut v___y_3471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3473_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v_range_3463_, v_b_3464_, v_i_3465_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
    return v___x_3473_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___boxed(
    mut v_range_3474_: *mut crate::leanh::LeanObject,
    mut v_b_3475_: *mut crate::leanh::LeanObject,
    mut v_i_3476_: *mut crate::leanh::LeanObject,
    mut v_hs_3477_: *mut crate::leanh::LeanObject,
    mut v_hl_3478_: *mut crate::leanh::LeanObject,
    mut v___y_3479_: *mut crate::leanh::LeanObject,
    mut v___y_3480_: *mut crate::leanh::LeanObject,
    mut v___y_3481_: *mut crate::leanh::LeanObject,
    mut v___y_3482_: *mut crate::leanh::LeanObject,
    mut v___y_3483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3484_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0(v_range_3474_, v_b_3475_, v_i_3476_, v_hs_3477_, v_hl_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
    crate::leanh::lean_dec(v___y_3482_);
    crate::leanh::lean_dec_ref(v___y_3481_);
    crate::leanh::lean_dec(v___y_3480_);
    crate::leanh::lean_dec_ref(v___y_3479_);
    crate::leanh::lean_dec_ref(v_range_3474_);
    return v_res_3484_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_DocString_Formatter(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_PrettyPrinter_Formatter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DocString_Parser(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_DocString_Formatter(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_DocString_Formatter(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_PrettyPrinter_Formatter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_DocString_Parser(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DocString_Formatter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_DocString_Formatter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_DocString_Formatter(builtin);
}
