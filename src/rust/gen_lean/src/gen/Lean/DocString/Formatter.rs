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
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString___closed__0_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [10, 10, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [97, 114, 103, 95, 115, 116, 114, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 121, 110, 116, 97, 120, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [68, 111, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3_value) as *mut leanh::LeanObject,16350384043721911836 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [97, 114, 103, 95, 110, 117, 109, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5_value) as *mut leanh::LeanObject,14487455678410716942 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 114, 103, 95, 105, 100, 101, 110, 116, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7_value) as *mut leanh::LeanObject,2451685894574911817 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [110, 97, 109, 101, 100, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9_value) as *mut leanh::LeanObject,7954595750846190064 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [110, 97, 109, 101, 100, 95, 110, 111, 95, 112, 97, 114, 101, 110, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11_value) as *mut leanh::LeanObject,1862588536603037236 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [102, 108, 97, 103, 95, 111, 110, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13_value) as *mut leanh::LeanObject,3891920175377473180 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__15_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [102, 108, 97, 103, 95, 111, 102, 102, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__15_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__15_value) as *mut leanh::LeanObject,16434802777007652893 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__17_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [97, 110, 111, 110, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__17_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__17_value) as *mut leanh::LeanObject,4061692882929131159 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__19_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 101, 120, 116, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__19_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__19_value) as *mut leanh::LeanObject,7633771195065472508 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__21_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [101, 109, 112, 104, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__21_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__21_value) as *mut leanh::LeanObject,17275792779021629260 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__23_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [98, 111, 108, 100, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__23_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__23_value) as *mut leanh::LeanObject,826132507934060761 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__25_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 105, 110, 107, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__25_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__25_value) as *mut leanh::LeanObject,5786183721214523521 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__27_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 109, 97, 103, 101, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__27_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__27_value) as *mut leanh::LeanObject,4431944511769375132 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__29_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [114, 111, 108, 101, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__29_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__29_value) as *mut leanh::LeanObject,8038157434449897304 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__31_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 100, 101, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__31_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__31_value) as *mut leanh::LeanObject,9119460824152039283 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__33_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [102, 111, 111, 116, 110, 111, 116, 101, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__33: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__33_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__33_value) as *mut leanh::LeanObject,8931910793042548687 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__35_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 105, 110, 101, 98, 114, 101, 97, 107, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__35: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__35_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__35_value) as *mut leanh::LeanObject,14934976377275135948 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__37_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 110, 108, 105, 110, 101, 95, 109, 97, 116, 104, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__37: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__37_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__37_value) as *mut leanh::LeanObject,13146676051664452135 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__39_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [100, 105, 115, 112, 108, 97, 121, 95, 109, 97, 116, 104, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__39: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__39_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__39_value) as *mut leanh::LeanObject,17625330591492572857 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__41_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [114, 101, 102, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__41: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__41_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__41_value) as *mut leanh::LeanObject,9592559646838605213 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__43_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [117, 114, 108, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__43: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__43_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__43_value) as *mut leanh::LeanObject,14879212058519956833 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__45_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [104, 101, 97, 100, 101, 114, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__45: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__45_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__45_value) as *mut leanh::LeanObject,12106318518385607562 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__47_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 97, 114, 97, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__47: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__47_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__47_value) as *mut leanh::LeanObject,10424585805673941106 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__49_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [117, 108, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__49: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__49_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__49_value) as *mut leanh::LeanObject,6453691647374023416 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__51_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [111, 108, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__51: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__51_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__51_value) as *mut leanh::LeanObject,12480416442879068486 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__53_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [98, 108, 111, 99, 107, 113, 117, 111, 116, 101, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__53: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__53_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__53_value) as *mut leanh::LeanObject,16099003537413514650 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__55_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [99, 111, 100, 101, 98, 108, 111, 99, 107, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__55: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__55_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__55_value) as *mut leanh::LeanObject,12761800624135336676 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__57_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 105, 114, 101, 99, 116, 105, 118, 101, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__57: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__57_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__57_value) as *mut leanh::LeanObject,13115808082649082939 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__59_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__59: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__59_value) as *mut leanh::LeanObject;
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__59_value) as *mut leanh::LeanObject,5109585754862282403 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__61_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [123, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__61: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__61_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__62_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [125, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__62: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__62_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__63_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__63: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__63_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__64_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [62, 32, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__64: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__64_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__3_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [108, 105, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__3_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__3_value) as *mut leanh::LeanObject,7179854397063619926 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [46, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__5_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [42, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__65_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [35, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__65: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__65_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__66_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [125, 91, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__66: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__66_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__67_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [115, 116, 114, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__67: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__67_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__68_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__67_value) as *mut leanh::LeanObject,9232979286016572671 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__68: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__68_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__69_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__69: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__69_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__69_value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__71_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__71: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__71_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__72_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 58, 61, 32, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__72: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__72_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__73_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__73: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__73_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__74_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 117, 109, 0]};
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__74: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__74_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__75_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__74_value) as *mut leanh::LeanObject,6110315075117401315 as *mut leanh::LeanObject] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__75: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__75_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__0_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [109, 101, 116, 97, 100, 97, 116, 97, 95, 98, 108, 111, 99, 107, 0]};
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__1_value) as *mut leanh::LeanObject,8539228228387540046 as *mut leanh::LeanObject] };
static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__2_value) as *mut leanh::LeanObject,18444330650968222853 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject,15635760689405348171 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Doc_Parser_document_formatter___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Doc_Parser_document_formatter___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Doc_Parser_document_formatter___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_Parser_document_formatter___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(
    mut v_x_1744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stx_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: u8 = 0;
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: u8 = 0;
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1744_) {
                1 => {
                    v_args_1755_ = leanh::lean_ctor_get(v_x_1744_, 2);
                    v___x_1756_ = lean_array_get_size(v_args_1755_);
                    v___x_1757_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1758_ = lean_nat_dec_eq(v___x_1756_, v___x_1757_);
                    if v___x_1758_ == 0 {
                        v_stx_1746_ = v_x_1744_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc_ref(v_args_1755_);
                        leanh::lean_dec_ref_known(v_x_1744_, 3);
                        v___x_1759_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1760_ = lean_array_fget(v_args_1755_, v___x_1759_);
                        leanh::lean_dec_ref(v_args_1755_);
                        v_x_1744_ = v___x_1760_;
                        state = 0;
                        continue;
                    }
                }
                2 => {
                    v_val_1762_ = leanh::lean_ctor_get(v_x_1744_, 1);
                    leanh::lean_inc_ref(v_val_1762_);
                    leanh::lean_dec_ref_known(v_x_1744_, 2);
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
                v___x_1748_ = leanh::lean_box(0);
                v___x_1749_ = 0;
                v___x_1750_ = l_Lean_Syntax_formatStx(v_stx_1746_, v___x_1748_, v___x_1749_);
                v___x_1751_ = l_Std_Format_defWidth;
                v___x_1752_ = leanh::lean_unsigned_to_nat(0);
                v___x_1753_ =
                    l_Std_Format_pretty(v___x_1750_, v___x_1751_, v___x_1752_, v___x_1752_);
                v___x_1754_ = lean_string_append(v___x_1747_, v___x_1753_);
                leanh::lean_dec_ref(v___x_1753_);
                return v___x_1754_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(
    mut v___y_1763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stxTrav_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cur_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1765_ = lean_st_ref_get(v___y_1763_);
    v_stxTrav_1766_ = leanh::lean_ctor_get(v___x_1765_, 0);
    leanh::lean_inc_ref(v_stxTrav_1766_);
    leanh::lean_dec(v___x_1765_);
    v_cur_1767_ = leanh::lean_ctor_get(v_stxTrav_1766_, 0);
    leanh::lean_inc(v_cur_1767_);
    leanh::lean_dec_ref(v_stxTrav_1766_);
    v___x_1768_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1768_, 0, v_cur_1767_);
    return v___x_1768_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg___boxed(
    mut v___y_1769_: *mut leanh::LeanObject,
    mut v___y_1770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1771_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v___y_1769_);
    leanh::lean_dec(v___y_1769_);
    return v_res_1771_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0(
    mut v___y_1772_: *mut leanh::LeanObject,
    mut v___y_1773_: *mut leanh::LeanObject,
    mut v___y_1774_: *mut leanh::LeanObject,
    mut v___y_1775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1777_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v___y_1773_);
    return v___x_1777_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___boxed(
    mut v___y_1778_: *mut leanh::LeanObject,
    mut v___y_1779_: *mut leanh::LeanObject,
    mut v___y_1780_: *mut leanh::LeanObject,
    mut v___y_1781_: *mut leanh::LeanObject,
    mut v___y_1782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1783_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0(v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
    leanh::lean_dec(v___y_1781_);
    leanh::lean_dec_ref(v___y_1780_);
    leanh::lean_dec(v___y_1779_);
    leanh::lean_dec_ref(v___y_1778_);
    return v_res_1783_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(
    mut v___y_1784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stxTrav_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leadWord_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leadWordIdent_1789_: u8 = 0;
    let mut v_isUngrouped_1790_: u8 = 0;
    let mut v_mustBeGrouped_1791_: u8 = 0;
    let mut v_stack_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1795_: u8 = 0;
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1803_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1786_ = lean_st_ref_take(v___y_1784_);
                v_stxTrav_1787_ = leanh::lean_ctor_get(v___x_1786_, 0);
                v_leadWord_1788_ = leanh::lean_ctor_get(v___x_1786_, 1);
                v_leadWordIdent_1789_ = leanh::lean_ctor_get_uint8(
                    v___x_1786_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_isUngrouped_1790_ = leanh::lean_ctor_get_uint8(
                    v___x_1786_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_mustBeGrouped_1791_ = leanh::lean_ctor_get_uint8(
                    v___x_1786_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2) as u32,
                );
                v_stack_1792_ = leanh::lean_ctor_get(v___x_1786_, 2);
                v_isSharedCheck_1803_ = (!leanh::lean_is_exclusive(v___x_1786_)) as u8;
                if v_isSharedCheck_1803_ == 0 {
                    v___x_1794_ = v___x_1786_;
                    v_isShared_1795_ = v_isSharedCheck_1803_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_stack_1792_);
                    leanh::lean_inc(v_leadWord_1788_);
                    leanh::lean_inc(v_stxTrav_1787_);
                    leanh::lean_dec(v___x_1786_);
                    v___x_1794_ = leanh::lean_box(0);
                    v_isShared_1795_ = v_isSharedCheck_1803_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1796_ = l_Lean_Syntax_Traverser_left(v_stxTrav_1787_);
                if v_isShared_1795_ == 0 {
                    leanh::lean_ctor_set(v___x_1794_, 0, v___x_1796_);
                    v___x_1798_ = v___x_1794_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1802_ = leanh::lean_alloc_ctor(0, 3, (3) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1796_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_leadWord_1788_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1802_, 2, v_stack_1792_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1802_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_leadWordIdent_1789_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1802_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                        v_isUngrouped_1790_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1802_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2) as u32,
                        v_mustBeGrouped_1791_,
                    );
                    v___x_1798_ = v_reuseFailAlloc_1802_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1799_ = lean_st_ref_set(v___y_1784_, v___x_1798_);
                v___x_1800_ = leanh::lean_box(0);
                v___x_1801_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1801_, 0, v___x_1800_);
                return v___x_1801_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg___boxed(
    mut v___y_1804_: *mut leanh::LeanObject,
    mut v___y_1805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1806_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(v___y_1804_);
    leanh::lean_dec(v___y_1804_);
    return v_res_1806_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1(
    mut v___y_1807_: *mut leanh::LeanObject,
    mut v___y_1808_: *mut leanh::LeanObject,
    mut v___y_1809_: *mut leanh::LeanObject,
    mut v___y_1810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1812_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(v___y_1808_);
    return v___x_1812_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___boxed(
    mut v___y_1813_: *mut leanh::LeanObject,
    mut v___y_1814_: *mut leanh::LeanObject,
    mut v___y_1815_: *mut leanh::LeanObject,
    mut v___y_1816_: *mut leanh::LeanObject,
    mut v___y_1817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1818_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1(v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
    leanh::lean_dec(v___y_1816_);
    leanh::lean_dec_ref(v___y_1815_);
    leanh::lean_dec(v___y_1814_);
    leanh::lean_dec_ref(v___y_1813_);
    return v_res_1818_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString(
    mut v_a_1819_: *mut leanh::LeanObject,
    mut v_a_1820_: *mut leanh::LeanObject,
    mut v_a_1821_: *mut leanh::LeanObject,
    mut v_a_1822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1828_: u8 = 0;
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1835_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1824_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v_a_1820_);
                v_a_1825_ = leanh::lean_ctor_get(v___x_1824_, 0);
                v_isSharedCheck_1835_ = (!leanh::lean_is_exclusive(v___x_1824_)) as u8;
                if v_isSharedCheck_1835_ == 0 {
                    v___x_1827_ = v___x_1824_;
                    v_isShared_1828_ = v_isSharedCheck_1835_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1825_);
                    leanh::lean_dec(v___x_1824_);
                    v___x_1827_ = leanh::lean_box(0);
                    v_isShared_1828_ = v_isSharedCheck_1835_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1829_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_a_1825_);
                if v_isShared_1828_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1827_, 3);
                    leanh::lean_ctor_set(v___x_1827_, 0, v___x_1829_);
                    v___x_1831_ = v___x_1827_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1834_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1829_);
                    v___x_1831_ = v_reuseFailAlloc_1834_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1832_ = l_Lean_PrettyPrinter_Formatter_push___redArg(v___x_1831_, v_a_1820_);
                if leanh::lean_obj_tag(v___x_1832_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1832_, 1);
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
    mut v_a_1836_: *mut leanh::LeanObject,
    mut v_a_1837_: *mut leanh::LeanObject,
    mut v_a_1838_: *mut leanh::LeanObject,
    mut v_a_1839_: *mut leanh::LeanObject,
    mut v_a_1840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1841_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString(
        v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_,
    );
    leanh::lean_dec(v_a_1839_);
    leanh::lean_dec_ref(v_a_1838_);
    leanh::lean_dec(v_a_1837_);
    leanh::lean_dec_ref(v_a_1836_);
    return v_res_1841_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg(
    mut v_a_1843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1849_: u8 = 0;
    let mut v___y_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1845_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v_a_1843_);
                v_a_1846_ = leanh::lean_ctor_get(v___x_1845_, 0);
                v_isSharedCheck_1861_ = (!leanh::lean_is_exclusive(v___x_1845_)) as u8;
                if v_isSharedCheck_1861_ == 0 {
                    v___x_1848_ = v___x_1845_;
                    v_isShared_1849_ = v_isSharedCheck_1861_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1846_);
                    leanh::lean_dec(v___x_1845_);
                    v___x_1848_ = leanh::lean_box(0);
                    v_isShared_1849_ = v_isSharedCheck_1861_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1857_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_a_1846_);
                v___x_1858_ = l_Lean_Syntax_decodeStrLit(v___x_1857_);
                if leanh::lean_obj_tag(v___x_1858_) == 0 {
                    v___x_1859_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
                    v___y_1851_ = v___x_1859_;
                    state = 2;
                    continue;
                } else {
                    v_val_1860_ = leanh::lean_ctor_get(v___x_1858_, 0);
                    leanh::lean_inc(v_val_1860_);
                    leanh::lean_dec_ref_known(v___x_1858_, 1);
                    v___y_1851_ = v_val_1860_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1849_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1848_, 3);
                    leanh::lean_ctor_set(v___x_1848_, 0, v___y_1851_);
                    v___x_1853_ = v___x_1848_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1856_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___y_1851_);
                    v___x_1853_ = v_reuseFailAlloc_1856_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1854_ = l_Lean_PrettyPrinter_Formatter_push___redArg(v___x_1853_, v_a_1843_);
                if leanh::lean_obj_tag(v___x_1854_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1854_, 1);
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
    mut v_a_1862_: *mut leanh::LeanObject,
    mut v_a_1863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1864_ =
        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg(v_a_1862_);
    leanh::lean_dec(v_a_1862_);
    return v_res_1864_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit(
    mut v_a_1865_: *mut leanh::LeanObject,
    mut v_a_1866_: *mut leanh::LeanObject,
    mut v_a_1867_: *mut leanh::LeanObject,
    mut v_a_1868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1870_ =
        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg(v_a_1866_);
    return v___x_1870_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___boxed(
    mut v_a_1871_: *mut leanh::LeanObject,
    mut v_a_1872_: *mut leanh::LeanObject,
    mut v_a_1873_: *mut leanh::LeanObject,
    mut v_a_1874_: *mut leanh::LeanObject,
    mut v_a_1875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1876_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit(
        v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_,
    );
    leanh::lean_dec(v_a_1874_);
    leanh::lean_dec_ref(v_a_1873_);
    leanh::lean_dec(v_a_1872_);
    leanh::lean_dec_ref(v_a_1871_);
    return v_res_1876_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(
    mut v_x_1878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stx_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: u8 = 0;
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: u8 = 0;
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: u8 = 0;
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1878_) {
                1 => {
                    v_args_1889_ = leanh::lean_ctor_get(v_x_1878_, 2);
                    v___x_1890_ = lean_array_get_size(v_args_1889_);
                    v___x_1891_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1892_ = lean_nat_dec_eq(v___x_1890_, v___x_1891_);
                    if v___x_1892_ == 0 {
                        v_stx_1880_ = v_x_1878_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc_ref(v_args_1889_);
                        leanh::lean_dec_ref_known(v_x_1878_, 3);
                        v___x_1893_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1894_ = lean_array_fget(v_args_1889_, v___x_1893_);
                        leanh::lean_dec_ref(v_args_1889_);
                        v_x_1878_ = v___x_1894_;
                        state = 0;
                        continue;
                    }
                }
                3 => {
                    v_val_1896_ = leanh::lean_ctor_get(v_x_1878_, 2);
                    leanh::lean_inc(v_val_1896_);
                    leanh::lean_dec_ref_known(v_x_1878_, 4);
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
                v___x_1882_ = leanh::lean_box(0);
                v___x_1883_ = 0;
                v___x_1884_ = l_Lean_Syntax_formatStx(v_stx_1880_, v___x_1882_, v___x_1883_);
                v___x_1885_ = l_Std_Format_defWidth;
                v___x_1886_ = leanh::lean_unsigned_to_nat(0);
                v___x_1887_ =
                    l_Std_Format_pretty(v___x_1884_, v___x_1885_, v___x_1886_, v___x_1886_);
                v___x_1888_ = lean_string_append(v___x_1881_, v___x_1887_);
                leanh::lean_dec_ref(v___x_1887_);
                return v___x_1888_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___redArg(
    mut v_a_1899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1905_: u8 = 0;
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1912_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1901_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v_a_1899_);
                v_a_1902_ = leanh::lean_ctor_get(v___x_1901_, 0);
                v_isSharedCheck_1912_ = (!leanh::lean_is_exclusive(v___x_1901_)) as u8;
                if v_isSharedCheck_1912_ == 0 {
                    v___x_1904_ = v___x_1901_;
                    v_isShared_1905_ = v_isSharedCheck_1912_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1902_);
                    leanh::lean_dec(v___x_1901_);
                    v___x_1904_ = leanh::lean_box(0);
                    v_isShared_1905_ = v_isSharedCheck_1912_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1906_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_a_1902_);
                if v_isShared_1905_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1904_, 3);
                    leanh::lean_ctor_set(v___x_1904_, 0, v___x_1906_);
                    v___x_1908_ = v___x_1904_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1911_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1906_);
                    v___x_1908_ = v_reuseFailAlloc_1911_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1909_ = l_Lean_PrettyPrinter_Formatter_push___redArg(v___x_1908_, v_a_1899_);
                if leanh::lean_obj_tag(v___x_1909_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1909_, 1);
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
    mut v_a_1913_: *mut leanh::LeanObject,
    mut v_a_1914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1915_ =
        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___redArg(v_a_1913_);
    leanh::lean_dec(v_a_1913_);
    return v_res_1915_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent(
    mut v_a_1916_: *mut leanh::LeanObject,
    mut v_a_1917_: *mut leanh::LeanObject,
    mut v_a_1918_: *mut leanh::LeanObject,
    mut v_a_1919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1921_ =
        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___redArg(v_a_1917_);
    return v___x_1921_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent___boxed(
    mut v_a_1922_: *mut leanh::LeanObject,
    mut v_a_1923_: *mut leanh::LeanObject,
    mut v_a_1924_: *mut leanh::LeanObject,
    mut v_a_1925_: *mut leanh::LeanObject,
    mut v_a_1926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1927_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushIdent(
        v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_,
    );
    leanh::lean_dec(v_a_1925_);
    leanh::lean_dec_ref(v_a_1924_);
    leanh::lean_dec(v_a_1923_);
    leanh::lean_dec_ref(v_a_1922_);
    return v_res_1927_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___redArg(
    mut v_f_1928_: *mut leanh::LeanObject,
    mut v_i_1929_: *mut leanh::LeanObject,
    mut v___y_1930_: *mut leanh::LeanObject,
    mut v___y_1931_: *mut leanh::LeanObject,
    mut v___y_1932_: *mut leanh::LeanObject,
    mut v___y_1933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1936_: u8 = 0;
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1935_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1936_ = lean_nat_dec_eq(v_i_1929_, v_zero_1935_);
                if v_isZero_1936_ == 1 {
                    leanh::lean_dec(v_i_1929_);
                    leanh::lean_dec_ref(v_f_1928_);
                    v___x_1937_ = leanh::lean_box(0);
                    v___x_1938_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1938_, 0, v___x_1937_);
                    return v___x_1938_;
                } else {
                    leanh::lean_inc_ref(v_f_1928_);
                    leanh::lean_inc(v___y_1933_);
                    leanh::lean_inc_ref(v___y_1932_);
                    leanh::lean_inc(v___y_1931_);
                    leanh::lean_inc_ref(v___y_1930_);
                    v___x_1939_ = leanh::lean_apply_5(
                        v_f_1928_,
                        v___y_1930_,
                        v___y_1931_,
                        v___y_1932_,
                        v___y_1933_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_1939_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1939_, 1);
                        v_one_1940_ = leanh::lean_unsigned_to_nat(1);
                        v_n_1941_ = lean_nat_sub(v_i_1929_, v_one_1940_);
                        leanh::lean_dec(v_i_1929_);
                        v_i_1929_ = v_n_1941_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_1929_);
                        leanh::lean_dec_ref(v_f_1928_);
                        return v___x_1939_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___redArg___boxed(
    mut v_f_1943_: *mut leanh::LeanObject,
    mut v_i_1944_: *mut leanh::LeanObject,
    mut v___y_1945_: *mut leanh::LeanObject,
    mut v___y_1946_: *mut leanh::LeanObject,
    mut v___y_1947_: *mut leanh::LeanObject,
    mut v___y_1948_: *mut leanh::LeanObject,
    mut v___y_1949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1950_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___redArg(v_f_1943_, v_i_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
    leanh::lean_dec(v___y_1948_);
    leanh::lean_dec_ref(v___y_1947_);
    leanh::lean_dec(v___y_1946_);
    leanh::lean_dec_ref(v___y_1945_);
    return v_res_1950_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0(
    mut v_f_1951_: *mut leanh::LeanObject,
    mut v_n_1952_: *mut leanh::LeanObject,
    mut v_i_1953_: *mut leanh::LeanObject,
    mut v_a_1954_: *mut leanh::LeanObject,
    mut v___y_1955_: *mut leanh::LeanObject,
    mut v___y_1956_: *mut leanh::LeanObject,
    mut v___y_1957_: *mut leanh::LeanObject,
    mut v___y_1958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1960_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___redArg(v_f_1951_, v_i_1953_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
    return v___x_1960_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___boxed(
    mut v_f_1961_: *mut leanh::LeanObject,
    mut v_n_1962_: *mut leanh::LeanObject,
    mut v_i_1963_: *mut leanh::LeanObject,
    mut v_a_1964_: *mut leanh::LeanObject,
    mut v___y_1965_: *mut leanh::LeanObject,
    mut v___y_1966_: *mut leanh::LeanObject,
    mut v___y_1967_: *mut leanh::LeanObject,
    mut v___y_1968_: *mut leanh::LeanObject,
    mut v___y_1969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1970_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0(v_f_1961_, v_n_1962_, v_i_1963_, v_a_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
    leanh::lean_dec(v___y_1968_);
    leanh::lean_dec_ref(v___y_1967_);
    leanh::lean_dec(v___y_1966_);
    leanh::lean_dec_ref(v___y_1965_);
    leanh::lean_dec(v_n_1962_);
    return v_res_1970_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___lam__0(
    mut v_f_1971_: *mut leanh::LeanObject,
    mut v___y_1972_: *mut leanh::LeanObject,
    mut v___y_1973_: *mut leanh::LeanObject,
    mut v___y_1974_: *mut leanh::LeanObject,
    mut v___y_1975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_count_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1977_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v___y_1973_);
    v_a_1978_ = leanh::lean_ctor_get(v___x_1977_, 0);
    leanh::lean_inc(v_a_1978_);
    leanh::lean_dec_ref(v___x_1977_);
    v___x_1979_ = l_Lean_Syntax_getArgs(v_a_1978_);
    leanh::lean_dec(v_a_1978_);
    v_count_1980_ = lean_array_get_size(v___x_1979_);
    leanh::lean_dec_ref(v___x_1979_);
    v___x_1981_ = leanh::lean_alloc_closure(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep_spec__0___boxed as *mut core::ffi::c_void, 9, 4);
    leanh::lean_closure_set(v___x_1981_, 0, v_f_1971_);
    leanh::lean_closure_set(v___x_1981_, 1, v_count_1980_);
    leanh::lean_closure_set(v___x_1981_, 2, v_count_1980_);
    leanh::lean_closure_set(v___x_1981_, 3, leanh::lean_box(0));
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
    mut v_f_1983_: *mut leanh::LeanObject,
    mut v___y_1984_: *mut leanh::LeanObject,
    mut v___y_1985_: *mut leanh::LeanObject,
    mut v___y_1986_: *mut leanh::LeanObject,
    mut v___y_1987_: *mut leanh::LeanObject,
    mut v___y_1988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1989_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___lam__0(
        v_f_1983_,
        v___y_1984_,
        v___y_1985_,
        v___y_1986_,
        v___y_1987_,
    );
    leanh::lean_dec(v___y_1987_);
    leanh::lean_dec_ref(v___y_1986_);
    leanh::lean_dec(v___y_1985_);
    leanh::lean_dec_ref(v___y_1984_);
    return v_res_1989_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep(
    mut v_f_1990_: *mut leanh::LeanObject,
    mut v_a_1991_: *mut leanh::LeanObject,
    mut v_a_1992_: *mut leanh::LeanObject,
    mut v_a_1993_: *mut leanh::LeanObject,
    mut v_a_1994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1996_ = leanh::lean_alloc_closure(
        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep___lam__0___boxed
            as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1996_, 0, v_f_1990_);
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
    mut v_f_1998_: *mut leanh::LeanObject,
    mut v_a_1999_: *mut leanh::LeanObject,
    mut v_a_2000_: *mut leanh::LeanObject,
    mut v_a_2001_: *mut leanh::LeanObject,
    mut v_a_2002_: *mut leanh::LeanObject,
    mut v_a_2003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2004_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_rep(
        v_f_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_,
    );
    leanh::lean_dec(v_a_2002_);
    leanh::lean_dec_ref(v_a_2001_);
    leanh::lean_dec(v_a_2000_);
    leanh::lean_dec_ref(v_a_1999_);
    return v_res_2004_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(
    mut v_s_2005_: *mut leanh::LeanObject,
    mut v_a_2006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2007_ = leanh::lean_box(0);
    v___x_2008_ = lean_string_append(v_a_2006_, v_s_2005_);
    v___x_2009_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2009_, 0, v___x_2007_);
    leanh::lean_ctor_set(v___x_2009_, 1, v___x_2008_);
    return v___x_2009_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg___boxed(
    mut v_s_2010_: *mut leanh::LeanObject,
    mut v_a_2011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2012_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v_s_2010_, v_a_2011_);
    leanh::lean_dec_ref(v_s_2010_);
    return v_res_2012_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out(
    mut v_s_2013_: *mut leanh::LeanObject,
    mut v_a_2014_: *mut leanh::LeanObject,
    mut v_a_2015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2016_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v_s_2013_, v_a_2015_);
    return v___x_2016_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___boxed(
    mut v_s_2017_: *mut leanh::LeanObject,
    mut v_a_2018_: *mut leanh::LeanObject,
    mut v_a_2019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2020_ =
        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out(
            v_s_2017_, v_a_2018_, v_a_2019_,
        );
    leanh::lean_dec(v_a_2018_);
    leanh::lean_dec_ref(v_s_2017_);
    return v_res_2020_;
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(
    mut v_x_2021_: *mut leanh::LeanObject,
    mut v_x_2022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2024_: u8 = 0;
    let mut v___x_2025_: u32 = 0;
    let mut v_one_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2023_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_2024_ = lean_nat_dec_eq(v_x_2021_, v_zero_2023_);
                if v_isZero_2024_ == 1 {
                    leanh::lean_dec(v_x_2021_);
                    return v_x_2022_;
                } else {
                    v___x_2025_ = 32;
                    v_one_2026_ = leanh::lean_unsigned_to_nat(1);
                    v_n_2027_ = lean_nat_sub(v_x_2021_, v_one_2026_);
                    leanh::lean_dec(v_x_2021_);
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
    mut v_a_2031_: *mut leanh::LeanObject,
    mut v_a_2032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2033_ = leanh::lean_box(0);
    v___x_2034_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0;
    leanh::lean_inc(v_a_2031_);
    v___x_2035_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(v_a_2031_, v___x_2034_);
    v___x_2036_ = lean_string_append(v_a_2032_, v___x_2035_);
    leanh::lean_dec_ref(v___x_2035_);
    v___x_2037_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2037_, 0, v___x_2033_);
    leanh::lean_ctor_set(v___x_2037_, 1, v___x_2036_);
    return v___x_2037_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___boxed(
    mut v_a_2038_: *mut leanh::LeanObject,
    mut v_a_2039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2040_ =
        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl(
            v_a_2038_, v_a_2039_,
        );
    leanh::lean_dec(v_a_2038_);
    return v_res_2040_;
}
pub unsafe fn _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2041_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0;
    v___x_2042_ = lean_string_utf8_byte_size(v___x_2041_);
    return v___x_2042_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(
    mut v_a_2043_: *mut leanh::LeanObject,
    mut v_a_2044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: u8 = 0;
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: u8 = 0;
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2048_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0;
                v___x_2049_ = lean_string_utf8_byte_size(v_a_2044_);
                v___x_2050_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0), core::ptr::addr_of_mut!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0_once), _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0);
                v___x_2051_ = lean_nat_dec_le(v___x_2050_, v___x_2049_);
                if v___x_2051_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_2052_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2053_ = lean_nat_sub(v___x_2049_, v___x_2050_);
                    v___x_2054_ = lean_string_memcmp(
                        v_a_2044_,
                        v___x_2048_,
                        v___x_2053_,
                        v___x_2052_,
                        v___x_2050_,
                    );
                    leanh::lean_dec(v___x_2053_);
                    if v___x_2054_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_2055_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
                        leanh::lean_inc(v_a_2043_);
                        v___x_2056_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(v_a_2043_, v___x_2055_);
                        v___x_2057_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2056_, v_a_2044_);
                        leanh::lean_dec_ref(v___x_2056_);
                        return v___x_2057_;
                    }
                }
            }
            1 => {
                v___x_2046_ = leanh::lean_box(0);
                v___x_2047_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2047_, 0, v___x_2046_);
                leanh::lean_ctor_set(v___x_2047_, 1, v_a_2044_);
                return v___x_2047_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___boxed(
    mut v_a_2058_: *mut leanh::LeanObject,
    mut v_a_2059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2060_ =
        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(
            v_a_2058_, v_a_2059_,
        );
    leanh::lean_dec(v_a_2058_);
    return v_res_2060_;
}
pub unsafe fn _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2062_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__0;
    v___x_2063_ = lean_string_utf8_byte_size(v___x_2062_);
    return v___x_2063_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(
    mut v_a_2064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: u8 = 0;
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: u8 = 0;
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: u8 = 0;
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: u8 = 0;
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2065_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__0;
                v___x_2077_ = lean_string_utf8_byte_size(v_a_2064_);
                v___x_2078_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1_once), _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg___closed__1);
                v___x_2079_ = lean_nat_dec_le(v___x_2078_, v___x_2077_);
                if v___x_2079_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_2080_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2081_ = lean_nat_sub(v___x_2077_, v___x_2078_);
                    v___x_2082_ = lean_string_memcmp(
                        v_a_2064_,
                        v___x_2065_,
                        v___x_2081_,
                        v___x_2080_,
                        v___x_2078_,
                    );
                    leanh::lean_dec(v___x_2081_);
                    if v___x_2082_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_2083_ = leanh::lean_box(0);
                        v___x_2084_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2084_, 0, v___x_2083_);
                        leanh::lean_ctor_set(v___x_2084_, 1, v_a_2064_);
                        return v___x_2084_;
                    }
                }
            }
            1 => {
                v___x_2067_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0;
                v___x_2068_ = lean_string_utf8_byte_size(v_a_2064_);
                v___x_2069_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0), core::ptr::addr_of_mut!(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0_once), _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock___closed__0);
                v___x_2070_ = lean_nat_dec_le(v___x_2069_, v___x_2068_);
                if v___x_2070_ == 0 {
                    v___x_2071_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2065_, v_a_2064_);
                    return v___x_2071_;
                } else {
                    v___x_2072_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2073_ = lean_nat_sub(v___x_2068_, v___x_2069_);
                    v___x_2074_ = lean_string_memcmp(
                        v_a_2064_,
                        v___x_2067_,
                        v___x_2073_,
                        v___x_2072_,
                        v___x_2069_,
                    );
                    leanh::lean_dec(v___x_2073_);
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
    mut v_a_2085_: *mut leanh::LeanObject,
    mut v_a_2086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2087_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_a_2086_);
    return v___x_2087_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___boxed(
    mut v_a_2088_: *mut leanh::LeanObject,
    mut v_a_2089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2090_ =
        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock(
            v_a_2088_, v_a_2089_,
        );
    leanh::lean_dec(v_a_2088_);
    return v_res_2090_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(
    mut v_s_2093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2094_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___closed__0;
    return v___x_2094_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___boxed(
    mut v_s_2095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2096_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_s_2095_);
    leanh::lean_dec_ref(v_s_2095_);
    return v_res_2096_;
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(
    mut v_x_2097_: *mut leanh::LeanObject,
    mut v_x_2098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2100_: u8 = 0;
    let mut v___x_2101_: u32 = 0;
    let mut v_one_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2099_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_2100_ = lean_nat_dec_eq(v_x_2097_, v_zero_2099_);
                if v_isZero_2100_ == 1 {
                    leanh::lean_dec(v_x_2097_);
                    return v_x_2098_;
                } else {
                    v___x_2101_ = 35;
                    v_one_2102_ = leanh::lean_unsigned_to_nat(1);
                    v_n_2103_ = lean_nat_sub(v_x_2097_, v_one_2102_);
                    leanh::lean_dec(v_x_2097_);
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
    mut v_a_2106_: *mut leanh::LeanObject,
    mut v___y_2107_: *mut leanh::LeanObject,
    mut v___x_2108_: *mut leanh::LeanObject,
    mut v___x_2109_: *mut leanh::LeanObject,
    mut v_a_2110_: *mut leanh::LeanObject,
    mut v_b_2111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2126_: u8 = 0;
    let mut v_startInclusive_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: u8 = 0;
    let mut v___x_2131_: u32 = 0;
    let mut v___x_2132_: u32 = 0;
    let mut v___x_2133_: u8 = 0;
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2149_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2110_) == 0 {
                    v_currPos_2122_ = leanh::lean_ctor_get(v_a_2110_, 0);
                    v_searcher_2123_ = leanh::lean_ctor_get(v_a_2110_, 1);
                    v_isSharedCheck_2149_ = (!leanh::lean_is_exclusive(v_a_2110_)) as u8;
                    if v_isSharedCheck_2149_ == 0 {
                        v___x_2125_ = v_a_2110_;
                        v_isShared_2126_ = v_isSharedCheck_2149_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_searcher_2123_);
                        leanh::lean_inc(v_currPos_2122_);
                        leanh::lean_dec(v_a_2110_);
                        v___x_2125_ = leanh::lean_box(0);
                        v_isShared_2126_ = v_isSharedCheck_2149_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2109_);
                    return v_b_2111_;
                }
            }
            1 => {
                v___x_2116_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
                leanh::lean_inc(v_a_2106_);
                v___x_2117_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(v_a_2106_, v___x_2116_);
                v___x_2118_ = lean_string_utf8_extract(
                    v___y_2107_,
                    v_startInclusive_2114_,
                    v_endExclusive_2115_,
                );
                leanh::lean_dec(v_endExclusive_2115_);
                leanh::lean_dec(v_startInclusive_2114_);
                v___x_2119_ = lean_string_append(v___x_2117_, v___x_2118_);
                leanh::lean_dec_ref(v___x_2118_);
                v___x_2120_ = lean_array_push(v_b_2111_, v___x_2119_);
                v_a_2110_ = v_it_2113_;
                v_b_2111_ = v___x_2120_;
                state = 0;
                continue;
            }
            2 => {
                v_startInclusive_2127_ = leanh::lean_ctor_get(v___x_2108_, 1);
                v_endExclusive_2128_ = leanh::lean_ctor_get(v___x_2108_, 2);
                v___x_2129_ = lean_nat_sub(v_endExclusive_2128_, v_startInclusive_2127_);
                v___x_2130_ = lean_nat_dec_eq(v_searcher_2123_, v___x_2129_);
                leanh::lean_dec(v___x_2129_);
                if v___x_2130_ == 0 {
                    v___x_2131_ = 10;
                    v___x_2132_ = lean_string_utf8_get_fast(v___y_2107_, v_searcher_2123_);
                    v___x_2133_ = lean_uint32_dec_eq(v___x_2132_, v___x_2131_);
                    if v___x_2133_ == 0 {
                        v___x_2134_ = lean_string_utf8_next_fast(v___y_2107_, v_searcher_2123_);
                        leanh::lean_dec(v_searcher_2123_);
                        if v_isShared_2126_ == 0 {
                            leanh::lean_ctor_set(v___x_2125_, 1, v___x_2134_);
                            v___x_2136_ = v___x_2125_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2138_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_currPos_2122_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2138_, 1, v___x_2134_);
                            v___x_2136_ = v_reuseFailAlloc_2138_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2139_ = lean_string_utf8_next_fast(v___y_2107_, v_searcher_2123_);
                        v___x_2140_ = lean_nat_sub(v___x_2139_, v_searcher_2123_);
                        v___x_2141_ = lean_nat_add(v_searcher_2123_, v___x_2140_);
                        leanh::lean_dec(v___x_2140_);
                        v_slice_2142_ = l_String_Slice_subslice_x21(
                            v___x_2108_,
                            v_currPos_2122_,
                            v_searcher_2123_,
                        );
                        leanh::lean_inc(v___x_2141_);
                        if v_isShared_2126_ == 0 {
                            leanh::lean_ctor_set(v___x_2125_, 1, v___x_2141_);
                            leanh::lean_ctor_set(v___x_2125_, 0, v___x_2141_);
                            v_nextIt_2144_ = v___x_2125_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2147_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2141_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2147_, 1, v___x_2141_);
                            v_nextIt_2144_ = v_reuseFailAlloc_2147_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_2125_);
                    leanh::lean_dec(v_searcher_2123_);
                    v___x_2148_ = leanh::lean_box(1);
                    leanh::lean_inc(v___x_2109_);
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
                v_startInclusive_2145_ = leanh::lean_ctor_get(v_slice_2142_, 0);
                leanh::lean_inc(v_startInclusive_2145_);
                v_endExclusive_2146_ = leanh::lean_ctor_get(v_slice_2142_, 1);
                leanh::lean_inc(v_endExclusive_2146_);
                leanh::lean_dec_ref(v_slice_2142_);
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
    mut v_a_2150_: *mut leanh::LeanObject,
    mut v___y_2151_: *mut leanh::LeanObject,
    mut v___x_2152_: *mut leanh::LeanObject,
    mut v___x_2153_: *mut leanh::LeanObject,
    mut v_a_2154_: *mut leanh::LeanObject,
    mut v_b_2155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2156_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg(v_a_2150_, v___y_2151_, v___x_2152_, v___x_2153_, v_a_2154_, v_b_2155_);
    leanh::lean_dec_ref(v___x_2152_);
    leanh::lean_dec_ref(v___y_2151_);
    leanh::lean_dec(v_a_2150_);
    return v_res_2156_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(
    mut v_as_2340_: *mut leanh::LeanObject,
    mut v_sz_2341_: usize,
    mut v_i_2342_: usize,
    mut v_b_2343_: *mut leanh::LeanObject,
    mut v___y_2344_: *mut leanh::LeanObject,
    mut v___y_2345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2346_: u8 = 0;
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: usize = 0;
    let mut v___x_2356_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2346_ = lean_usize_dec_lt(v_i_2342_, v_sz_2341_);
                if v___x_2346_ == 0 {
                    v___x_2347_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2347_, 0, v_b_2343_);
                    leanh::lean_ctor_set(v___x_2347_, 1, v___y_2345_);
                    return v___x_2347_;
                } else {
                    v___x_2348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0;
                    v___x_2349_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2348_, v___y_2345_);
                    v_snd_2350_ = leanh::lean_ctor_get(v___x_2349_, 1);
                    leanh::lean_inc(v_snd_2350_);
                    leanh::lean_dec_ref(v___x_2349_);
                    v_a_2351_ = lean_array_uget_borrowed(v_as_2340_, v_i_2342_);
                    leanh::lean_inc(v_a_2351_);
                    v___x_2352_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_a_2351_, v___y_2344_, v_snd_2350_);
                    v_snd_2353_ = leanh::lean_ctor_get(v___x_2352_, 1);
                    leanh::lean_inc(v_snd_2353_);
                    leanh::lean_dec_ref(v___x_2352_);
                    v___x_2354_ = leanh::lean_box(0);
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
    mut v_as_2359_: *mut leanh::LeanObject,
    mut v_sz_2360_: usize,
    mut v_i_2361_: usize,
    mut v_b_2362_: *mut leanh::LeanObject,
    mut v___y_2363_: *mut leanh::LeanObject,
    mut v___y_2364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2365_: u8 = 0;
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: usize = 0;
    let mut v___x_2375_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2365_ = lean_usize_dec_lt(v_i_2361_, v_sz_2360_);
                if v___x_2365_ == 0 {
                    v___x_2366_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2366_, 0, v_b_2362_);
                    leanh::lean_ctor_set(v___x_2366_, 1, v___y_2364_);
                    return v___x_2366_;
                } else {
                    v___x_2367_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0;
                    v___x_2368_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2367_, v___y_2364_);
                    v_snd_2369_ = leanh::lean_ctor_get(v___x_2368_, 1);
                    leanh::lean_inc(v_snd_2369_);
                    leanh::lean_dec_ref(v___x_2368_);
                    v_a_2370_ = lean_array_uget_borrowed(v_as_2359_, v_i_2361_);
                    leanh::lean_inc(v_a_2370_);
                    v___x_2371_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_a_2370_, v___y_2363_, v_snd_2369_);
                    v_snd_2372_ = leanh::lean_ctor_get(v___x_2371_, 1);
                    leanh::lean_inc(v_snd_2372_);
                    leanh::lean_dec_ref(v___x_2371_);
                    v___x_2373_ = leanh::lean_box(0);
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
    mut v_as_2387_: *mut leanh::LeanObject,
    mut v_sz_2388_: usize,
    mut v_i_2389_: usize,
    mut v_b_2390_: *mut leanh::LeanObject,
    mut v___y_2391_: *mut leanh::LeanObject,
    mut v___y_2392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: usize = 0;
    let mut v___x_2397_: usize = 0;
    let mut v___x_2399_: u8 = 0;
    let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: u8 = 0;
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: u8 = 0;
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: u8 = 0;
    let mut v___x_2427_: usize = 0;
    let mut v___x_2428_: usize = 0;
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: usize = 0;
    let mut v___x_2431_: usize = 0;
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2399_ = lean_usize_dec_lt(v_i_2389_, v_sz_2388_);
                if v___x_2399_ == 0 {
                    v___x_2400_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2400_, 0, v_b_2390_);
                    leanh::lean_ctor_set(v___x_2400_, 1, v___y_2392_);
                    return v___x_2400_;
                } else {
                    v_a_2401_ = lean_array_uget_borrowed(v_as_2387_, v_i_2389_);
                    v___x_2402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4;
                    leanh::lean_inc(v_a_2401_);
                    v___x_2403_ = l_Lean_Syntax_isOfKind(v_a_2401_, v___x_2402_);
                    if v___x_2403_ == 0 {
                        v_a_2394_ = v_b_2390_;
                        v_snd_2395_ = v___y_2392_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_b_2390_);
                        v___x_2404_ = l_Nat_reprFast(v_b_2390_);
                        v___x_2405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___closed__0;
                        v___x_2406_ = lean_string_append(v___x_2404_, v___x_2405_);
                        v___x_2407_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2406_, v___y_2392_);
                        leanh::lean_dec_ref(v___x_2406_);
                        v_snd_2408_ = leanh::lean_ctor_get(v___x_2407_, 1);
                        leanh::lean_inc(v_snd_2408_);
                        leanh::lean_dec_ref(v___x_2407_);
                        v___x_2409_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2418_ = leanh::lean_unsigned_to_nat(0);
                        v___x_2419_ = l_Lean_Syntax_getArg(v_a_2401_, v___x_2409_);
                        v___x_2420_ = l_Lean_Syntax_getArgs(v___x_2419_);
                        leanh::lean_dec(v___x_2419_);
                        v___x_2421_ = lean_array_get_size(v___x_2420_);
                        v___x_2422_ = lean_nat_dec_lt(v___x_2418_, v___x_2421_);
                        if v___x_2422_ == 0 {
                            leanh::lean_dec_ref(v___x_2420_);
                            v_snd_2411_ = v_snd_2408_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2423_ = leanh::lean_unsigned_to_nat(2);
                            v___x_2424_ = lean_nat_add(v___y_2391_, v___x_2423_);
                            v___x_2425_ = leanh::lean_box(0);
                            v___x_2426_ = lean_nat_dec_le(v___x_2421_, v___x_2421_);
                            if v___x_2426_ == 0 {
                                if v___x_2422_ == 0 {
                                    leanh::lean_dec(v___x_2424_);
                                    leanh::lean_dec_ref(v___x_2420_);
                                    v_snd_2411_ = v_snd_2408_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_2427_ = 0usize;
                                    v___x_2428_ = lean_usize_of_nat(v___x_2421_);
                                    v___x_2429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_2420_, v___x_2427_, v___x_2428_, v___x_2425_, v___x_2424_, v_snd_2408_);
                                    leanh::lean_dec(v___x_2424_);
                                    leanh::lean_dec_ref(v___x_2420_);
                                    v___y_2416_ = v___x_2429_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                v___x_2430_ = 0usize;
                                v___x_2431_ = lean_usize_of_nat(v___x_2421_);
                                v___x_2432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_2420_, v___x_2430_, v___x_2431_, v___x_2425_, v___x_2424_, v_snd_2408_);
                                leanh::lean_dec(v___x_2424_);
                                leanh::lean_dec_ref(v___x_2420_);
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
                v_snd_2413_ = leanh::lean_ctor_get(v___x_2412_, 1);
                leanh::lean_inc(v_snd_2413_);
                leanh::lean_dec_ref(v___x_2412_);
                v___x_2414_ = lean_nat_add(v_b_2390_, v___x_2409_);
                leanh::lean_dec(v_b_2390_);
                v_a_2394_ = v___x_2414_;
                v_snd_2395_ = v_snd_2413_;
                state = 1;
                continue;
            }
            3 => {
                v_snd_2417_ = leanh::lean_ctor_get(v___y_2416_, 1);
                leanh::lean_inc(v_snd_2417_);
                leanh::lean_dec_ref(v___y_2416_);
                v_snd_2411_ = v_snd_2417_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(
    mut v_as_2434_: *mut leanh::LeanObject,
    mut v_i_2435_: usize,
    mut v_stop_2436_: usize,
    mut v_b_2437_: *mut leanh::LeanObject,
    mut v___y_2438_: *mut leanh::LeanObject,
    mut v___y_2439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: usize = 0;
    let mut v___x_2444_: usize = 0;
    let mut v___y_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: u8 = 0;
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: u8 = 0;
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: u8 = 0;
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: u8 = 0;
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: usize = 0;
    let mut v___x_2475_: usize = 0;
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: usize = 0;
    let mut v___x_2478_: usize = 0;
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2454_ = lean_usize_dec_eq(v_i_2435_, v_stop_2436_);
                if v___x_2454_ == 0 {
                    v___x_2455_ = lean_array_uget_borrowed(v_as_2434_, v_i_2435_);
                    v___x_2456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__4;
                    leanh::lean_inc(v___x_2455_);
                    v___x_2457_ = l_Lean_Syntax_isOfKind(v___x_2455_, v___x_2456_);
                    if v___x_2457_ == 0 {
                        v___x_2458_ = leanh::lean_box(0);
                        v_fst_2441_ = v___x_2458_;
                        v_snd_2442_ = v___y_2439_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___closed__5;
                        v___x_2460_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2459_, v___y_2439_);
                        v_snd_2461_ = leanh::lean_ctor_get(v___x_2460_, 1);
                        leanh::lean_inc(v_snd_2461_);
                        leanh::lean_dec_ref(v___x_2460_);
                        v___x_2462_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2463_ = leanh::lean_unsigned_to_nat(0);
                        v___x_2464_ = l_Lean_Syntax_getArg(v___x_2455_, v___x_2462_);
                        v___x_2465_ = l_Lean_Syntax_getArgs(v___x_2464_);
                        leanh::lean_dec(v___x_2464_);
                        v___x_2466_ = lean_array_get_size(v___x_2465_);
                        v___x_2467_ = lean_nat_dec_lt(v___x_2463_, v___x_2466_);
                        if v___x_2467_ == 0 {
                            leanh::lean_dec_ref(v___x_2465_);
                            v___x_2468_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2461_);
                            v___y_2447_ = v___x_2468_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2469_ = leanh::lean_unsigned_to_nat(2);
                            v___x_2470_ = lean_nat_add(v___y_2438_, v___x_2469_);
                            v___x_2471_ = leanh::lean_box(0);
                            v___x_2472_ = lean_nat_dec_le(v___x_2466_, v___x_2466_);
                            if v___x_2472_ == 0 {
                                if v___x_2467_ == 0 {
                                    leanh::lean_dec(v___x_2470_);
                                    leanh::lean_dec_ref(v___x_2465_);
                                    v___x_2473_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2461_);
                                    v___y_2447_ = v___x_2473_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_2474_ = 0usize;
                                    v___x_2475_ = lean_usize_of_nat(v___x_2466_);
                                    v___x_2476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_2465_, v___x_2474_, v___x_2475_, v___x_2471_, v___x_2470_, v_snd_2461_);
                                    leanh::lean_dec(v___x_2470_);
                                    leanh::lean_dec_ref(v___x_2465_);
                                    v___y_2451_ = v___x_2476_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                v___x_2477_ = 0usize;
                                v___x_2478_ = lean_usize_of_nat(v___x_2466_);
                                v___x_2479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_2465_, v___x_2477_, v___x_2478_, v___x_2471_, v___x_2470_, v_snd_2461_);
                                leanh::lean_dec(v___x_2470_);
                                leanh::lean_dec_ref(v___x_2465_);
                                v___y_2451_ = v___x_2479_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_2480_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2480_, 0, v_b_2437_);
                    leanh::lean_ctor_set(v___x_2480_, 1, v___y_2439_);
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
                v_fst_2448_ = leanh::lean_ctor_get(v___y_2447_, 0);
                leanh::lean_inc(v_fst_2448_);
                v_snd_2449_ = leanh::lean_ctor_get(v___y_2447_, 1);
                leanh::lean_inc(v_snd_2449_);
                leanh::lean_dec_ref(v___y_2447_);
                v_fst_2441_ = v_fst_2448_;
                v_snd_2442_ = v_snd_2449_;
                state = 1;
                continue;
            }
            3 => {
                v_snd_2452_ = leanh::lean_ctor_get(v___y_2451_, 1);
                leanh::lean_inc(v_snd_2452_);
                leanh::lean_dec_ref(v___y_2451_);
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
    mut v_stx_2495_: *mut leanh::LeanObject,
    mut v_a_2496_: *mut leanh::LeanObject,
    mut v_a_2497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: u8 = 0;
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: u8 = 0;
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: u8 = 0;
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: u8 = 0;
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: u8 = 0;
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: u8 = 0;
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: u8 = 0;
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: u8 = 0;
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: u8 = 0;
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: u8 = 0;
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: u8 = 0;
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: u8 = 0;
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: u8 = 0;
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: u8 = 0;
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: u8 = 0;
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: u8 = 0;
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: u8 = 0;
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: u8 = 0;
    let mut v___x_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: u8 = 0;
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: u8 = 0;
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: u8 = 0;
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: u8 = 0;
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: u8 = 0;
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: u8 = 0;
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: u8 = 0;
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: u8 = 0;
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: u8 = 0;
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: u8 = 0;
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: u8 = 0;
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: u8 = 0;
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2602_: usize = 0;
    let mut v___x_2603_: usize = 0;
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2629_: usize = 0;
    let mut v___x_2630_: usize = 0;
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_blks_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: u8 = 0;
    let mut v___x_2656_: u8 = 0;
    let mut v___x_2657_: usize = 0;
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: usize = 0;
    let mut v___x_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: u8 = 0;
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2685_: usize = 0;
    let mut v___x_2686_: usize = 0;
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_blks_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: u8 = 0;
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: u8 = 0;
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: usize = 0;
    let mut v___x_2737_: usize = 0;
    let mut v___x_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: usize = 0;
    let mut v___x_2740_: usize = 0;
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2750_: usize = 0;
    let mut v___x_2751_: usize = 0;
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: u8 = 0;
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: u8 = 0;
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: usize = 0;
    let mut v___x_2768_: usize = 0;
    let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: usize = 0;
    let mut v___x_2771_: usize = 0;
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inl_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: u8 = 0;
    let mut v___x_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: u8 = 0;
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: usize = 0;
    let mut v___x_2786_: usize = 0;
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: usize = 0;
    let mut v___x_2789_: usize = 0;
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inl_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: u8 = 0;
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: u8 = 0;
    let mut v___x_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: usize = 0;
    let mut v___x_2811_: usize = 0;
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: usize = 0;
    let mut v___x_2814_: usize = 0;
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: u8 = 0;
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk3_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: u8 = 0;
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk3_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2974_: usize = 0;
    let mut v___x_2975_: usize = 0;
    let mut v___x_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inls_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: u8 = 0;
    let mut v___x_2987_: u8 = 0;
    let mut v___x_2988_: usize = 0;
    let mut v___x_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: usize = 0;
    let mut v___x_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inl_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: u8 = 0;
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: u8 = 0;
    let mut v___x_3040_: usize = 0;
    let mut v___x_3041_: usize = 0;
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: usize = 0;
    let mut v___x_3044_: usize = 0;
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inl_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: u8 = 0;
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: u8 = 0;
    let mut v___x_3067_: usize = 0;
    let mut v___x_3068_: usize = 0;
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: usize = 0;
    let mut v___x_3071_: usize = 0;
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk1_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk2_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inl_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: u8 = 0;
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: u8 = 0;
    let mut v___x_3094_: usize = 0;
    let mut v___x_3095_: usize = 0;
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: usize = 0;
    let mut v___x_3098_: usize = 0;
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: u8 = 0;
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: u8 = 0;
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: u8 = 0;
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: u8 = 0;
    let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: u8 = 0;
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: u8 = 0;
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: u8 = 0;
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: u8 = 0;
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: u8 = 0;
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: usize = 0;
    let mut v___x_3231_: usize = 0;
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: usize = 0;
    let mut v___x_3234_: usize = 0;
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_stx_2495_);
                v___x_2521_ = l_Lean_Syntax_getKind(v_stx_2495_);
                v___x_2522_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__2;
                v___x_2523_ = lean_name_eq(v___x_2521_, v___x_2522_);
                leanh::lean_dec(v___x_2521_);
                if v___x_2523_ == 0 {
                    v___x_2524_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4;
                    leanh::lean_inc(v_stx_2495_);
                    v___x_2525_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2524_);
                    if v___x_2525_ == 0 {
                        v___x_2526_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6;
                        leanh::lean_inc(v_stx_2495_);
                        v___x_2527_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2526_);
                        if v___x_2527_ == 0 {
                            v___x_2528_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8;
                            leanh::lean_inc(v_stx_2495_);
                            v___x_2529_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2528_);
                            if v___x_2529_ == 0 {
                                v___x_2530_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10;
                                leanh::lean_inc(v_stx_2495_);
                                v___x_2531_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2530_);
                                if v___x_2531_ == 0 {
                                    v___x_2532_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12;
                                    leanh::lean_inc(v_stx_2495_);
                                    v___x_2533_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2532_);
                                    if v___x_2533_ == 0 {
                                        v___x_2534_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14;
                                        leanh::lean_inc(v_stx_2495_);
                                        v___x_2535_ =
                                            l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2534_);
                                        if v___x_2535_ == 0 {
                                            v___x_2536_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__16;
                                            leanh::lean_inc(v_stx_2495_);
                                            v___x_2537_ =
                                                l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2536_);
                                            if v___x_2537_ == 0 {
                                                v___x_2538_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__18;
                                                leanh::lean_inc(v_stx_2495_);
                                                v___x_2539_ = l_Lean_Syntax_isOfKind(
                                                    v_stx_2495_,
                                                    v___x_2538_,
                                                );
                                                if v___x_2539_ == 0 {
                                                    v___x_2540_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__20;
                                                    leanh::lean_inc(v_stx_2495_);
                                                    v___x_2541_ = l_Lean_Syntax_isOfKind(
                                                        v_stx_2495_,
                                                        v___x_2540_,
                                                    );
                                                    if v___x_2541_ == 0 {
                                                        v___x_2542_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__22;
                                                        leanh::lean_inc(v_stx_2495_);
                                                        v___x_2543_ = l_Lean_Syntax_isOfKind(
                                                            v_stx_2495_,
                                                            v___x_2542_,
                                                        );
                                                        if v___x_2543_ == 0 {
                                                            v___x_2544_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__24;
                                                            leanh::lean_inc(v_stx_2495_);
                                                            v___x_2545_ = l_Lean_Syntax_isOfKind(
                                                                v_stx_2495_,
                                                                v___x_2544_,
                                                            );
                                                            if v___x_2545_ == 0 {
                                                                v___x_2546_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__26;
                                                                leanh::lean_inc(v_stx_2495_);
                                                                v___x_2547_ =
                                                                    l_Lean_Syntax_isOfKind(
                                                                        v_stx_2495_,
                                                                        v___x_2546_,
                                                                    );
                                                                if v___x_2547_ == 0 {
                                                                    v___x_2548_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__28;
                                                                    leanh::lean_inc(
                                                                        v_stx_2495_,
                                                                    );
                                                                    v___x_2549_ =
                                                                        l_Lean_Syntax_isOfKind(
                                                                            v_stx_2495_,
                                                                            v___x_2548_,
                                                                        );
                                                                    if v___x_2549_ == 0 {
                                                                        v___x_2550_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__30;
                                                                        leanh::lean_inc(
                                                                            v_stx_2495_,
                                                                        );
                                                                        v___x_2551_ =
                                                                            l_Lean_Syntax_isOfKind(
                                                                                v_stx_2495_,
                                                                                v___x_2550_,
                                                                            );
                                                                        if v___x_2551_ == 0 {
                                                                            v___x_2552_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__32;
                                                                            leanh::lean_inc(
                                                                                v_stx_2495_,
                                                                            );
                                                                            v___x_2553_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2552_);
                                                                            if v___x_2553_ == 0 {
                                                                                v___x_2554_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__34;
                                                                                leanh::lean_inc(v_stx_2495_);
                                                                                v___x_2555_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2554_);
                                                                                if v___x_2555_ == 0
                                                                                {
                                                                                    v___x_2556_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__36;
                                                                                    leanh::lean_inc(v_stx_2495_);
                                                                                    v___x_2557_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2556_);
                                                                                    if v___x_2557_
                                                                                        == 0
                                                                                    {
                                                                                        v___x_2558_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__38;
                                                                                        leanh::lean_inc(v_stx_2495_);
                                                                                        v___x_2559_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2558_);
                                                                                        if v___x_2559_ == 0 {
v___x_2560_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__40;
leanh::lean_inc(v_stx_2495_);
v___x_2561_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2560_);
if v___x_2561_ == 0 {
v___x_2562_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__42;
leanh::lean_inc(v_stx_2495_);
v___x_2563_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2562_);
if v___x_2563_ == 0 {
v___x_2564_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__44;
leanh::lean_inc(v_stx_2495_);
v___x_2565_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2564_);
if v___x_2565_ == 0 {
v___x_2566_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__46;
leanh::lean_inc(v_stx_2495_);
v___x_2567_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2566_);
if v___x_2567_ == 0 {
v___x_2568_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__48;
leanh::lean_inc(v_stx_2495_);
v___x_2569_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2568_);
if v___x_2569_ == 0 {
v___x_2570_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__50;
leanh::lean_inc(v_stx_2495_);
v___x_2571_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2570_);
if v___x_2571_ == 0 {
v___x_2572_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__52;
leanh::lean_inc(v_stx_2495_);
v___x_2573_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2572_);
if v___x_2573_ == 0 {
v___x_2574_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__54;
leanh::lean_inc(v_stx_2495_);
v___x_2575_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2574_);
if v___x_2575_ == 0 {
v___x_2576_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__56;
leanh::lean_inc(v_stx_2495_);
v___x_2577_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2576_);
if v___x_2577_ == 0 {
v___x_2578_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__58;
leanh::lean_inc(v_stx_2495_);
v___x_2579_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2578_);
if v___x_2579_ == 0 {
v___x_2580_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__60;
leanh::lean_inc(v_stx_2495_);
v___x_2581_ = l_Lean_Syntax_isOfKind(v_stx_2495_, v___x_2580_);
if v___x_2581_ == 0 {
v___x_2582_ = leanh::lean_box(0);
v___x_2583_ = l_Lean_Syntax_formatStx(v_stx_2495_, v___x_2582_, v___x_2581_);
v___x_2584_ = l_Std_Format_defWidth;
v___x_2585_ = leanh::lean_unsigned_to_nat(0);
v___x_2586_ = l_Std_Format_pretty(v___x_2583_, v___x_2584_, v___x_2585_, v___x_2585_);
v___x_2587_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2586_, v_a_2497_);
leanh::lean_dec_ref(v___x_2586_);
return v___x_2587_;
} else {
v___x_2588_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_2496_, v_a_2497_);
v_snd_2589_ = leanh::lean_ctor_get(v___x_2588_, 1);
leanh::lean_inc(v_snd_2589_);
leanh::lean_dec_ref(v___x_2588_);
v___x_2590_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__61;
v___x_2591_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2590_, v_snd_2589_);
v_snd_2592_ = leanh::lean_ctor_get(v___x_2591_, 1);
leanh::lean_inc(v_snd_2592_);
leanh::lean_dec_ref(v___x_2591_);
v___x_2593_ = leanh::lean_unsigned_to_nat(1);
v___x_2594_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2593_);
v___x_2595_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_2594_);
v___x_2596_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2595_, v_snd_2592_);
leanh::lean_dec_ref(v___x_2595_);
v_snd_2597_ = leanh::lean_ctor_get(v___x_2596_, 1);
leanh::lean_inc(v_snd_2597_);
leanh::lean_dec_ref(v___x_2596_);
v___x_2598_ = leanh::lean_unsigned_to_nat(2);
v___x_2599_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2598_);
leanh::lean_dec(v_stx_2495_);
v_args_2600_ = l_Lean_Syntax_getArgs(v___x_2599_);
leanh::lean_dec(v___x_2599_);
v___x_2601_ = leanh::lean_box(0);
v_sz_2602_ = lean_array_size(v_args_2600_);
v___x_2603_ = 0usize;
v___x_2604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(v_args_2600_, v_sz_2602_, v___x_2603_, v___x_2601_, v_a_2496_, v_snd_2597_);
leanh::lean_dec_ref(v_args_2600_);
v_snd_2605_ = leanh::lean_ctor_get(v___x_2604_, 1);
leanh::lean_inc(v_snd_2605_);
leanh::lean_dec_ref(v___x_2604_);
v___x_2606_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__62;
v___x_2607_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2606_, v_snd_2605_);
v_snd_2608_ = leanh::lean_ctor_get(v___x_2607_, 1);
leanh::lean_inc(v_snd_2608_);
leanh::lean_dec_ref(v___x_2607_);
v___x_2609_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2608_);
return v___x_2609_;
}
} else {
v___x_2610_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_2496_, v_a_2497_);
v_snd_2611_ = leanh::lean_ctor_get(v___x_2610_, 1);
leanh::lean_inc(v_snd_2611_);
leanh::lean_dec_ref(v___x_2610_);
v___x_2612_ = leanh::lean_unsigned_to_nat(0);
v_tk1_2613_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2612_);
v___x_2614_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_2613_);
v___x_2615_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2614_, v_snd_2611_);
leanh::lean_dec_ref(v___x_2614_);
v_snd_2616_ = leanh::lean_ctor_get(v___x_2615_, 1);
leanh::lean_inc(v_snd_2616_);
leanh::lean_dec_ref(v___x_2615_);
v___x_2617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0;
v___x_2618_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2617_, v_snd_2616_);
v_snd_2619_ = leanh::lean_ctor_get(v___x_2618_, 1);
leanh::lean_inc(v_snd_2619_);
leanh::lean_dec_ref(v___x_2618_);
v___x_2620_ = leanh::lean_unsigned_to_nat(1);
v___x_2621_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2620_);
v___x_2622_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_2621_);
v___x_2623_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2622_, v_snd_2619_);
leanh::lean_dec_ref(v___x_2622_);
v_snd_2624_ = leanh::lean_ctor_get(v___x_2623_, 1);
leanh::lean_inc(v_snd_2624_);
leanh::lean_dec_ref(v___x_2623_);
v___x_2625_ = leanh::lean_unsigned_to_nat(2);
v___x_2626_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2625_);
v_args_2627_ = l_Lean_Syntax_getArgs(v___x_2626_);
leanh::lean_dec(v___x_2626_);
v___x_2628_ = leanh::lean_box(0);
v_sz_2629_ = lean_array_size(v_args_2627_);
v___x_2630_ = 0usize;
v___x_2631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__1(v_args_2627_, v_sz_2629_, v___x_2630_, v___x_2628_, v_a_2496_, v_snd_2624_);
leanh::lean_dec_ref(v_args_2627_);
v_snd_2632_ = leanh::lean_ctor_get(v___x_2631_, 1);
leanh::lean_inc(v_snd_2632_);
leanh::lean_dec_ref(v___x_2631_);
v___x_2633_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0;
v___x_2634_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2633_, v_snd_2632_);
v_snd_2635_ = leanh::lean_ctor_get(v___x_2634_, 1);
leanh::lean_inc(v_snd_2635_);
leanh::lean_dec_ref(v___x_2634_);
v___x_2636_ = leanh::lean_unsigned_to_nat(4);
v___x_2637_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2636_);
v___x_2638_ = leanh::lean_unsigned_to_nat(5);
v_tk2_2639_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2638_);
leanh::lean_dec(v_stx_2495_);
v_blks_2653_ = l_Lean_Syntax_getArgs(v___x_2637_);
leanh::lean_dec(v___x_2637_);
v___x_2654_ = lean_array_get_size(v_blks_2653_);
v___x_2655_ = lean_nat_dec_lt(v___x_2612_, v___x_2654_);
if v___x_2655_ == 0 {
leanh::lean_dec_ref(v_blks_2653_);
v_snd_2641_ = v_snd_2635_;
state = 7; continue;
} else {
v___x_2656_ = lean_nat_dec_le(v___x_2654_, v___x_2654_);
if v___x_2656_ == 0 {
if v___x_2655_ == 0 {
leanh::lean_dec_ref(v_blks_2653_);
v_snd_2641_ = v_snd_2635_;
state = 7; continue;
} else {
v___x_2657_ = lean_usize_of_nat(v___x_2654_);
v___x_2658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_blks_2653_, v___x_2630_, v___x_2657_, v___x_2628_, v_a_2496_, v_snd_2635_);
leanh::lean_dec_ref(v_blks_2653_);
v___y_2651_ = v___x_2658_;
state = 8; continue;
}
} else {
v___x_2659_ = lean_usize_of_nat(v___x_2654_);
v___x_2660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_blks_2653_, v___x_2630_, v___x_2659_, v___x_2628_, v_a_2496_, v_snd_2635_);
leanh::lean_dec_ref(v_blks_2653_);
v___y_2651_ = v___x_2660_;
state = 8; continue;
}
}
}
} else {
v___x_2661_ = leanh::lean_unsigned_to_nat(1);
v___x_2662_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2661_);
v___x_2663_ = leanh::lean_unsigned_to_nat(2);
leanh::lean_inc(v___x_2662_);
v___x_2664_ = l_Lean_Syntax_matchesNull(v___x_2662_, v___x_2663_);
if v___x_2664_ == 0 {
leanh::lean_dec(v___x_2662_);
v___x_2665_ = leanh::lean_box(0);
v___x_2666_ = l_Lean_Syntax_formatStx(v_stx_2495_, v___x_2665_, v___x_2664_);
v___x_2667_ = l_Std_Format_defWidth;
v___x_2668_ = leanh::lean_unsigned_to_nat(0);
v___x_2669_ = l_Std_Format_pretty(v___x_2666_, v___x_2667_, v___x_2668_, v___x_2668_);
v___x_2670_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2669_, v_a_2497_);
leanh::lean_dec_ref(v___x_2669_);
return v___x_2670_;
} else {
v___x_2671_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_2496_, v_a_2497_);
v_snd_2672_ = leanh::lean_ctor_get(v___x_2671_, 1);
leanh::lean_inc(v_snd_2672_);
leanh::lean_dec_ref(v___x_2671_);
v___x_2673_ = leanh::lean_unsigned_to_nat(0);
v_tk1_2674_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2673_);
v___x_2675_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_2674_);
v___x_2676_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2675_, v_snd_2672_);
leanh::lean_dec_ref(v___x_2675_);
v_snd_2677_ = leanh::lean_ctor_get(v___x_2676_, 1);
leanh::lean_inc(v_snd_2677_);
leanh::lean_dec_ref(v___x_2676_);
v___x_2678_ = l_Lean_Syntax_getArg(v___x_2662_, v___x_2673_);
v___x_2679_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_2678_);
v___x_2680_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2679_, v_snd_2677_);
leanh::lean_dec_ref(v___x_2679_);
v_snd_2681_ = leanh::lean_ctor_get(v___x_2680_, 1);
leanh::lean_inc(v_snd_2681_);
leanh::lean_dec_ref(v___x_2680_);
v___x_2682_ = l_Lean_Syntax_getArg(v___x_2662_, v___x_2661_);
leanh::lean_dec(v___x_2662_);
v_args_2683_ = l_Lean_Syntax_getArgs(v___x_2682_);
leanh::lean_dec(v___x_2682_);
v___x_2684_ = leanh::lean_box(0);
v_sz_2685_ = lean_array_size(v_args_2683_);
v___x_2686_ = 0usize;
v___x_2687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(v_args_2683_, v_sz_2685_, v___x_2686_, v___x_2684_, v_a_2496_, v_snd_2681_);
leanh::lean_dec_ref(v_args_2683_);
v_snd_2688_ = leanh::lean_ctor_get(v___x_2687_, 1);
leanh::lean_inc(v_snd_2688_);
leanh::lean_dec_ref(v___x_2687_);
v___x_2689_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl___closed__0;
v___x_2690_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2689_, v_snd_2688_);
v_snd_2691_ = leanh::lean_ctor_get(v___x_2690_, 1);
leanh::lean_inc(v_snd_2691_);
leanh::lean_dec_ref(v___x_2690_);
v___x_2692_ = leanh::lean_unsigned_to_nat(3);
v___x_2693_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2692_);
v___x_2694_ = leanh::lean_unsigned_to_nat(4);
v_tk2_2695_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2694_);
leanh::lean_dec(v_stx_2495_);
v___x_2715_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_2693_);
v___x_2716_ = l_Lean_Syntax_decodeStrLit(v___x_2715_);
if leanh::lean_obj_tag(v___x_2716_) == 0 {
v___x_2717_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
v___y_2697_ = v___x_2717_;
state = 9; continue;
} else {
v_val_2718_ = leanh::lean_ctor_get(v___x_2716_, 0);
leanh::lean_inc(v_val_2718_);
leanh::lean_dec_ref_known(v___x_2716_, 1);
v___y_2697_ = v_val_2718_;
state = 9; continue;
}
}
}
} else {
v___x_2719_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_2496_, v_a_2497_);
v_snd_2720_ = leanh::lean_ctor_get(v___x_2719_, 1);
leanh::lean_inc(v_snd_2720_);
leanh::lean_dec_ref(v___x_2719_);
v___x_2721_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__64;
v___x_2722_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2721_, v_snd_2720_);
v_snd_2723_ = leanh::lean_ctor_get(v___x_2722_, 1);
leanh::lean_inc(v_snd_2723_);
leanh::lean_dec_ref(v___x_2722_);
v___x_2724_ = leanh::lean_unsigned_to_nat(0);
v___x_2725_ = leanh::lean_unsigned_to_nat(1);
v___x_2726_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2725_);
leanh::lean_dec(v_stx_2495_);
v_blks_2727_ = l_Lean_Syntax_getArgs(v___x_2726_);
leanh::lean_dec(v___x_2726_);
v___x_2728_ = lean_array_get_size(v_blks_2727_);
v___x_2729_ = lean_nat_dec_lt(v___x_2724_, v___x_2728_);
if v___x_2729_ == 0 {
leanh::lean_dec_ref(v_blks_2727_);
v___x_2730_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2723_);
return v___x_2730_;
} else {
v___x_2731_ = leanh::lean_unsigned_to_nat(2);
v___x_2732_ = lean_nat_add(v_a_2496_, v___x_2731_);
v___x_2733_ = leanh::lean_box(0);
v___x_2734_ = lean_nat_dec_le(v___x_2728_, v___x_2728_);
if v___x_2734_ == 0 {
if v___x_2729_ == 0 {
leanh::lean_dec(v___x_2732_);
leanh::lean_dec_ref(v_blks_2727_);
v___x_2735_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2723_);
return v___x_2735_;
} else {
v___x_2736_ = 0usize;
v___x_2737_ = lean_usize_of_nat(v___x_2728_);
v___x_2738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_blks_2727_, v___x_2736_, v___x_2737_, v___x_2733_, v___x_2732_, v_snd_2723_);
leanh::lean_dec(v___x_2732_);
leanh::lean_dec_ref(v_blks_2727_);
v___y_2518_ = v___x_2738_;
state = 6; continue;
}
} else {
v___x_2739_ = 0usize;
v___x_2740_ = lean_usize_of_nat(v___x_2728_);
v___x_2741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_blks_2727_, v___x_2739_, v___x_2740_, v___x_2733_, v___x_2732_, v_snd_2723_);
leanh::lean_dec(v___x_2732_);
leanh::lean_dec_ref(v_blks_2727_);
v___y_2518_ = v___x_2741_;
state = 6; continue;
}
}
}
} else {
v___x_2742_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_2496_, v_a_2497_);
v_snd_2743_ = leanh::lean_ctor_get(v___x_2742_, 1);
leanh::lean_inc(v_snd_2743_);
leanh::lean_dec_ref(v___x_2742_);
v___x_2744_ = leanh::lean_unsigned_to_nat(1);
v_n_2745_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2744_);
v___x_2746_ = leanh::lean_unsigned_to_nat(4);
v___x_2747_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2746_);
leanh::lean_dec(v_stx_2495_);
v_items_2748_ = l_Lean_Syntax_getArgs(v___x_2747_);
leanh::lean_dec(v___x_2747_);
v___x_2749_ = l_Lean_TSyntax_getNat(v_n_2745_);
leanh::lean_dec(v_n_2745_);
v_sz_2750_ = lean_array_size(v_items_2748_);
v___x_2751_ = 0usize;
v___x_2752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(v_items_2748_, v_sz_2750_, v___x_2751_, v___x_2749_, v_a_2496_, v_snd_2743_);
leanh::lean_dec_ref(v_items_2748_);
v_snd_2753_ = leanh::lean_ctor_get(v___x_2752_, 1);
leanh::lean_inc(v_snd_2753_);
leanh::lean_dec_ref(v___x_2752_);
v___x_2754_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2753_);
return v___x_2754_;
}
} else {
v___x_2755_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_2496_, v_a_2497_);
v_snd_2756_ = leanh::lean_ctor_get(v___x_2755_, 1);
leanh::lean_inc(v_snd_2756_);
leanh::lean_dec_ref(v___x_2755_);
v___x_2757_ = leanh::lean_unsigned_to_nat(0);
v___x_2758_ = leanh::lean_unsigned_to_nat(1);
v___x_2759_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2758_);
leanh::lean_dec(v_stx_2495_);
v_items_2760_ = l_Lean_Syntax_getArgs(v___x_2759_);
leanh::lean_dec(v___x_2759_);
v___x_2761_ = lean_array_get_size(v_items_2760_);
v___x_2762_ = lean_nat_dec_lt(v___x_2757_, v___x_2761_);
if v___x_2762_ == 0 {
leanh::lean_dec_ref(v_items_2760_);
v___x_2763_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2756_);
return v___x_2763_;
} else {
v___x_2764_ = leanh::lean_box(0);
v___x_2765_ = lean_nat_dec_le(v___x_2761_, v___x_2761_);
if v___x_2765_ == 0 {
if v___x_2762_ == 0 {
leanh::lean_dec_ref(v_items_2760_);
v___x_2766_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2756_);
return v___x_2766_;
} else {
v___x_2767_ = 0usize;
v___x_2768_ = lean_usize_of_nat(v___x_2761_);
v___x_2769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v_items_2760_, v___x_2767_, v___x_2768_, v___x_2764_, v_a_2496_, v_snd_2756_);
leanh::lean_dec_ref(v_items_2760_);
v___y_2514_ = v___x_2769_;
state = 5; continue;
}
} else {
v___x_2770_ = 0usize;
v___x_2771_ = lean_usize_of_nat(v___x_2761_);
v___x_2772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v_items_2760_, v___x_2770_, v___x_2771_, v___x_2764_, v_a_2496_, v_snd_2756_);
leanh::lean_dec_ref(v_items_2760_);
v___y_2514_ = v___x_2772_;
state = 5; continue;
}
}
}
} else {
v___x_2773_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_startBlock(v_a_2496_, v_a_2497_);
v_snd_2774_ = leanh::lean_ctor_get(v___x_2773_, 1);
leanh::lean_inc(v_snd_2774_);
leanh::lean_dec_ref(v___x_2773_);
v___x_2775_ = leanh::lean_unsigned_to_nat(0);
v___x_2776_ = leanh::lean_unsigned_to_nat(1);
v___x_2777_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2776_);
leanh::lean_dec(v_stx_2495_);
v_inl_2778_ = l_Lean_Syntax_getArgs(v___x_2777_);
leanh::lean_dec(v___x_2777_);
v___x_2779_ = lean_array_get_size(v_inl_2778_);
v___x_2780_ = lean_nat_dec_lt(v___x_2775_, v___x_2779_);
if v___x_2780_ == 0 {
leanh::lean_dec_ref(v_inl_2778_);
v___x_2781_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2774_);
return v___x_2781_;
} else {
v___x_2782_ = leanh::lean_box(0);
v___x_2783_ = lean_nat_dec_le(v___x_2779_, v___x_2779_);
if v___x_2783_ == 0 {
if v___x_2780_ == 0 {
leanh::lean_dec_ref(v_inl_2778_);
v___x_2784_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2774_);
return v___x_2784_;
} else {
v___x_2785_ = 0usize;
v___x_2786_ = lean_usize_of_nat(v___x_2779_);
v___x_2787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_2778_, v___x_2785_, v___x_2786_, v___x_2782_, v_a_2496_, v_snd_2774_);
leanh::lean_dec_ref(v_inl_2778_);
v___y_2510_ = v___x_2787_;
state = 4; continue;
}
} else {
v___x_2788_ = 0usize;
v___x_2789_ = lean_usize_of_nat(v___x_2779_);
v___x_2790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_2778_, v___x_2788_, v___x_2789_, v___x_2782_, v_a_2496_, v_snd_2774_);
leanh::lean_dec_ref(v_inl_2778_);
v___y_2510_ = v___x_2790_;
state = 4; continue;
}
}
}
} else {
v___x_2791_ = leanh::lean_unsigned_to_nat(1);
v_n_2792_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2791_);
v___x_2793_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__65;
v___x_2794_ = l_Lean_TSyntax_getNat(v_n_2792_);
leanh::lean_dec(v_n_2792_);
v___x_2795_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(v___x_2794_, v___x_2793_);
v___x_2796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___closed__0;
v___x_2797_ = lean_string_append(v___x_2795_, v___x_2796_);
v___x_2798_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2797_, v_a_2497_);
leanh::lean_dec_ref(v___x_2797_);
v_snd_2799_ = leanh::lean_ctor_get(v___x_2798_, 1);
leanh::lean_inc(v_snd_2799_);
leanh::lean_dec_ref(v___x_2798_);
v___x_2800_ = leanh::lean_unsigned_to_nat(0);
v___x_2801_ = leanh::lean_unsigned_to_nat(4);
v___x_2802_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2801_);
leanh::lean_dec(v_stx_2495_);
v_inl_2803_ = l_Lean_Syntax_getArgs(v___x_2802_);
leanh::lean_dec(v___x_2802_);
v___x_2804_ = lean_array_get_size(v_inl_2803_);
v___x_2805_ = lean_nat_dec_lt(v___x_2800_, v___x_2804_);
if v___x_2805_ == 0 {
leanh::lean_dec_ref(v_inl_2803_);
v___x_2806_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2799_);
return v___x_2806_;
} else {
v___x_2807_ = leanh::lean_box(0);
v___x_2808_ = lean_nat_dec_le(v___x_2804_, v___x_2804_);
if v___x_2808_ == 0 {
if v___x_2805_ == 0 {
leanh::lean_dec_ref(v_inl_2803_);
v___x_2809_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2799_);
return v___x_2809_;
} else {
v___x_2810_ = 0usize;
v___x_2811_ = lean_usize_of_nat(v___x_2804_);
v___x_2812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_2803_, v___x_2810_, v___x_2811_, v___x_2807_, v_a_2496_, v_snd_2799_);
leanh::lean_dec_ref(v_inl_2803_);
v___y_2506_ = v___x_2812_;
state = 3; continue;
}
} else {
v___x_2813_ = 0usize;
v___x_2814_ = lean_usize_of_nat(v___x_2804_);
v___x_2815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_2803_, v___x_2813_, v___x_2814_, v___x_2807_, v_a_2496_, v_snd_2799_);
leanh::lean_dec_ref(v_inl_2803_);
v___y_2506_ = v___x_2815_;
state = 3; continue;
}
}
}
} else {
v___x_2816_ = leanh::lean_unsigned_to_nat(0);
v_tk1_2817_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2816_);
v___x_2818_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_2817_);
v___x_2819_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2818_, v_a_2497_);
leanh::lean_dec_ref(v___x_2818_);
v_snd_2820_ = leanh::lean_ctor_get(v___x_2819_, 1);
leanh::lean_inc(v_snd_2820_);
leanh::lean_dec_ref(v___x_2819_);
v___x_2821_ = leanh::lean_unsigned_to_nat(1);
v___x_2822_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2821_);
v___x_2823_ = leanh::lean_unsigned_to_nat(2);
v_tk2_2824_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2823_);
leanh::lean_dec(v_stx_2495_);
v___x_2831_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_2822_);
v___x_2832_ = l_Lean_Syntax_decodeStrLit(v___x_2831_);
if leanh::lean_obj_tag(v___x_2832_) == 0 {
v___x_2833_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
v___y_2826_ = v___x_2833_;
state = 10; continue;
} else {
v_val_2834_ = leanh::lean_ctor_get(v___x_2832_, 0);
leanh::lean_inc(v_val_2834_);
leanh::lean_dec_ref_known(v___x_2832_, 1);
v___y_2826_ = v_val_2834_;
state = 10; continue;
}
}
} else {
v___x_2835_ = leanh::lean_unsigned_to_nat(0);
v_tk1_2836_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2835_);
v___x_2837_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_2836_);
v___x_2838_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2837_, v_a_2497_);
leanh::lean_dec_ref(v___x_2837_);
v_snd_2839_ = leanh::lean_ctor_get(v___x_2838_, 1);
leanh::lean_inc(v_snd_2839_);
leanh::lean_dec_ref(v___x_2838_);
v___x_2840_ = leanh::lean_unsigned_to_nat(1);
v___x_2841_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2840_);
v___x_2842_ = leanh::lean_unsigned_to_nat(2);
v_tk2_2843_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2842_);
leanh::lean_dec(v_stx_2495_);
v___x_2850_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_2841_);
v___x_2851_ = l_Lean_Syntax_decodeStrLit(v___x_2850_);
if leanh::lean_obj_tag(v___x_2851_) == 0 {
v___x_2852_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
v___y_2845_ = v___x_2852_;
state = 11; continue;
} else {
v_val_2853_ = leanh::lean_ctor_get(v___x_2851_, 0);
leanh::lean_inc(v_val_2853_);
leanh::lean_dec_ref_known(v___x_2851_, 1);
v___y_2845_ = v_val_2853_;
state = 11; continue;
}
}
} else {
v___x_2854_ = leanh::lean_unsigned_to_nat(1);
v___x_2855_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2854_);
leanh::lean_inc(v___x_2855_);
v___x_2856_ = l_Lean_Syntax_isOfKind(v___x_2855_, v___x_2552_);
if v___x_2856_ == 0 {
leanh::lean_dec(v___x_2855_);
v___x_2857_ = leanh::lean_box(0);
v___x_2858_ = l_Lean_Syntax_formatStx(v_stx_2495_, v___x_2857_, v___x_2856_);
v___x_2859_ = l_Std_Format_defWidth;
v___x_2860_ = leanh::lean_unsigned_to_nat(0);
v___x_2861_ = l_Std_Format_pretty(v___x_2858_, v___x_2859_, v___x_2860_, v___x_2860_);
v___x_2862_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2861_, v_a_2497_);
leanh::lean_dec_ref(v___x_2861_);
return v___x_2862_;
} else {
v___x_2863_ = leanh::lean_unsigned_to_nat(0);
v_tk1_2864_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2863_);
leanh::lean_dec(v_stx_2495_);
v___x_2865_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_2864_);
v___x_2866_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2865_, v_a_2497_);
leanh::lean_dec_ref(v___x_2865_);
v_snd_2867_ = leanh::lean_ctor_get(v___x_2866_, 1);
leanh::lean_inc(v_snd_2867_);
leanh::lean_dec_ref(v___x_2866_);
v_tk2_2868_ = l_Lean_Syntax_getArg(v___x_2855_, v___x_2863_);
v___x_2869_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_2868_);
v___x_2870_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2869_, v_snd_2867_);
leanh::lean_dec_ref(v___x_2869_);
v_snd_2871_ = leanh::lean_ctor_get(v___x_2870_, 1);
leanh::lean_inc(v_snd_2871_);
leanh::lean_dec_ref(v___x_2870_);
v___x_2872_ = l_Lean_Syntax_getArg(v___x_2855_, v___x_2854_);
v___x_2873_ = leanh::lean_unsigned_to_nat(2);
v_tk3_2874_ = l_Lean_Syntax_getArg(v___x_2855_, v___x_2873_);
leanh::lean_dec(v___x_2855_);
v___x_2881_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_2872_);
v___x_2882_ = l_Lean_Syntax_decodeStrLit(v___x_2881_);
if leanh::lean_obj_tag(v___x_2882_) == 0 {
v___x_2883_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
v___y_2876_ = v___x_2883_;
state = 12; continue;
} else {
v_val_2884_ = leanh::lean_ctor_get(v___x_2882_, 0);
leanh::lean_inc(v_val_2884_);
leanh::lean_dec_ref_known(v___x_2882_, 1);
v___y_2876_ = v_val_2884_;
state = 12; continue;
}
}
}
} else {
v___x_2885_ = leanh::lean_unsigned_to_nat(1);
v___x_2886_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2885_);
leanh::lean_inc(v___x_2886_);
v___x_2887_ = l_Lean_Syntax_isOfKind(v___x_2886_, v___x_2552_);
if v___x_2887_ == 0 {
leanh::lean_dec(v___x_2886_);
v___x_2888_ = leanh::lean_box(0);
v___x_2889_ = l_Lean_Syntax_formatStx(v_stx_2495_, v___x_2888_, v___x_2887_);
v___x_2890_ = l_Std_Format_defWidth;
v___x_2891_ = leanh::lean_unsigned_to_nat(0);
v___x_2892_ = l_Std_Format_pretty(v___x_2889_, v___x_2890_, v___x_2891_, v___x_2891_);
v___x_2893_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2892_, v_a_2497_);
leanh::lean_dec_ref(v___x_2892_);
return v___x_2893_;
} else {
v___x_2894_ = leanh::lean_unsigned_to_nat(0);
v_tk1_2895_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2894_);
leanh::lean_dec(v_stx_2495_);
v___x_2896_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_2895_);
v___x_2897_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2896_, v_a_2497_);
leanh::lean_dec_ref(v___x_2896_);
v_snd_2898_ = leanh::lean_ctor_get(v___x_2897_, 1);
leanh::lean_inc(v_snd_2898_);
leanh::lean_dec_ref(v___x_2897_);
v_tk2_2899_ = l_Lean_Syntax_getArg(v___x_2886_, v___x_2894_);
v___x_2900_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_2899_);
v___x_2901_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2900_, v_snd_2898_);
leanh::lean_dec_ref(v___x_2900_);
v_snd_2902_ = leanh::lean_ctor_get(v___x_2901_, 1);
leanh::lean_inc(v_snd_2902_);
leanh::lean_dec_ref(v___x_2901_);
v___x_2903_ = l_Lean_Syntax_getArg(v___x_2886_, v___x_2885_);
v___x_2904_ = leanh::lean_unsigned_to_nat(2);
v_tk3_2905_ = l_Lean_Syntax_getArg(v___x_2886_, v___x_2904_);
leanh::lean_dec(v___x_2886_);
v___x_2912_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_2903_);
v___x_2913_ = l_Lean_Syntax_decodeStrLit(v___x_2912_);
if leanh::lean_obj_tag(v___x_2913_) == 0 {
v___x_2914_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
v___y_2907_ = v___x_2914_;
state = 13; continue;
} else {
v_val_2915_ = leanh::lean_ctor_get(v___x_2913_, 0);
leanh::lean_inc(v_val_2915_);
leanh::lean_dec_ref_known(v___x_2913_, 1);
v___y_2907_ = v_val_2915_;
state = 13; continue;
}
}
}
                                                                                    } else {
                                                                                        v___x_2916_ = leanh::lean_unsigned_to_nat(1);
                                                                                        v___x_2917_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2916_);
                                                                                        leanh::lean_dec(v_stx_2495_);
                                                                                        v___x_2918_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_2917_);
                                                                                        v___x_2919_ = l_Lean_Syntax_decodeStrLit(v___x_2918_);
                                                                                        if leanh::lean_obj_tag(v___x_2919_) == 0 {
v___x_2920_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
v___x_2921_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2920_, v_a_2497_);
return v___x_2921_;
} else {
v_val_2922_ = leanh::lean_ctor_get(v___x_2919_, 0);
leanh::lean_inc(v_val_2922_);
leanh::lean_dec_ref_known(v___x_2919_, 1);
v___x_2923_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v_val_2922_, v_a_2497_);
leanh::lean_dec(v_val_2922_);
return v___x_2923_;
}
                                                                                    }
                                                                                } else {
                                                                                    v___x_2924_ = leanh::lean_unsigned_to_nat(0);
                                                                                    v_tk1_2925_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2924_);
                                                                                    v___x_2926_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_2925_);
                                                                                    v___x_2927_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2926_, v_a_2497_);
                                                                                    leanh::lean_dec_ref(v___x_2926_);
                                                                                    v_snd_2928_ = leanh::lean_ctor_get(v___x_2927_, 1);
                                                                                    leanh::lean_inc(v_snd_2928_);
                                                                                    leanh::lean_dec_ref(v___x_2927_);
                                                                                    v___x_2929_ = leanh::lean_unsigned_to_nat(1);
                                                                                    v___x_2930_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2929_);
                                                                                    v___x_2931_ = leanh::lean_unsigned_to_nat(2);
                                                                                    v_tk2_2932_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2931_);
                                                                                    leanh::lean_dec(v_stx_2495_);
                                                                                    v___x_2939_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_2930_);
                                                                                    v___x_2940_ = l_Lean_Syntax_decodeStrLit(v___x_2939_);
                                                                                    if leanh::lean_obj_tag(v___x_2940_) == 0 {
v___x_2941_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
v___y_2934_ = v___x_2941_;
state = 14; continue;
} else {
v_val_2942_ = leanh::lean_ctor_get(v___x_2940_, 0);
leanh::lean_inc(v_val_2942_);
leanh::lean_dec_ref_known(v___x_2940_, 1);
v___y_2934_ = v_val_2942_;
state = 14; continue;
}
                                                                                }
                                                                            } else {
                                                                                v___x_2943_ = leanh::lean_unsigned_to_nat(0);
                                                                                v_tk1_2944_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2943_);
                                                                                v___x_2945_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_2944_);
                                                                                v___x_2946_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2945_, v_a_2497_);
                                                                                leanh::lean_dec_ref(v___x_2945_);
                                                                                v_snd_2947_ = leanh::lean_ctor_get(v___x_2946_, 1);
                                                                                leanh::lean_inc(v_snd_2947_);
                                                                                leanh::lean_dec_ref(v___x_2946_);
                                                                                v___x_2948_ = leanh::lean_unsigned_to_nat(1);
                                                                                v___x_2949_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2948_);
                                                                                v___x_2950_ = leanh::lean_unsigned_to_nat(2);
                                                                                v_tk2_2951_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2950_);
                                                                                leanh::lean_dec(v_stx_2495_);
                                                                                v___x_2958_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_2949_);
                                                                                v___x_2959_ = l_Lean_Syntax_decodeStrLit(v___x_2958_);
                                                                                if leanh::lean_obj_tag(v___x_2959_) == 0 {
v___x_2960_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
v___y_2953_ = v___x_2960_;
state = 15; continue;
} else {
v_val_2961_ = leanh::lean_ctor_get(v___x_2959_, 0);
leanh::lean_inc(v_val_2961_);
leanh::lean_dec_ref_known(v___x_2959_, 1);
v___y_2953_ = v_val_2961_;
state = 15; continue;
}
                                                                            }
                                                                        } else {
                                                                            v___x_2962_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__61;
                                                                            v___x_2963_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2962_, v_a_2497_);
                                                                            v_snd_2964_ = leanh::lean_ctor_get(v___x_2963_, 1);
                                                                            leanh::lean_inc(
                                                                                v_snd_2964_,
                                                                            );
                                                                            leanh::lean_dec_ref(v___x_2963_);
                                                                            v___x_2965_ = leanh::lean_unsigned_to_nat(1);
                                                                            v___x_2966_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2965_);
                                                                            v___x_2967_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_2966_);
                                                                            v___x_2968_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2967_, v_snd_2964_);
                                                                            leanh::lean_dec_ref(v___x_2967_);
                                                                            v_snd_2969_ = leanh::lean_ctor_get(v___x_2968_, 1);
                                                                            leanh::lean_inc(
                                                                                v_snd_2969_,
                                                                            );
                                                                            leanh::lean_dec_ref(v___x_2968_);
                                                                            v___x_2970_ = leanh::lean_unsigned_to_nat(2);
                                                                            v___x_2971_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2970_);
                                                                            v_args_2972_ = l_Lean_Syntax_getArgs(v___x_2971_);
                                                                            leanh::lean_dec(
                                                                                v___x_2971_,
                                                                            );
                                                                            v___x_2973_ = leanh::lean_box(0);
                                                                            v_sz_2974_ =
                                                                                lean_array_size(
                                                                                    v_args_2972_,
                                                                                );
                                                                            v___x_2975_ = 0usize;
                                                                            v___x_2976_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(v_args_2972_, v_sz_2974_, v___x_2975_, v___x_2973_, v_a_2496_, v_snd_2969_);
                                                                            leanh::lean_dec_ref(v_args_2972_);
                                                                            v_snd_2977_ = leanh::lean_ctor_get(v___x_2976_, 1);
                                                                            leanh::lean_inc(
                                                                                v_snd_2977_,
                                                                            );
                                                                            leanh::lean_dec_ref(v___x_2976_);
                                                                            v___x_2978_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__66;
                                                                            v___x_2979_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2978_, v_snd_2977_);
                                                                            v_snd_2980_ = leanh::lean_ctor_get(v___x_2979_, 1);
                                                                            leanh::lean_inc(
                                                                                v_snd_2980_,
                                                                            );
                                                                            leanh::lean_dec_ref(v___x_2979_);
                                                                            v___x_2981_ = leanh::lean_unsigned_to_nat(0);
                                                                            v___x_2982_ = leanh::lean_unsigned_to_nat(5);
                                                                            v___x_2983_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_2982_);
                                                                            leanh::lean_dec(
                                                                                v_stx_2495_,
                                                                            );
                                                                            v_inls_2984_ = l_Lean_Syntax_getArgs(v___x_2983_);
                                                                            leanh::lean_dec(
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
                                                                                leanh::lean_dec_ref(v_inls_2984_);
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
                                                                                        leanh::lean_dec_ref(v_inls_2984_);
                                                                                        v_snd_2499_ = v_snd_2980_;
                                                                                        state = 1;
                                                                                        continue;
                                                                                    } else {
                                                                                        v___x_2988_ = lean_usize_of_nat(v___x_2985_);
                                                                                        v___x_2989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inls_2984_, v___x_2975_, v___x_2988_, v___x_2973_, v_a_2496_, v_snd_2980_);
                                                                                        leanh::lean_dec_ref(v_inls_2984_);
                                                                                        v___y_2503_ = v___x_2989_;
                                                                                        state = 2;
                                                                                        continue;
                                                                                    }
                                                                                } else {
                                                                                    v___x_2990_ = lean_usize_of_nat(v___x_2985_);
                                                                                    v___x_2991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inls_2984_, v___x_2975_, v___x_2990_, v___x_2973_, v_a_2496_, v_snd_2980_);
                                                                                    leanh::lean_dec_ref(v_inls_2984_);
                                                                                    v___y_2503_ =
                                                                                        v___x_2991_;
                                                                                    state = 2;
                                                                                    continue;
                                                                                }
                                                                            }
                                                                        }
                                                                    } else {
                                                                        v___x_2992_ = leanh::lean_unsigned_to_nat(0);
                                                                        v_tk1_2993_ =
                                                                            l_Lean_Syntax_getArg(
                                                                                v_stx_2495_,
                                                                                v___x_2992_,
                                                                            );
                                                                        v___x_2994_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_2993_);
                                                                        v___x_2995_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2994_, v_a_2497_);
                                                                        leanh::lean_dec_ref(
                                                                            v___x_2994_,
                                                                        );
                                                                        v_snd_2996_ = leanh::lean_ctor_get(v___x_2995_, 1);
                                                                        leanh::lean_inc(
                                                                            v_snd_2996_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v___x_2995_,
                                                                        );
                                                                        v___x_2997_ = leanh::lean_unsigned_to_nat(1);
                                                                        v___x_2998_ =
                                                                            l_Lean_Syntax_getArg(
                                                                                v_stx_2495_,
                                                                                v___x_2997_,
                                                                            );
                                                                        v___x_2999_ = leanh::lean_unsigned_to_nat(2);
                                                                        v_tk2_3000_ =
                                                                            l_Lean_Syntax_getArg(
                                                                                v_stx_2495_,
                                                                                v___x_2999_,
                                                                            );
                                                                        v___x_3001_ = leanh::lean_unsigned_to_nat(3);
                                                                        v___x_3002_ =
                                                                            l_Lean_Syntax_getArg(
                                                                                v_stx_2495_,
                                                                                v___x_3001_,
                                                                            );
                                                                        leanh::lean_dec(
                                                                            v_stx_2495_,
                                                                        );
                                                                        v___x_3011_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_2998_);
                                                                        v___x_3012_ = l_Lean_Syntax_decodeStrLit(v___x_3011_);
                                                                        if leanh::lean_obj_tag(v___x_3012_) == 0 {
v___x_3013_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
v___y_3004_ = v___x_3013_;
state = 16; continue;
} else {
v_val_3014_ = leanh::lean_ctor_get(v___x_3012_, 0);
leanh::lean_inc(v_val_3014_);
leanh::lean_dec_ref_known(v___x_3012_, 1);
v___y_3004_ = v_val_3014_;
state = 16; continue;
}
                                                                    }
                                                                } else {
                                                                    v___x_3015_ = leanh::lean_unsigned_to_nat(0);
                                                                    v_tk1_3016_ =
                                                                        l_Lean_Syntax_getArg(
                                                                            v_stx_2495_,
                                                                            v___x_3015_,
                                                                        );
                                                                    v___x_3017_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_3016_);
                                                                    v___x_3018_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3017_, v_a_2497_);
                                                                    leanh::lean_dec_ref(
                                                                        v___x_3017_,
                                                                    );
                                                                    v_snd_3019_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_3018_,
                                                                            1,
                                                                        );
                                                                    leanh::lean_inc(
                                                                        v_snd_3019_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v___x_3018_,
                                                                    );
                                                                    v___x_3020_ = leanh::lean_unsigned_to_nat(1);
                                                                    v___x_3021_ =
                                                                        l_Lean_Syntax_getArg(
                                                                            v_stx_2495_,
                                                                            v___x_3020_,
                                                                        );
                                                                    v___x_3022_ = leanh::lean_unsigned_to_nat(2);
                                                                    v_tk2_3023_ =
                                                                        l_Lean_Syntax_getArg(
                                                                            v_stx_2495_,
                                                                            v___x_3022_,
                                                                        );
                                                                    v___x_3024_ = leanh::lean_unsigned_to_nat(3);
                                                                    v___x_3025_ =
                                                                        l_Lean_Syntax_getArg(
                                                                            v_stx_2495_,
                                                                            v___x_3024_,
                                                                        );
                                                                    leanh::lean_dec(
                                                                        v_stx_2495_,
                                                                    );
                                                                    v_inl_3035_ =
                                                                        l_Lean_Syntax_getArgs(
                                                                            v___x_3021_,
                                                                        );
                                                                    leanh::lean_dec(
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
                                                                        leanh::lean_dec_ref(
                                                                            v_inl_3035_,
                                                                        );
                                                                        v_snd_3027_ = v_snd_3019_;
                                                                        state = 17;
                                                                        continue;
                                                                    } else {
                                                                        v___x_3038_ =
                                                                            leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v___x_3039_ =
                                                                            lean_nat_dec_le(
                                                                                v___x_3036_,
                                                                                v___x_3036_,
                                                                            );
                                                                        if v___x_3039_ == 0 {
                                                                            if v___x_3037_ == 0 {
                                                                                leanh::lean_dec_ref(v_inl_3035_);
                                                                                v_snd_3027_ =
                                                                                    v_snd_3019_;
                                                                                state = 17;
                                                                                continue;
                                                                            } else {
                                                                                v___x_3040_ =
                                                                                    0usize;
                                                                                v___x_3041_ = lean_usize_of_nat(v___x_3036_);
                                                                                v___x_3042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_inl_3035_, v___x_3040_, v___x_3041_, v___x_3038_, v_a_2496_, v_snd_3019_);
                                                                                leanh::lean_dec_ref(v_inl_3035_);
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
                                                                            leanh::lean_dec_ref(v_inl_3035_);
                                                                            v___y_3033_ =
                                                                                v___x_3045_;
                                                                            state = 18;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                v___x_3046_ = leanh::lean_unsigned_to_nat(0);
                                                                v_tk1_3047_ = l_Lean_Syntax_getArg(
                                                                    v_stx_2495_,
                                                                    v___x_3046_,
                                                                );
                                                                v___x_3048_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_3047_);
                                                                v___x_3049_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3048_, v_a_2497_);
                                                                leanh::lean_dec_ref(
                                                                    v___x_3048_,
                                                                );
                                                                v_snd_3050_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_3049_,
                                                                        1,
                                                                    );
                                                                leanh::lean_inc(v_snd_3050_);
                                                                leanh::lean_dec_ref(
                                                                    v___x_3049_,
                                                                );
                                                                v___x_3051_ = leanh::lean_unsigned_to_nat(1);
                                                                v___x_3052_ = l_Lean_Syntax_getArg(
                                                                    v_stx_2495_,
                                                                    v___x_3051_,
                                                                );
                                                                v___x_3053_ = leanh::lean_unsigned_to_nat(2);
                                                                v_tk2_3054_ = l_Lean_Syntax_getArg(
                                                                    v_stx_2495_,
                                                                    v___x_3053_,
                                                                );
                                                                leanh::lean_dec(v_stx_2495_);
                                                                v_inl_3062_ = l_Lean_Syntax_getArgs(
                                                                    v___x_3052_,
                                                                );
                                                                leanh::lean_dec(v___x_3052_);
                                                                v___x_3063_ = lean_array_get_size(
                                                                    v_inl_3062_,
                                                                );
                                                                v___x_3064_ = lean_nat_dec_lt(
                                                                    v___x_3046_,
                                                                    v___x_3063_,
                                                                );
                                                                if v___x_3064_ == 0 {
                                                                    leanh::lean_dec_ref(
                                                                        v_inl_3062_,
                                                                    );
                                                                    v_snd_3056_ = v_snd_3050_;
                                                                    state = 19;
                                                                    continue;
                                                                } else {
                                                                    v___x_3065_ =
                                                                        leanh::lean_box(0);
                                                                    v___x_3066_ = lean_nat_dec_le(
                                                                        v___x_3063_,
                                                                        v___x_3063_,
                                                                    );
                                                                    if v___x_3066_ == 0 {
                                                                        if v___x_3064_ == 0 {
                                                                            leanh::lean_dec_ref(v_inl_3062_);
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
                                                                            leanh::lean_dec_ref(v_inl_3062_);
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
                                                                        leanh::lean_dec_ref(
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
                                                                leanh::lean_unsigned_to_nat(
                                                                    0,
                                                                );
                                                            v_tk1_3074_ = l_Lean_Syntax_getArg(
                                                                v_stx_2495_,
                                                                v___x_3073_,
                                                            );
                                                            v___x_3075_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk1_3074_);
                                                            v___x_3076_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3075_, v_a_2497_);
                                                            leanh::lean_dec_ref(v___x_3075_);
                                                            v_snd_3077_ =
                                                                leanh::lean_ctor_get(
                                                                    v___x_3076_,
                                                                    1,
                                                                );
                                                            leanh::lean_inc(v_snd_3077_);
                                                            leanh::lean_dec_ref(v___x_3076_);
                                                            v___x_3078_ =
                                                                leanh::lean_unsigned_to_nat(
                                                                    1,
                                                                );
                                                            v___x_3079_ = l_Lean_Syntax_getArg(
                                                                v_stx_2495_,
                                                                v___x_3078_,
                                                            );
                                                            v___x_3080_ =
                                                                leanh::lean_unsigned_to_nat(
                                                                    2,
                                                                );
                                                            v_tk2_3081_ = l_Lean_Syntax_getArg(
                                                                v_stx_2495_,
                                                                v___x_3080_,
                                                            );
                                                            leanh::lean_dec(v_stx_2495_);
                                                            v_inl_3089_ =
                                                                l_Lean_Syntax_getArgs(v___x_3079_);
                                                            leanh::lean_dec(v___x_3079_);
                                                            v___x_3090_ =
                                                                lean_array_get_size(v_inl_3089_);
                                                            v___x_3091_ = lean_nat_dec_lt(
                                                                v___x_3073_,
                                                                v___x_3090_,
                                                            );
                                                            if v___x_3091_ == 0 {
                                                                leanh::lean_dec_ref(
                                                                    v_inl_3089_,
                                                                );
                                                                v_snd_3083_ = v_snd_3077_;
                                                                state = 21;
                                                                continue;
                                                            } else {
                                                                v___x_3092_ =
                                                                    leanh::lean_box(0);
                                                                v___x_3093_ = lean_nat_dec_le(
                                                                    v___x_3090_,
                                                                    v___x_3090_,
                                                                );
                                                                if v___x_3093_ == 0 {
                                                                    if v___x_3091_ == 0 {
                                                                        leanh::lean_dec_ref(
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
                                                                        leanh::lean_dec_ref(
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
                                                                    leanh::lean_dec_ref(
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
                                                            leanh::lean_unsigned_to_nat(0);
                                                        v_s_3101_ = l_Lean_Syntax_getArg(
                                                            v_stx_2495_,
                                                            v___x_3100_,
                                                        );
                                                        v___x_3102_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__68;
                                                        leanh::lean_inc(v_s_3101_);
                                                        v___x_3103_ = l_Lean_Syntax_isOfKind(
                                                            v_s_3101_,
                                                            v___x_3102_,
                                                        );
                                                        if v___x_3103_ == 0 {
                                                            leanh::lean_dec(v_s_3101_);
                                                            v___x_3104_ = leanh::lean_box(0);
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
                                                            leanh::lean_dec_ref(v___x_3107_);
                                                            return v___x_3108_;
                                                        } else {
                                                            leanh::lean_dec(v_stx_2495_);
                                                            v___x_3109_ =
                                                                l_Lean_TSyntax_getString(v_s_3101_);
                                                            leanh::lean_dec(v_s_3101_);
                                                            v___x_3110_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3109_, v_a_2497_);
                                                            leanh::lean_dec_ref(v___x_3109_);
                                                            return v___x_3110_;
                                                        }
                                                    }
                                                } else {
                                                    v___x_3111_ =
                                                        leanh::lean_unsigned_to_nat(0);
                                                    v___x_3112_ = l_Lean_Syntax_getArg(
                                                        v_stx_2495_,
                                                        v___x_3111_,
                                                    );
                                                    leanh::lean_dec(v_stx_2495_);
                                                    v_stx_2495_ = v___x_3112_;
                                                    state = 0;
                                                    continue;
                                                }
                                            } else {
                                                v___x_3114_ = leanh::lean_unsigned_to_nat(1);
                                                v___x_3115_ =
                                                    l_Lean_Syntax_getArg(v_stx_2495_, v___x_3114_);
                                                v___x_3116_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70;
                                                leanh::lean_inc(v___x_3115_);
                                                v___x_3117_ = l_Lean_Syntax_isOfKind(
                                                    v___x_3115_,
                                                    v___x_3116_,
                                                );
                                                if v___x_3117_ == 0 {
                                                    leanh::lean_dec(v___x_3115_);
                                                    v___x_3118_ = leanh::lean_box(0);
                                                    v___x_3119_ = l_Lean_Syntax_formatStx(
                                                        v_stx_2495_,
                                                        v___x_3118_,
                                                        v___x_3117_,
                                                    );
                                                    v___x_3120_ = l_Std_Format_defWidth;
                                                    v___x_3121_ =
                                                        leanh::lean_unsigned_to_nat(0);
                                                    v___x_3122_ = l_Std_Format_pretty(
                                                        v___x_3119_,
                                                        v___x_3120_,
                                                        v___x_3121_,
                                                        v___x_3121_,
                                                    );
                                                    v___x_3123_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3122_, v_a_2497_);
                                                    leanh::lean_dec_ref(v___x_3122_);
                                                    return v___x_3123_;
                                                } else {
                                                    v___x_3124_ =
                                                        leanh::lean_unsigned_to_nat(0);
                                                    v_tk_3125_ = l_Lean_Syntax_getArg(
                                                        v_stx_2495_,
                                                        v___x_3124_,
                                                    );
                                                    leanh::lean_dec(v_stx_2495_);
                                                    v___x_3126_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk_3125_);
                                                    v___x_3127_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3126_, v_a_2497_);
                                                    leanh::lean_dec_ref(v___x_3126_);
                                                    v_snd_3128_ =
                                                        leanh::lean_ctor_get(v___x_3127_, 1);
                                                    leanh::lean_inc(v_snd_3128_);
                                                    leanh::lean_dec_ref(v___x_3127_);
                                                    v___x_3129_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_3115_);
                                                    v___x_3130_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3129_, v_snd_3128_);
                                                    leanh::lean_dec_ref(v___x_3129_);
                                                    return v___x_3130_;
                                                }
                                            }
                                        } else {
                                            v___x_3131_ = leanh::lean_unsigned_to_nat(1);
                                            v___x_3132_ =
                                                l_Lean_Syntax_getArg(v_stx_2495_, v___x_3131_);
                                            v___x_3133_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70;
                                            leanh::lean_inc(v___x_3132_);
                                            v___x_3134_ =
                                                l_Lean_Syntax_isOfKind(v___x_3132_, v___x_3133_);
                                            if v___x_3134_ == 0 {
                                                leanh::lean_dec(v___x_3132_);
                                                v___x_3135_ = leanh::lean_box(0);
                                                v___x_3136_ = l_Lean_Syntax_formatStx(
                                                    v_stx_2495_,
                                                    v___x_3135_,
                                                    v___x_3134_,
                                                );
                                                v___x_3137_ = l_Std_Format_defWidth;
                                                v___x_3138_ = leanh::lean_unsigned_to_nat(0);
                                                v___x_3139_ = l_Std_Format_pretty(
                                                    v___x_3136_,
                                                    v___x_3137_,
                                                    v___x_3138_,
                                                    v___x_3138_,
                                                );
                                                v___x_3140_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3139_, v_a_2497_);
                                                leanh::lean_dec_ref(v___x_3139_);
                                                return v___x_3140_;
                                            } else {
                                                v___x_3141_ = leanh::lean_unsigned_to_nat(0);
                                                v_tk_3142_ =
                                                    l_Lean_Syntax_getArg(v_stx_2495_, v___x_3141_);
                                                leanh::lean_dec(v_stx_2495_);
                                                v___x_3143_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk_3142_);
                                                v___x_3144_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3143_, v_a_2497_);
                                                leanh::lean_dec_ref(v___x_3143_);
                                                v_snd_3145_ =
                                                    leanh::lean_ctor_get(v___x_3144_, 1);
                                                leanh::lean_inc(v_snd_3145_);
                                                leanh::lean_dec_ref(v___x_3144_);
                                                v___x_3146_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_3132_);
                                                v___x_3147_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3146_, v_snd_3145_);
                                                leanh::lean_dec_ref(v___x_3146_);
                                                return v___x_3147_;
                                            }
                                        }
                                    } else {
                                        v___x_3148_ = leanh::lean_unsigned_to_nat(0);
                                        v___x_3149_ =
                                            l_Lean_Syntax_getArg(v_stx_2495_, v___x_3148_);
                                        v___x_3150_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70;
                                        leanh::lean_inc(v___x_3149_);
                                        v___x_3151_ =
                                            l_Lean_Syntax_isOfKind(v___x_3149_, v___x_3150_);
                                        if v___x_3151_ == 0 {
                                            leanh::lean_dec(v___x_3149_);
                                            v___x_3152_ = leanh::lean_box(0);
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
                                            leanh::lean_dec_ref(v___x_3155_);
                                            return v___x_3156_;
                                        } else {
                                            v___x_3157_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__71;
                                            v___x_3158_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3157_, v_a_2497_);
                                            v_snd_3159_ =
                                                leanh::lean_ctor_get(v___x_3158_, 1);
                                            leanh::lean_inc(v_snd_3159_);
                                            leanh::lean_dec_ref(v___x_3158_);
                                            v___x_3160_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_3149_);
                                            v___x_3161_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3160_, v_snd_3159_);
                                            leanh::lean_dec_ref(v___x_3160_);
                                            v_snd_3162_ =
                                                leanh::lean_ctor_get(v___x_3161_, 1);
                                            leanh::lean_inc(v_snd_3162_);
                                            leanh::lean_dec_ref(v___x_3161_);
                                            v___x_3163_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__72;
                                            v___x_3164_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3163_, v_snd_3162_);
                                            v_snd_3165_ =
                                                leanh::lean_ctor_get(v___x_3164_, 1);
                                            leanh::lean_inc(v_snd_3165_);
                                            leanh::lean_dec_ref(v___x_3164_);
                                            v___x_3166_ = leanh::lean_unsigned_to_nat(2);
                                            v___x_3167_ =
                                                l_Lean_Syntax_getArg(v_stx_2495_, v___x_3166_);
                                            leanh::lean_dec(v_stx_2495_);
                                            v___x_3168_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v___x_3167_, v_a_2496_, v_snd_3165_);
                                            v_snd_3169_ =
                                                leanh::lean_ctor_get(v___x_3168_, 1);
                                            leanh::lean_inc(v_snd_3169_);
                                            leanh::lean_dec_ref(v___x_3168_);
                                            v___x_3170_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__73;
                                            v___x_3171_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3170_, v_snd_3169_);
                                            return v___x_3171_;
                                        }
                                    }
                                } else {
                                    v___x_3172_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__71;
                                    v___x_3173_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3172_, v_a_2497_);
                                    v_snd_3174_ = leanh::lean_ctor_get(v___x_3173_, 1);
                                    leanh::lean_inc(v_snd_3174_);
                                    leanh::lean_dec_ref(v___x_3173_);
                                    v___x_3175_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_3176_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_3175_);
                                    v___x_3177_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_3176_);
                                    v___x_3178_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3177_, v_snd_3174_);
                                    leanh::lean_dec_ref(v___x_3177_);
                                    v_snd_3179_ = leanh::lean_ctor_get(v___x_3178_, 1);
                                    leanh::lean_inc(v_snd_3179_);
                                    leanh::lean_dec_ref(v___x_3178_);
                                    v___x_3180_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__72;
                                    v___x_3181_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3180_, v_snd_3179_);
                                    v_snd_3182_ = leanh::lean_ctor_get(v___x_3181_, 1);
                                    leanh::lean_inc(v_snd_3182_);
                                    leanh::lean_dec_ref(v___x_3181_);
                                    v___x_3183_ = leanh::lean_unsigned_to_nat(3);
                                    v___x_3184_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_3183_);
                                    leanh::lean_dec(v_stx_2495_);
                                    v___x_3185_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v___x_3184_, v_a_2496_, v_snd_3182_);
                                    v_snd_3186_ = leanh::lean_ctor_get(v___x_3185_, 1);
                                    leanh::lean_inc(v_snd_3186_);
                                    leanh::lean_dec_ref(v___x_3185_);
                                    v___x_3187_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__73;
                                    v___x_3188_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3187_, v_snd_3186_);
                                    return v___x_3188_;
                                }
                            } else {
                                v___x_3189_ = leanh::lean_unsigned_to_nat(0);
                                v___x_3190_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_3189_);
                                v___x_3191_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__70;
                                leanh::lean_inc(v___x_3190_);
                                v___x_3192_ = l_Lean_Syntax_isOfKind(v___x_3190_, v___x_3191_);
                                if v___x_3192_ == 0 {
                                    leanh::lean_dec(v___x_3190_);
                                    v___x_3193_ = leanh::lean_box(0);
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
                                    leanh::lean_dec_ref(v___x_3196_);
                                    return v___x_3197_;
                                } else {
                                    leanh::lean_dec(v_stx_2495_);
                                    v___x_3198_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v___x_3190_);
                                    v___x_3199_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3198_, v_a_2497_);
                                    leanh::lean_dec_ref(v___x_3198_);
                                    return v___x_3199_;
                                }
                            }
                        } else {
                            v___x_3200_ = leanh::lean_unsigned_to_nat(0);
                            v___x_3201_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_3200_);
                            v___x_3202_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__75;
                            leanh::lean_inc(v___x_3201_);
                            v___x_3203_ = l_Lean_Syntax_isOfKind(v___x_3201_, v___x_3202_);
                            if v___x_3203_ == 0 {
                                leanh::lean_dec(v___x_3201_);
                                v___x_3204_ = leanh::lean_box(0);
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
                                leanh::lean_dec_ref(v___x_3207_);
                                return v___x_3208_;
                            } else {
                                leanh::lean_dec(v_stx_2495_);
                                v___x_3209_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v___x_3201_);
                                v___x_3210_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3209_, v_a_2497_);
                                leanh::lean_dec_ref(v___x_3209_);
                                return v___x_3210_;
                            }
                        }
                    } else {
                        v___x_3211_ = leanh::lean_unsigned_to_nat(0);
                        v___x_3212_ = l_Lean_Syntax_getArg(v_stx_2495_, v___x_3211_);
                        v___x_3213_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__68;
                        leanh::lean_inc(v___x_3212_);
                        v___x_3214_ = l_Lean_Syntax_isOfKind(v___x_3212_, v___x_3213_);
                        if v___x_3214_ == 0 {
                            leanh::lean_dec(v___x_3212_);
                            v___x_3215_ = leanh::lean_box(0);
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
                            leanh::lean_dec_ref(v___x_3218_);
                            return v___x_3219_;
                        } else {
                            leanh::lean_dec(v_stx_2495_);
                            v___x_3220_ =
                                l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(
                                    v___x_3212_,
                                );
                            v___x_3221_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3220_, v_a_2497_);
                            leanh::lean_dec_ref(v___x_3220_);
                            return v___x_3221_;
                        }
                    }
                } else {
                    v___x_3222_ = l_Lean_Syntax_getArgs(v_stx_2495_);
                    leanh::lean_dec(v_stx_2495_);
                    v___x_3223_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3224_ = lean_array_get_size(v___x_3222_);
                    v___x_3225_ = leanh::lean_box(0);
                    v___x_3226_ = lean_nat_dec_lt(v___x_3223_, v___x_3224_);
                    if v___x_3226_ == 0 {
                        leanh::lean_dec_ref(v___x_3222_);
                        v___x_3227_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3227_, 0, v___x_3225_);
                        leanh::lean_ctor_set(v___x_3227_, 1, v_a_2497_);
                        return v___x_3227_;
                    } else {
                        v___x_3228_ = lean_nat_dec_le(v___x_3224_, v___x_3224_);
                        if v___x_3228_ == 0 {
                            if v___x_3226_ == 0 {
                                leanh::lean_dec_ref(v___x_3222_);
                                v___x_3229_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3229_, 0, v___x_3225_);
                                leanh::lean_ctor_set(v___x_3229_, 1, v_a_2497_);
                                return v___x_3229_;
                            } else {
                                v___x_3230_ = 0usize;
                                v___x_3231_ = lean_usize_of_nat(v___x_3224_);
                                v___x_3232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_3222_, v___x_3230_, v___x_3231_, v___x_3225_, v_a_2496_, v_a_2497_);
                                leanh::lean_dec_ref(v___x_3222_);
                                return v___x_3232_;
                            }
                        } else {
                            v___x_3233_ = 0usize;
                            v___x_3234_ = lean_usize_of_nat(v___x_3224_);
                            v___x_3235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v___x_3222_, v___x_3233_, v___x_3234_, v___x_3225_, v_a_2496_, v_a_2497_);
                            leanh::lean_dec_ref(v___x_3222_);
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
                v_snd_2504_ = leanh::lean_ctor_get(v___y_2503_, 1);
                leanh::lean_inc(v_snd_2504_);
                leanh::lean_dec_ref(v___y_2503_);
                v_snd_2499_ = v_snd_2504_;
                state = 1;
                continue;
            }
            3 => {
                v_snd_2507_ = leanh::lean_ctor_get(v___y_2506_, 1);
                leanh::lean_inc(v_snd_2507_);
                leanh::lean_dec_ref(v___y_2506_);
                v___x_2508_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2507_);
                return v___x_2508_;
            }
            4 => {
                v_snd_2511_ = leanh::lean_ctor_get(v___y_2510_, 1);
                leanh::lean_inc(v_snd_2511_);
                leanh::lean_dec_ref(v___y_2510_);
                v___x_2512_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2511_);
                return v___x_2512_;
            }
            5 => {
                v_snd_2515_ = leanh::lean_ctor_get(v___y_2514_, 1);
                leanh::lean_inc(v_snd_2515_);
                leanh::lean_dec_ref(v___y_2514_);
                v___x_2516_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2515_);
                return v___x_2516_;
            }
            6 => {
                v_snd_2519_ = leanh::lean_ctor_get(v___y_2518_, 1);
                leanh::lean_inc(v_snd_2519_);
                leanh::lean_dec_ref(v___y_2518_);
                v___x_2520_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2519_);
                return v___x_2520_;
            }
            7 => {
                v___x_2642_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
                leanh::lean_inc(v_a_2496_);
                v___x_2643_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(v_a_2496_, v___x_2642_);
                v___x_2644_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2643_, v_snd_2641_);
                leanh::lean_dec_ref(v___x_2643_);
                v_snd_2645_ = leanh::lean_ctor_get(v___x_2644_, 1);
                leanh::lean_inc(v_snd_2645_);
                leanh::lean_dec_ref(v___x_2644_);
                v___x_2646_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_2639_);
                v___x_2647_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2646_, v_snd_2645_);
                leanh::lean_dec_ref(v___x_2646_);
                v_snd_2648_ = leanh::lean_ctor_get(v___x_2647_, 1);
                leanh::lean_inc(v_snd_2648_);
                leanh::lean_dec_ref(v___x_2647_);
                v___x_2649_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2648_);
                return v___x_2649_;
            }
            8 => {
                v_snd_2652_ = leanh::lean_ctor_get(v___y_2651_, 1);
                leanh::lean_inc(v_snd_2652_);
                leanh::lean_dec_ref(v___y_2651_);
                v_snd_2641_ = v_snd_2652_;
                state = 7;
                continue;
            }
            9 => {
                v___x_2698_ = lean_string_utf8_byte_size(v___y_2697_);
                leanh::lean_inc_ref(v___y_2697_);
                v___x_2699_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2699_, 0, v___y_2697_);
                leanh::lean_ctor_set(v___x_2699_, 1, v___x_2673_);
                leanh::lean_ctor_set(v___x_2699_, 2, v___x_2698_);
                v___x_2700_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v___x_2699_);
                v___x_2701_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__63;
                v___x_2702_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg(v_a_2496_, v___y_2697_, v___x_2699_, v___x_2698_, v___x_2700_, v___x_2701_);
                leanh::lean_dec_ref_known(v___x_2699_, 3);
                leanh::lean_dec_ref(v___y_2697_);
                v___x_2703_ = lean_array_to_list(v___x_2702_);
                v___x_2704_ = l_String_intercalate(v___x_2689_, v___x_2703_);
                v___x_2705_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2704_, v_snd_2691_);
                leanh::lean_dec_ref(v___x_2704_);
                v_snd_2706_ = leanh::lean_ctor_get(v___x_2705_, 1);
                leanh::lean_inc(v_snd_2706_);
                leanh::lean_dec_ref(v___x_2705_);
                v___x_2707_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
                leanh::lean_inc(v_a_2496_);
                v___x_2708_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_nl_spec__0(v_a_2496_, v___x_2707_);
                v___x_2709_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2708_, v_snd_2706_);
                leanh::lean_dec_ref(v___x_2708_);
                v_snd_2710_ = leanh::lean_ctor_get(v___x_2709_, 1);
                leanh::lean_inc(v_snd_2710_);
                leanh::lean_dec_ref(v___x_2709_);
                v___x_2711_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_2695_);
                v___x_2712_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2711_, v_snd_2710_);
                leanh::lean_dec_ref(v___x_2711_);
                v_snd_2713_ = leanh::lean_ctor_get(v___x_2712_, 1);
                leanh::lean_inc(v_snd_2713_);
                leanh::lean_dec_ref(v___x_2712_);
                v___x_2714_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_endBlock___redArg(v_snd_2713_);
                return v___x_2714_;
            }
            10 => {
                v___x_2827_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_2826_, v_snd_2820_);
                leanh::lean_dec_ref(v___y_2826_);
                v_snd_2828_ = leanh::lean_ctor_get(v___x_2827_, 1);
                leanh::lean_inc(v_snd_2828_);
                leanh::lean_dec_ref(v___x_2827_);
                v___x_2829_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_2824_);
                v___x_2830_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2829_, v_snd_2828_);
                leanh::lean_dec_ref(v___x_2829_);
                return v___x_2830_;
            }
            11 => {
                v___x_2846_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_2845_, v_snd_2839_);
                leanh::lean_dec_ref(v___y_2845_);
                v_snd_2847_ = leanh::lean_ctor_get(v___x_2846_, 1);
                leanh::lean_inc(v_snd_2847_);
                leanh::lean_dec_ref(v___x_2846_);
                v___x_2848_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_2843_);
                v___x_2849_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2848_, v_snd_2847_);
                leanh::lean_dec_ref(v___x_2848_);
                return v___x_2849_;
            }
            12 => {
                v___x_2877_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_2876_, v_snd_2871_);
                leanh::lean_dec_ref(v___y_2876_);
                v_snd_2878_ = leanh::lean_ctor_get(v___x_2877_, 1);
                leanh::lean_inc(v_snd_2878_);
                leanh::lean_dec_ref(v___x_2877_);
                v___x_2879_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk3_2874_);
                v___x_2880_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2879_, v_snd_2878_);
                leanh::lean_dec_ref(v___x_2879_);
                return v___x_2880_;
            }
            13 => {
                v___x_2908_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_2907_, v_snd_2902_);
                leanh::lean_dec_ref(v___y_2907_);
                v_snd_2909_ = leanh::lean_ctor_get(v___x_2908_, 1);
                leanh::lean_inc(v_snd_2909_);
                leanh::lean_dec_ref(v___x_2908_);
                v___x_2910_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk3_2905_);
                v___x_2911_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2910_, v_snd_2909_);
                leanh::lean_dec_ref(v___x_2910_);
                return v___x_2911_;
            }
            14 => {
                v___x_2935_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_2934_, v_snd_2928_);
                leanh::lean_dec_ref(v___y_2934_);
                v_snd_2936_ = leanh::lean_ctor_get(v___x_2935_, 1);
                leanh::lean_inc(v_snd_2936_);
                leanh::lean_dec_ref(v___x_2935_);
                v___x_2937_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_2932_);
                v___x_2938_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2937_, v_snd_2936_);
                leanh::lean_dec_ref(v___x_2937_);
                return v___x_2938_;
            }
            15 => {
                v___x_2954_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_2953_, v_snd_2947_);
                leanh::lean_dec_ref(v___y_2953_);
                v_snd_2955_ = leanh::lean_ctor_get(v___x_2954_, 1);
                leanh::lean_inc(v_snd_2955_);
                leanh::lean_dec_ref(v___x_2954_);
                v___x_2956_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_2951_);
                v___x_2957_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_2956_, v_snd_2955_);
                leanh::lean_dec_ref(v___x_2956_);
                return v___x_2957_;
            }
            16 => {
                v___x_3005_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___y_3004_, v_snd_2996_);
                leanh::lean_dec_ref(v___y_3004_);
                v_snd_3006_ = leanh::lean_ctor_get(v___x_3005_, 1);
                leanh::lean_inc(v_snd_3006_);
                leanh::lean_dec_ref(v___x_3005_);
                v___x_3007_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_3000_);
                v___x_3008_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3007_, v_snd_3006_);
                leanh::lean_dec_ref(v___x_3007_);
                v_snd_3009_ = leanh::lean_ctor_get(v___x_3008_, 1);
                leanh::lean_inc(v_snd_3009_);
                leanh::lean_dec_ref(v___x_3008_);
                v_stx_2495_ = v___x_3002_;
                v_a_2497_ = v_snd_3009_;
                state = 0;
                continue;
            }
            17 => {
                v___x_3028_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_3023_);
                v___x_3029_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3028_, v_snd_3027_);
                leanh::lean_dec_ref(v___x_3028_);
                v_snd_3030_ = leanh::lean_ctor_get(v___x_3029_, 1);
                leanh::lean_inc(v_snd_3030_);
                leanh::lean_dec_ref(v___x_3029_);
                v_stx_2495_ = v___x_3025_;
                v_a_2497_ = v_snd_3030_;
                state = 0;
                continue;
            }
            18 => {
                v_snd_3034_ = leanh::lean_ctor_get(v___y_3033_, 1);
                leanh::lean_inc(v_snd_3034_);
                leanh::lean_dec_ref(v___y_3033_);
                v_snd_3027_ = v_snd_3034_;
                state = 17;
                continue;
            }
            19 => {
                v___x_3057_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_3054_);
                v___x_3058_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3057_, v_snd_3056_);
                leanh::lean_dec_ref(v___x_3057_);
                return v___x_3058_;
            }
            20 => {
                v_snd_3061_ = leanh::lean_ctor_get(v___y_3060_, 1);
                leanh::lean_inc(v_snd_3061_);
                leanh::lean_dec_ref(v___y_3060_);
                v_snd_3056_ = v_snd_3061_;
                state = 19;
                continue;
            }
            21 => {
                v___x_3084_ =
                    l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_tk2_3081_);
                v___x_3085_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_out___redArg(v___x_3084_, v_snd_3083_);
                leanh::lean_dec_ref(v___x_3084_);
                return v___x_3085_;
            }
            22 => {
                v_snd_3088_ = leanh::lean_ctor_get(v___y_3087_, 1);
                leanh::lean_inc(v_snd_3088_);
                leanh::lean_dec_ref(v___y_3087_);
                v_snd_3083_ = v_snd_3088_;
                state = 21;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(
    mut v_as_3236_: *mut leanh::LeanObject,
    mut v_i_3237_: usize,
    mut v_stop_3238_: usize,
    mut v_b_3239_: *mut leanh::LeanObject,
    mut v___y_3240_: *mut leanh::LeanObject,
    mut v___y_3241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3242_: u8 = 0;
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: usize = 0;
    let mut v___x_3248_: usize = 0;
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3242_ = lean_usize_dec_eq(v_i_3237_, v_stop_3238_);
                if v___x_3242_ == 0 {
                    v___x_3243_ = lean_array_uget_borrowed(v_as_3236_, v_i_3237_);
                    leanh::lean_inc(v___x_3243_);
                    v___x_3244_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v___x_3243_, v___y_3240_, v___y_3241_);
                    v_fst_3245_ = leanh::lean_ctor_get(v___x_3244_, 0);
                    leanh::lean_inc(v_fst_3245_);
                    v_snd_3246_ = leanh::lean_ctor_get(v___x_3244_, 1);
                    leanh::lean_inc(v_snd_3246_);
                    leanh::lean_dec_ref(v___x_3244_);
                    v___x_3247_ = 1usize;
                    v___x_3248_ = lean_usize_add(v_i_3237_, v___x_3247_);
                    v_i_3237_ = v___x_3248_;
                    v_b_3239_ = v_fst_3245_;
                    v___y_3241_ = v_snd_3246_;
                    state = 0;
                    continue;
                } else {
                    v___x_3250_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3250_, 0, v_b_3239_);
                    leanh::lean_ctor_set(v___x_3250_, 1, v___y_3241_);
                    return v___x_3250_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2___boxed(
    mut v_as_3251_: *mut leanh::LeanObject,
    mut v_i_3252_: *mut leanh::LeanObject,
    mut v_stop_3253_: *mut leanh::LeanObject,
    mut v_b_3254_: *mut leanh::LeanObject,
    mut v___y_3255_: *mut leanh::LeanObject,
    mut v___y_3256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3257_: usize = 0;
    let mut v_stop_boxed_3258_: usize = 0;
    let mut v_res_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3257_ = leanh::lean_unbox_usize(v_i_3252_);
    leanh::lean_dec(v_i_3252_);
    v_stop_boxed_3258_ = leanh::lean_unbox_usize(v_stop_3253_);
    leanh::lean_dec(v_stop_3253_);
    v_res_3259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__2(v_as_3251_, v_i_boxed_3257_, v_stop_boxed_3258_, v_b_3254_, v___y_3255_, v___y_3256_);
    leanh::lean_dec(v___y_3255_);
    leanh::lean_dec_ref(v_as_3251_);
    return v_res_3259_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0___boxed(
    mut v_as_3260_: *mut leanh::LeanObject,
    mut v_sz_3261_: *mut leanh::LeanObject,
    mut v_i_3262_: *mut leanh::LeanObject,
    mut v_b_3263_: *mut leanh::LeanObject,
    mut v___y_3264_: *mut leanh::LeanObject,
    mut v___y_3265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3266_: usize = 0;
    let mut v_i_boxed_3267_: usize = 0;
    let mut v_res_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3266_ = leanh::lean_unbox_usize(v_sz_3261_);
    leanh::lean_dec(v_sz_3261_);
    v_i_boxed_3267_ = leanh::lean_unbox_usize(v_i_3262_);
    leanh::lean_dec(v_i_3262_);
    v_res_3268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__0(v_as_3260_, v_sz_boxed_3266_, v_i_boxed_3267_, v_b_3263_, v___y_3264_, v___y_3265_);
    leanh::lean_dec(v___y_3264_);
    leanh::lean_dec_ref(v_as_3260_);
    return v_res_3268_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__1___boxed(
    mut v_as_3269_: *mut leanh::LeanObject,
    mut v_sz_3270_: *mut leanh::LeanObject,
    mut v_i_3271_: *mut leanh::LeanObject,
    mut v_b_3272_: *mut leanh::LeanObject,
    mut v___y_3273_: *mut leanh::LeanObject,
    mut v___y_3274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3275_: usize = 0;
    let mut v_i_boxed_3276_: usize = 0;
    let mut v_res_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3275_ = leanh::lean_unbox_usize(v_sz_3270_);
    leanh::lean_dec(v_sz_3270_);
    v_i_boxed_3276_ = leanh::lean_unbox_usize(v_i_3271_);
    leanh::lean_dec(v_i_3271_);
    v_res_3277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__1(v_as_3269_, v_sz_boxed_3275_, v_i_boxed_3276_, v_b_3272_, v___y_3273_, v___y_3274_);
    leanh::lean_dec(v___y_3273_);
    leanh::lean_dec_ref(v_as_3269_);
    return v_res_3277_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___boxed(
    mut v_as_3278_: *mut leanh::LeanObject,
    mut v_i_3279_: *mut leanh::LeanObject,
    mut v_stop_3280_: *mut leanh::LeanObject,
    mut v_b_3281_: *mut leanh::LeanObject,
    mut v___y_3282_: *mut leanh::LeanObject,
    mut v___y_3283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3284_: usize = 0;
    let mut v_stop_boxed_3285_: usize = 0;
    let mut v_res_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3284_ = leanh::lean_unbox_usize(v_i_3279_);
    leanh::lean_dec(v_i_3279_);
    v_stop_boxed_3285_ = leanh::lean_unbox_usize(v_stop_3280_);
    leanh::lean_dec(v_stop_3280_);
    v_res_3286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v_as_3278_, v_i_boxed_3284_, v_stop_boxed_3285_, v_b_3281_, v___y_3282_, v___y_3283_);
    leanh::lean_dec(v___y_3282_);
    leanh::lean_dec_ref(v_as_3278_);
    return v_res_3286_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___boxed(
    mut v_as_3287_: *mut leanh::LeanObject,
    mut v_sz_3288_: *mut leanh::LeanObject,
    mut v_i_3289_: *mut leanh::LeanObject,
    mut v_b_3290_: *mut leanh::LeanObject,
    mut v___y_3291_: *mut leanh::LeanObject,
    mut v___y_3292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3293_: usize = 0;
    let mut v_i_boxed_3294_: usize = 0;
    let mut v_res_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3293_ = leanh::lean_unbox_usize(v_sz_3288_);
    leanh::lean_dec(v_sz_3288_);
    v_i_boxed_3294_ = leanh::lean_unbox_usize(v_i_3289_);
    leanh::lean_dec(v_i_3289_);
    v_res_3295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(v_as_3287_, v_sz_boxed_3293_, v_i_boxed_3294_, v_b_3290_, v___y_3291_, v___y_3292_);
    leanh::lean_dec(v___y_3291_);
    leanh::lean_dec_ref(v_as_3287_);
    return v_res_3295_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___boxed(
    mut v_stx_3296_: *mut leanh::LeanObject,
    mut v_a_3297_: *mut leanh::LeanObject,
    mut v_a_3298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3299_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(
        v_stx_3296_,
        v_a_3297_,
        v_a_3298_,
    );
    leanh::lean_dec(v_a_3297_);
    return v_res_3299_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(
    mut v_a_3300_: *mut leanh::LeanObject,
    mut v___y_3301_: *mut leanh::LeanObject,
    mut v___x_3302_: *mut leanh::LeanObject,
    mut v___x_3303_: *mut leanh::LeanObject,
    mut v_inst_3304_: *mut leanh::LeanObject,
    mut v_R_3305_: *mut leanh::LeanObject,
    mut v_a_3306_: *mut leanh::LeanObject,
    mut v_b_3307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3308_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___redArg(v_a_3300_, v___y_3301_, v___x_3302_, v___x_3303_, v_a_3306_, v_b_3307_);
    return v___x_3308_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___boxed(
    mut v_a_3309_: *mut leanh::LeanObject,
    mut v___y_3310_: *mut leanh::LeanObject,
    mut v___x_3311_: *mut leanh::LeanObject,
    mut v___x_3312_: *mut leanh::LeanObject,
    mut v_inst_3313_: *mut leanh::LeanObject,
    mut v_R_3314_: *mut leanh::LeanObject,
    mut v_a_3315_: *mut leanh::LeanObject,
    mut v_b_3316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3317_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v_a_3309_, v___y_3310_, v___x_3311_, v___x_3312_, v_inst_3313_, v_R_3314_, v_a_3315_, v_b_3316_);
    leanh::lean_dec_ref(v___x_3311_);
    leanh::lean_dec_ref(v___y_3310_);
    leanh::lean_dec(v_a_3309_);
    return v_res_3317_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___lam__0(
    mut v___y_3318_: *mut leanh::LeanObject,
    mut v___y_3319_: *mut leanh::LeanObject,
    mut v___y_3320_: *mut leanh::LeanObject,
    mut v___y_3321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3323_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_3319_);
    if leanh::lean_obj_tag(v___x_3323_) == 0 {
        let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_3323_, 1);
        v___x_3324_ = leanh::lean_box(0);
        v___x_3325_ = l_Lean_PrettyPrinter_Formatter_visitAtom(
            v___x_3324_,
            v___y_3318_,
            v___y_3319_,
            v___y_3320_,
            v___y_3321_,
        );
        if leanh::lean_obj_tag(v___x_3325_) == 0 {
            let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_3325_, 1);
            v___x_3326_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_3319_);
            if leanh::lean_obj_tag(v___x_3326_) == 0 {
                let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref_known(v___x_3326_, 1);
                v___x_3327_ = l_Lean_Doc_Parser_metadataContents_formatter(
                    v___y_3318_,
                    v___y_3319_,
                    v___y_3320_,
                    v___y_3321_,
                );
                if leanh::lean_obj_tag(v___x_3327_) == 0 {
                    let mut v___x_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec_ref_known(v___x_3327_, 1);
                    v___x_3328_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_3319_);
                    if leanh::lean_obj_tag(v___x_3328_) == 0 {
                        let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
                        leanh::lean_dec_ref_known(v___x_3328_, 1);
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
    mut v___y_3330_: *mut leanh::LeanObject,
    mut v___y_3331_: *mut leanh::LeanObject,
    mut v___y_3332_: *mut leanh::LeanObject,
    mut v___y_3333_: *mut leanh::LeanObject,
    mut v___y_3334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3335_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata___lam__0(
        v___y_3330_,
        v___y_3331_,
        v___y_3332_,
        v___y_3333_,
    );
    leanh::lean_dec(v___y_3333_);
    leanh::lean_dec_ref(v___y_3332_);
    leanh::lean_dec(v___y_3331_);
    leanh::lean_dec_ref(v___y_3330_);
    return v_res_3335_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata(
    mut v_a_3337_: *mut leanh::LeanObject,
    mut v_a_3338_: *mut leanh::LeanObject,
    mut v_a_3339_: *mut leanh::LeanObject,
    mut v_a_3340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_3344_: *mut leanh::LeanObject,
    mut v_a_3345_: *mut leanh::LeanObject,
    mut v_a_3346_: *mut leanh::LeanObject,
    mut v_a_3347_: *mut leanh::LeanObject,
    mut v_a_3348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3349_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata(
        v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_,
    );
    leanh::lean_dec(v_a_3347_);
    leanh::lean_dec_ref(v_a_3346_);
    leanh::lean_dec(v_a_3345_);
    leanh::lean_dec_ref(v_a_3344_);
    return v_res_3349_;
}
pub unsafe fn l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString(
    mut v_stx_3350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3351_ = leanh::lean_unsigned_to_nat(0);
    v___x_3352_ =
        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomStrLit___redArg___closed__0;
    v___x_3353_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(
        v_stx_3350_,
        v___x_3351_,
        v___x_3352_,
    );
    v_snd_3354_ = leanh::lean_ctor_get(v___x_3353_, 1);
    leanh::lean_inc(v_snd_3354_);
    leanh::lean_dec_ref(v___x_3353_);
    return v_snd_3354_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(
    mut v_range_3361_: *mut leanh::LeanObject,
    mut v_b_3362_: *mut leanh::LeanObject,
    mut v_i_3363_: *mut leanh::LeanObject,
    mut v___y_3364_: *mut leanh::LeanObject,
    mut v___y_3365_: *mut leanh::LeanObject,
    mut v___y_3366_: *mut leanh::LeanObject,
    mut v___y_3367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stop_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: u8 = 0;
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3377_: u8 = 0;
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: u8 = 0;
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3392_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_3369_ = leanh::lean_ctor_get(v_range_3361_, 1);
                v_step_3370_ = leanh::lean_ctor_get(v_range_3361_, 2);
                v___x_3371_ = lean_nat_dec_lt(v_i_3363_, v_stop_3369_);
                if v___x_3371_ == 0 {
                    leanh::lean_dec(v_i_3363_);
                    v___x_3372_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3372_, 0, v_b_3362_);
                    return v___x_3372_;
                } else {
                    v___x_3373_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v___y_3365_);
                    v_a_3374_ = leanh::lean_ctor_get(v___x_3373_, 0);
                    v_isSharedCheck_3392_ = (!leanh::lean_is_exclusive(v___x_3373_)) as u8;
                    if v_isSharedCheck_3392_ == 0 {
                        v___x_3376_ = v___x_3373_;
                        v_isShared_3377_ = v_isSharedCheck_3392_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3374_);
                        leanh::lean_dec(v___x_3373_);
                        v___x_3376_ = leanh::lean_box(0);
                        v_isShared_3377_ = v_isSharedCheck_3392_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3378_ = leanh::lean_box(0);
                leanh::lean_inc(v_a_3374_);
                v___x_3382_ = l_Lean_Syntax_getKind(v_a_3374_);
                v___x_3383_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___closed__1;
                v___x_3384_ = lean_name_eq(v___x_3382_, v___x_3383_);
                leanh::lean_dec(v___x_3382_);
                if v___x_3384_ == 0 {
                    v___x_3385_ =
                        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString(
                            v_a_3374_,
                        );
                    if v_isShared_3377_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3376_, 3);
                        leanh::lean_ctor_set(v___x_3376_, 0, v___x_3385_);
                        v___x_3387_ = v___x_3376_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3390_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3385_);
                        v___x_3387_ = v_reuseFailAlloc_3390_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3376_);
                    leanh::lean_dec(v_a_3374_);
                    v___x_3391_ =
                        l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_formatMetadata(
                            v___y_3364_,
                            v___y_3365_,
                            v___y_3366_,
                            v___y_3367_,
                        );
                    if leanh::lean_obj_tag(v___x_3391_) == 0 {
                        leanh::lean_dec_ref_known(v___x_3391_, 1);
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_3363_);
                        return v___x_3391_;
                    }
                }
            }
            2 => {
                v___x_3380_ = lean_nat_add(v_i_3363_, v_step_3370_);
                leanh::lean_dec(v_i_3363_);
                v_b_3362_ = v___x_3378_;
                v_i_3363_ = v___x_3380_;
                state = 0;
                continue;
            }
            3 => {
                v___x_3388_ =
                    l_Lean_PrettyPrinter_Formatter_push___redArg(v___x_3387_, v___y_3365_);
                if leanh::lean_obj_tag(v___x_3388_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3388_, 1);
                    v___x_3389_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__1___redArg(v___y_3365_);
                    leanh::lean_dec_ref(v___x_3389_);
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_i_3363_);
                    return v___x_3388_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___boxed(
    mut v_range_3393_: *mut leanh::LeanObject,
    mut v_b_3394_: *mut leanh::LeanObject,
    mut v_i_3395_: *mut leanh::LeanObject,
    mut v___y_3396_: *mut leanh::LeanObject,
    mut v___y_3397_: *mut leanh::LeanObject,
    mut v___y_3398_: *mut leanh::LeanObject,
    mut v___y_3399_: *mut leanh::LeanObject,
    mut v___y_3400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3401_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v_range_3393_, v_b_3394_, v_i_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
    leanh::lean_dec(v___y_3399_);
    leanh::lean_dec_ref(v___y_3398_);
    leanh::lean_dec(v___y_3397_);
    leanh::lean_dec_ref(v___y_3396_);
    leanh::lean_dec_ref(v_range_3393_);
    return v_res_3401_;
}
pub unsafe fn l_Lean_Doc_Parser_document_formatter___lam__0(
    mut v___x_3402_: *mut leanh::LeanObject,
    mut v___x_3403_: *mut leanh::LeanObject,
    mut v___x_3404_: *mut leanh::LeanObject,
    mut v___y_3405_: *mut leanh::LeanObject,
    mut v___y_3406_: *mut leanh::LeanObject,
    mut v___y_3407_: *mut leanh::LeanObject,
    mut v___y_3408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3413_: u8 = 0;
    let mut v___x_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3417_: u8 = 0;
    let mut v_unused_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3410_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v___x_3402_, v___x_3403_, v___x_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_);
                if leanh::lean_obj_tag(v___x_3410_) == 0 {
                    v_isSharedCheck_3417_ = (!leanh::lean_is_exclusive(v___x_3410_)) as u8;
                    if v_isSharedCheck_3417_ == 0 {
                        v_unused_3418_ = leanh::lean_ctor_get(v___x_3410_, 0);
                        leanh::lean_dec(v_unused_3418_);
                        v___x_3412_ = v___x_3410_;
                        v_isShared_3413_ = v_isSharedCheck_3417_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3410_);
                        v___x_3412_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_3412_, 0, v___x_3403_);
                    v___x_3415_ = v___x_3412_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3416_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3403_);
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
    mut v___x_3419_: *mut leanh::LeanObject,
    mut v___x_3420_: *mut leanh::LeanObject,
    mut v___x_3421_: *mut leanh::LeanObject,
    mut v___y_3422_: *mut leanh::LeanObject,
    mut v___y_3423_: *mut leanh::LeanObject,
    mut v___y_3424_: *mut leanh::LeanObject,
    mut v___y_3425_: *mut leanh::LeanObject,
    mut v___y_3426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3427_ = l_Lean_Doc_Parser_document_formatter___lam__0(
        v___x_3419_,
        v___x_3420_,
        v___x_3421_,
        v___y_3422_,
        v___y_3423_,
        v___y_3424_,
        v___y_3425_,
    );
    leanh::lean_dec(v___y_3425_);
    leanh::lean_dec_ref(v___y_3424_);
    leanh::lean_dec(v___y_3423_);
    leanh::lean_dec_ref(v___y_3422_);
    leanh::lean_dec_ref(v___x_3419_);
    return v_res_3427_;
}
pub unsafe fn l_Lean_Doc_Parser_document_formatter___lam__1(
    mut v___y_3428_: *mut leanh::LeanObject,
    mut v___y_3429_: *mut leanh::LeanObject,
    mut v___y_3430_: *mut leanh::LeanObject,
    mut v___y_3431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3433_ = l_Lean_Syntax_MonadTraverser_getCur___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_pushAtomString_spec__0___redArg(v___y_3429_);
    v_a_3434_ = leanh::lean_ctor_get(v___x_3433_, 0);
    leanh::lean_inc(v_a_3434_);
    leanh::lean_dec_ref(v___x_3433_);
    v___x_3435_ = l_Lean_Syntax_getArgs(v_a_3434_);
    leanh::lean_dec(v_a_3434_);
    v_i_3436_ = lean_array_get_size(v___x_3435_);
    leanh::lean_dec_ref(v___x_3435_);
    v___x_3437_ = leanh::lean_unsigned_to_nat(0);
    v___x_3438_ = leanh::lean_unsigned_to_nat(1);
    v___x_3439_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3439_, 0, v___x_3437_);
    leanh::lean_ctor_set(v___x_3439_, 1, v_i_3436_);
    leanh::lean_ctor_set(v___x_3439_, 2, v___x_3438_);
    v___x_3440_ = leanh::lean_box(0);
    v___f_3441_ = leanh::lean_alloc_closure(
        l_Lean_Doc_Parser_document_formatter___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___f_3441_, 0, v___x_3439_);
    leanh::lean_closure_set(v___f_3441_, 1, v___x_3440_);
    leanh::lean_closure_set(v___f_3441_, 2, v___x_3437_);
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
    mut v___y_3443_: *mut leanh::LeanObject,
    mut v___y_3444_: *mut leanh::LeanObject,
    mut v___y_3445_: *mut leanh::LeanObject,
    mut v___y_3446_: *mut leanh::LeanObject,
    mut v___y_3447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3448_ = l_Lean_Doc_Parser_document_formatter___lam__1(
        v___y_3443_,
        v___y_3444_,
        v___y_3445_,
        v___y_3446_,
    );
    leanh::lean_dec(v___y_3446_);
    leanh::lean_dec_ref(v___y_3445_);
    leanh::lean_dec(v___y_3444_);
    leanh::lean_dec_ref(v___y_3443_);
    return v_res_3448_;
}
pub unsafe fn l_Lean_Doc_Parser_document_formatter(
    mut v_a_3450_: *mut leanh::LeanObject,
    mut v_a_3451_: *mut leanh::LeanObject,
    mut v_a_3452_: *mut leanh::LeanObject,
    mut v_a_3453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_3457_: *mut leanh::LeanObject,
    mut v_a_3458_: *mut leanh::LeanObject,
    mut v_a_3459_: *mut leanh::LeanObject,
    mut v_a_3460_: *mut leanh::LeanObject,
    mut v_a_3461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3462_ = l_Lean_Doc_Parser_document_formatter(v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
    leanh::lean_dec(v_a_3460_);
    leanh::lean_dec_ref(v_a_3459_);
    leanh::lean_dec(v_a_3458_);
    leanh::lean_dec_ref(v_a_3457_);
    return v_res_3462_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0(
    mut v_range_3463_: *mut leanh::LeanObject,
    mut v_b_3464_: *mut leanh::LeanObject,
    mut v_i_3465_: *mut leanh::LeanObject,
    mut v_hs_3466_: *mut leanh::LeanObject,
    mut v_hl_3467_: *mut leanh::LeanObject,
    mut v___y_3468_: *mut leanh::LeanObject,
    mut v___y_3469_: *mut leanh::LeanObject,
    mut v___y_3470_: *mut leanh::LeanObject,
    mut v___y_3471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3473_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v_range_3463_, v_b_3464_, v_i_3465_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
    return v___x_3473_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0___boxed(
    mut v_range_3474_: *mut leanh::LeanObject,
    mut v_b_3475_: *mut leanh::LeanObject,
    mut v_i_3476_: *mut leanh::LeanObject,
    mut v_hs_3477_: *mut leanh::LeanObject,
    mut v_hl_3478_: *mut leanh::LeanObject,
    mut v___y_3479_: *mut leanh::LeanObject,
    mut v___y_3480_: *mut leanh::LeanObject,
    mut v___y_3481_: *mut leanh::LeanObject,
    mut v___y_3482_: *mut leanh::LeanObject,
    mut v___y_3483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3484_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Doc_Parser_document_formatter_spec__0(v_range_3474_, v_b_3475_, v_i_3476_, v_hs_3477_, v_hl_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
    leanh::lean_dec(v___y_3482_);
    leanh::lean_dec_ref(v___y_3481_);
    leanh::lean_dec(v___y_3480_);
    leanh::lean_dec_ref(v___y_3479_);
    leanh::lean_dec_ref(v_range_3474_);
    return v_res_3484_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_DocString_Formatter(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_PrettyPrinter_Formatter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DocString_Parser(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_DocString_Formatter(
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
pub unsafe fn initialize_Lean_DocString_Formatter(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_PrettyPrinter_Formatter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_DocString_Parser(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DocString_Formatter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_DocString_Formatter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_DocString_Formatter(builtin);
}