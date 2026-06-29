// Lean compiler output
// Module: Std.Time.Zoned.Database.TzIf
// Imports: Init.Data.Range.Polymorphic.Iterators Std.Internal.Parsec Init.Data.Int.Repr
use crate::r#gen::Init::Data::ByteArray::Extra::{
    l_ByteArray_toUInt64BE_x21, l_ByteArray_toUInt64LE_x21,
};
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::Int::Basic::l_Int_negOfNat;
use crate::r#gen::Init::Data::Int::Repr::{
    initialize_Init_Data_Int_Repr, l_Int_repr, runtime_initialize_Init_Data_Int_Repr,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Data::Repr::{
    l_Bool_repr___redArg, l_Nat_reprFast, l_Repr_addAppParen, l_String_quote,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_addMacroScope,
    l_Lean_replaceRef, l_String_toRawSubstring_x27, l_instInhabitedUInt8, l_instInhabitedUInt32,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Std::Data::ByteSlice::l_ByteSlice_toByteArray;
use crate::r#gen::Std::Internal::Parsec::ByteArray::{
    l_Std_Internal_Parsec_ByteArray_skipBytes, l_Std_Internal_Parsec_ByteArray_take,
};
use crate::r#gen::Std::Internal::Parsec::{
    initialize_Std_Internal_Parsec, runtime_initialize_Std_Internal_Parsec,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::ByteArray::Basic::{
    lean_byte_array_fget, lean_byte_array_get,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{lean_int_dec_lt, lean_nat_to_int};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftl;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::{lean_string_length, lean_string_push};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_to_utf8;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{lean_uint32_lor, lean_uint32_shift_left};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint8_to_nat, lean_uint8_to_uint32, lean_uint64_to_nat, lean_usize_add, lean_usize_dec_lt,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_array_get_size, lean_array_push, lean_array_to_list, lean_byte_array_size,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed,
    lean_uint8_dec_eq, lean_uint8_of_nat, lean_uint32_of_nat, lean_uint32_to_nat,
};
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__0_value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__1_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__2_value) as *mut crate::leanh::LeanObject,2126719535545605916 as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 105, 109, 101, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__4_value) as *mut crate::leanh::LeanObject,14182064430198580444 as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__6_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [90, 111, 110, 101, 100, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__6_value) as *mut crate::leanh::LeanObject,12797042221022953416 as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__8_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [68, 97, 116, 97, 98, 97, 115, 101, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__8_value) as *mut crate::leanh::LeanObject,14246659929497392988 as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__10_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 122, 73, 102, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__9_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__10_value) as *mut crate::leanh::LeanObject,9593979424156350980 as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__11_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,17284221013824265317 as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__12_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__2_value) as *mut crate::leanh::LeanObject,16077304773555400774 as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__13_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__4_value) as *mut crate::leanh::LeanObject,5244953291729708654 as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__15_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [84, 105, 109, 101, 90, 111, 110, 101, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__16_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__14_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__15_value) as *mut crate::leanh::LeanObject,13444310946274085109 as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__17_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 90, 105, 102, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__18_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__16_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__17_value) as *mut crate::leanh::LeanObject,5411744946770301377 as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__19_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 73, 110, 116, 51, 50, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__18_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__19_value) as *mut crate::leanh::LeanObject,11496539451519720210 as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__21_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [73, 110, 116, 51, 50, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__22_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__21_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__23_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__20_value) as *mut crate::leanh::LeanObject,((( 1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__22_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__23_value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__23_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 110, 116, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__0_value) as *mut crate::leanh::LeanObject,7009148538150066493 as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__2_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__4_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__4_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__0_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 73, 110, 116, 54, 52, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__18_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__0_value) as *mut crate::leanh::LeanObject,7844554101976475412 as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [73, 110, 116, 54, 52, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__3_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__1_value) as *mut crate::leanh::LeanObject,((( 1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__3_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__4_value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__0_value:
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
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__1_value:
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
    m_data: [118, 101, 114, 115, 105, 111, 110, 0],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__2_value:
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
        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__1_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__4_value:
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
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value:
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
        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__8_value:
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
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9_value:
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
        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__8_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__10_value:
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
    m_data: [105, 115, 117, 116, 99, 110, 116, 0],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__11_value:
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
        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__10_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__12_value:
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
    m_data: [105, 115, 115, 116, 100, 99, 110, 116, 0],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__13_value:
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
        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__12_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__15_value:
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
    m_data: [108, 101, 97, 112, 99, 110, 116, 0],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__16_value:
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
        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__15_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__17_value:
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
    m_data: [116, 105, 109, 101, 99, 110, 116, 0],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__18_value:
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
        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__17_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__19_value:
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
    m_data: [116, 121, 112, 101, 99, 110, 116, 0],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__20_value:
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
        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__19_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__21_value:
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
    m_data: [99, 104, 97, 114, 99, 110, 116, 0],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__22_value:
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
        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__21_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__22:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__23_value:
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
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__23:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__23_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26_value:
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
        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27_value:
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
        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__23_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader___closed__0_value:
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
    m_fun: l_Std_Time_TimeZone_TZif_instReprHeader_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_TimeZone_TZif_instReprHeader: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0: u8 = 0;
static mut l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__1: u32 = 0;
static mut l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedHeader_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedHeader: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__0_value:
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
    m_data: [103, 109, 116, 79, 102, 102, 115, 101, 116, 0],
};
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__1_value:
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
        l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(
            l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__1_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(
            l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__5_value:
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
    m_data: [105, 115, 68, 115, 116, 0],
};
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__6_value:
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
        l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__5_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__8_value:
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
        97, 98, 98, 114, 101, 118, 105, 97, 116, 105, 111, 110, 73, 110, 100, 101, 120, 0,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__9_value:
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
        l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__8_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__9_value
) as *mut crate::leanh::LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprLocalTimeType___closed__0_value:
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
    m_fun: l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__0_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
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
        116, 114, 97, 110, 115, 105, 116, 105, 111, 110, 84, 105, 109, 101, 0,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__1_value:
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
        l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(
            l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__1_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(
            l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__5_value:
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
    m_data: [99, 111, 114, 114, 101, 99, 116, 105, 111, 110, 0],
};
static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__6_value:
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
        l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__5_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprLeapSecond___closed__0_value:
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
    m_fun: l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprLeapSecond___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprLeapSecond___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [35, 91, 0]};
static mut l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9_value) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__7_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [35, 91, 93, 0]};
static mut l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__0_value:
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
    m_data: [104, 101, 97, 100, 101, 114, 0],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__1_value:
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
        l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__5_value:
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
        116, 114, 97, 110, 115, 105, 116, 105, 111, 110, 84, 105, 109, 101, 115, 0,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__6_value:
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
        l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__5_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__8_value:
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
        116, 114, 97, 110, 115, 105, 116, 105, 111, 110, 73, 110, 100, 105, 99, 101, 115, 0,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__9_value:
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
        l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__8_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__10_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
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
        108, 111, 99, 97, 108, 84, 105, 109, 101, 84, 121, 112, 101, 115, 0,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__11_value:
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
        l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__10_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__12_value:
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
        97, 98, 98, 114, 101, 118, 105, 97, 116, 105, 111, 110, 115, 0,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__13_value:
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
        l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__12_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__15_value:
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
    m_data: [108, 101, 97, 112, 83, 101, 99, 111, 110, 100, 115, 0],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__16_value:
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
        l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__15_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__18_value:
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
        115, 116, 100, 87, 97, 108, 108, 73, 110, 100, 105, 99, 97, 116, 111, 114, 115, 0,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__19_value:
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
        l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__18_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__20_value:
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
        117, 116, 76, 111, 99, 97, 108, 73, 110, 100, 105, 99, 97, 116, 111, 114, 115, 0,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__21_value:
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
        l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__20_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1___closed__0_value:
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
    m_fun: l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_TimeZone_TZif_instReprTZifV1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__0_value:
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
static mut l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedTZifV1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 111, 109, 101, 32, 0]};
static mut l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__3_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__0_value:
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
    m_data: [116, 111, 84, 90, 105, 102, 86, 49, 0],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__1_value:
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
        l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__4_value:
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
    m_data: [102, 111, 111, 116, 101, 114, 0],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__5_value:
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
        l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV2___closed__0_value:
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
    m_fun: l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_TimeZone_TZif_instReprTZifV2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV2___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedTZifV2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__0_value:
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
    m_data: [118, 49, 0],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__1_value:
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
        l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__5_value:
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
    m_data: [118, 50, 0],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__6_value:
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
        l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__5_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZif___closed__0_value:
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
    m_fun: l_Std_Time_TimeZone_TZif_instReprTZif_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZif___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZif___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_TimeZone_TZif_instReprTZif: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZif___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedTZif_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedTZif: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__0_value: crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [83, 116, 100, 46, 84, 105, 109, 101, 46, 90, 111, 110, 101, 100, 46, 68, 97, 116, 97, 98, 97, 115, 101, 46, 84, 122, 73, 102, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__1_value: crate::leanh::LeanStringObject<72> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 72, m_capacity: 72, m_length: 71, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 83, 116, 100, 46, 84, 105, 109, 101, 46, 90, 111, 110, 101, 100, 46, 68, 97, 116, 97, 98, 97, 115, 101, 46, 84, 122, 73, 102, 46, 48, 46, 83, 116, 100, 46, 84, 105, 109, 101, 46, 84, 105, 109, 101, 90, 111, 110, 101, 46, 84, 90, 105, 102, 46, 116, 111, 85, 73, 110, 116, 51, 50, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__2_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 98, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 52, 10, 32, 32, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [99, 111, 110, 100, 105, 116, 105, 111, 110, 32, 110, 111, 116, 32, 115, 97, 116, 105, 115, 102, 105, 101, 100, 0]};
static mut l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2319_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__0;
    v___x_2320_ = l_String_toRawSubstring_x27(v___x_2319_);
    return v___x_2320_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1(
    mut v_x_2334_: *mut crate::leanh::LeanObject,
    mut v_a_2335_: *mut crate::leanh::LeanObject,
    mut v_a_2336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: u8 = 0;
    v___x_2337_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__20;
    v___x_2338_ = l_Lean_Syntax_isOfKind(v_x_2334_, v___x_2337_);
    if v___x_2338_ == 0 {
        let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2339_ = crate::leanh::lean_box(1);
        v___x_2340_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2340_, 0, v___x_2339_);
        crate::leanh::lean_ctor_set(v___x_2340_, 1, v_a_2336_);
        return v___x_2340_;
    } else {
        let mut v_quotContext_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2344_: u8 = 0;
        let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2341_ = crate::leanh::lean_ctor_get(v_a_2335_, 1);
        v_currMacroScope_2342_ = crate::leanh::lean_ctor_get(v_a_2335_, 2);
        v_ref_2343_ = crate::leanh::lean_ctor_get(v_a_2335_, 5);
        v___x_2344_ = 0;
        v___x_2345_ = l_Lean_SourceInfo_fromRef(v_ref_2343_, v___x_2344_);
        v___x_2346_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1), core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1_once), _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1);
        v___x_2347_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__2;
        crate::leanh::lean_inc(v_currMacroScope_2342_);
        crate::leanh::lean_inc(v_quotContext_2341_);
        v___x_2348_ =
            l_Lean_addMacroScope(v_quotContext_2341_, v___x_2347_, v_currMacroScope_2342_);
        v___x_2349_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__6;
        v___x_2350_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2350_, 0, v___x_2345_);
        crate::leanh::lean_ctor_set(v___x_2350_, 1, v___x_2346_);
        crate::leanh::lean_ctor_set(v___x_2350_, 2, v___x_2348_);
        crate::leanh::lean_ctor_set(v___x_2350_, 3, v___x_2349_);
        v___x_2351_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2351_, 0, v___x_2350_);
        crate::leanh::lean_ctor_set(v___x_2351_, 1, v_a_2336_);
        return v___x_2351_;
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___boxed(
    mut v_x_2352_: *mut crate::leanh::LeanObject,
    mut v_a_2353_: *mut crate::leanh::LeanObject,
    mut v_a_2354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2355_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1(v_x_2352_, v_a_2353_, v_a_2354_);
    crate::leanh::lean_dec_ref(v_a_2353_);
    return v_res_2355_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1(
    mut v_x_2359_: *mut crate::leanh::LeanObject,
    mut v_a_2360_: *mut crate::leanh::LeanObject,
    mut v_a_2361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: u8 = 0;
    v___x_2362_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__1;
    crate::leanh::lean_inc(v_x_2359_);
    v___x_2363_ = l_Lean_Syntax_isOfKind(v_x_2359_, v___x_2362_);
    if v___x_2363_ == 0 {
        let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2359_);
        v___x_2364_ = crate::leanh::lean_box(0);
        v___x_2365_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2365_, 0, v___x_2364_);
        crate::leanh::lean_ctor_set(v___x_2365_, 1, v_a_2361_);
        return v___x_2365_;
    } else {
        let mut v_ref_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2367_: u8 = 0;
        let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_2366_ = l_Lean_replaceRef(v_x_2359_, v_a_2360_);
        crate::leanh::lean_dec(v_x_2359_);
        v___x_2367_ = 0;
        v___x_2368_ = l_Lean_SourceInfo_fromRef(v_ref_2366_, v___x_2367_);
        crate::leanh::lean_dec(v_ref_2366_);
        v___x_2369_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__20;
        v___x_2370_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__21;
        crate::leanh::lean_inc(v___x_2368_);
        v___x_2371_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2371_, 0, v___x_2368_);
        crate::leanh::lean_ctor_set(v___x_2371_, 1, v___x_2370_);
        v___x_2372_ = l_Lean_Syntax_node1(v___x_2368_, v___x_2369_, v___x_2371_);
        v___x_2373_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2373_, 0, v___x_2372_);
        crate::leanh::lean_ctor_set(v___x_2373_, 1, v_a_2361_);
        return v___x_2373_;
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___boxed(
    mut v_x_2374_: *mut crate::leanh::LeanObject,
    mut v_a_2375_: *mut crate::leanh::LeanObject,
    mut v_a_2376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2377_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1(v_x_2374_, v_a_2375_, v_a_2376_);
    crate::leanh::lean_dec(v_a_2375_);
    return v_res_2377_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt64__1(
    mut v_x_2390_: *mut crate::leanh::LeanObject,
    mut v_a_2391_: *mut crate::leanh::LeanObject,
    mut v_a_2392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: u8 = 0;
    v___x_2393_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__1;
    v___x_2394_ = l_Lean_Syntax_isOfKind(v_x_2390_, v___x_2393_);
    if v___x_2394_ == 0 {
        let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2395_ = crate::leanh::lean_box(1);
        v___x_2396_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2396_, 0, v___x_2395_);
        crate::leanh::lean_ctor_set(v___x_2396_, 1, v_a_2392_);
        return v___x_2396_;
    } else {
        let mut v_quotContext_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2400_: u8 = 0;
        let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_2397_ = crate::leanh::lean_ctor_get(v_a_2391_, 1);
        v_currMacroScope_2398_ = crate::leanh::lean_ctor_get(v_a_2391_, 2);
        v_ref_2399_ = crate::leanh::lean_ctor_get(v_a_2391_, 5);
        v___x_2400_ = 0;
        v___x_2401_ = l_Lean_SourceInfo_fromRef(v_ref_2399_, v___x_2400_);
        v___x_2402_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1), core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1_once), _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1);
        v___x_2403_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__2;
        crate::leanh::lean_inc(v_currMacroScope_2398_);
        crate::leanh::lean_inc(v_quotContext_2397_);
        v___x_2404_ =
            l_Lean_addMacroScope(v_quotContext_2397_, v___x_2403_, v_currMacroScope_2398_);
        v___x_2405_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__6;
        v___x_2406_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2406_, 0, v___x_2401_);
        crate::leanh::lean_ctor_set(v___x_2406_, 1, v___x_2402_);
        crate::leanh::lean_ctor_set(v___x_2406_, 2, v___x_2404_);
        crate::leanh::lean_ctor_set(v___x_2406_, 3, v___x_2405_);
        v___x_2407_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2407_, 0, v___x_2406_);
        crate::leanh::lean_ctor_set(v___x_2407_, 1, v_a_2392_);
        return v___x_2407_;
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt64__1___boxed(
    mut v_x_2408_: *mut crate::leanh::LeanObject,
    mut v_a_2409_: *mut crate::leanh::LeanObject,
    mut v_a_2410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2411_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt64__1(v_x_2408_, v_a_2409_, v_a_2410_);
    crate::leanh::lean_dec_ref(v_a_2409_);
    return v_res_2411_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__2(
    mut v_x_2412_: *mut crate::leanh::LeanObject,
    mut v_a_2413_: *mut crate::leanh::LeanObject,
    mut v_a_2414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: u8 = 0;
    v___x_2415_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__1;
    crate::leanh::lean_inc(v_x_2412_);
    v___x_2416_ = l_Lean_Syntax_isOfKind(v_x_2412_, v___x_2415_);
    if v___x_2416_ == 0 {
        let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2412_);
        v___x_2417_ = crate::leanh::lean_box(0);
        v___x_2418_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2418_, 0, v___x_2417_);
        crate::leanh::lean_ctor_set(v___x_2418_, 1, v_a_2414_);
        return v___x_2418_;
    } else {
        let mut v_ref_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2420_: u8 = 0;
        let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_2419_ = l_Lean_replaceRef(v_x_2412_, v_a_2413_);
        crate::leanh::lean_dec(v_x_2412_);
        v___x_2420_ = 0;
        v___x_2421_ = l_Lean_SourceInfo_fromRef(v_ref_2419_, v___x_2420_);
        crate::leanh::lean_dec(v_ref_2419_);
        v___x_2422_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__1;
        v___x_2423_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__2;
        crate::leanh::lean_inc(v___x_2421_);
        v___x_2424_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2424_, 0, v___x_2421_);
        crate::leanh::lean_ctor_set(v___x_2424_, 1, v___x_2423_);
        v___x_2425_ = l_Lean_Syntax_node1(v___x_2421_, v___x_2422_, v___x_2424_);
        v___x_2426_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2426_, 0, v___x_2425_);
        crate::leanh::lean_ctor_set(v___x_2426_, 1, v_a_2414_);
        return v___x_2426_;
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__2___boxed(
    mut v_x_2427_: *mut crate::leanh::LeanObject,
    mut v_a_2428_: *mut crate::leanh::LeanObject,
    mut v_a_2429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2430_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__2(v_x_2427_, v_a_2428_, v_a_2429_);
    crate::leanh::lean_dec(v_a_2428_);
    return v_res_2430_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_TimeZone_TZif_instReprHeader_repr_spec__0(
    mut v_a_2431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2432_ = lean_nat_to_int(v_a_2431_);
    return v___x_2432_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2446_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_2447_ = lean_nat_to_int(v___x_2446_);
    return v___x_2447_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2457_ = crate::leanh::lean_unsigned_to_nat(12);
    v___x_2458_ = lean_nat_to_int(v___x_2457_);
    return v___x_2458_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2472_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__0;
    v___x_2473_ = lean_string_length(v___x_2472_);
    return v___x_2473_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2474_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__24),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__24_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__24,
    );
    v___x_2475_ = lean_nat_to_int(v___x_2474_);
    return v___x_2475_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg(
    mut v_x_2480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_version_2481_: u8 = 0;
    let mut v_isutcnt_2482_: u32 = 0;
    let mut v_isstdcnt_2483_: u32 = 0;
    let mut v_leapcnt_2484_: u32 = 0;
    let mut v_timecnt_2485_: u32 = 0;
    let mut v_typecnt_2486_: u32 = 0;
    let mut v_charcnt_2487_: u32 = 0;
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: u8 = 0;
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_version_2481_ = crate::leanh::lean_ctor_get_uint8(v_x_2480_, 24 as u32);
    v_isutcnt_2482_ = crate::leanh::lean_ctor_get_uint32(v_x_2480_, 0 as u32);
    v_isstdcnt_2483_ = crate::leanh::lean_ctor_get_uint32(v_x_2480_, 4 as u32);
    v_leapcnt_2484_ = crate::leanh::lean_ctor_get_uint32(v_x_2480_, 8 as u32);
    v_timecnt_2485_ = crate::leanh::lean_ctor_get_uint32(v_x_2480_, 12 as u32);
    v_typecnt_2486_ = crate::leanh::lean_ctor_get_uint32(v_x_2480_, 16 as u32);
    v_charcnt_2487_ = crate::leanh::lean_ctor_get_uint32(v_x_2480_, 20 as u32);
    v___x_2488_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5;
    v___x_2489_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__6;
    v___x_2490_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__7_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__7,
    );
    v___x_2491_ = lean_uint8_to_nat(v_version_2481_);
    v___x_2492_ = l_Nat_reprFast(v___x_2491_);
    v___x_2493_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2493_, 0, v___x_2492_);
    v___x_2494_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2494_, 0, v___x_2490_);
    crate::leanh::lean_ctor_set(v___x_2494_, 1, v___x_2493_);
    v___x_2495_ = 0;
    v___x_2496_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2496_, 0, v___x_2494_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2496_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2495_,
    );
    v___x_2497_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2497_, 0, v___x_2489_);
    crate::leanh::lean_ctor_set(v___x_2497_, 1, v___x_2496_);
    v___x_2498_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9;
    v___x_2499_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2499_, 0, v___x_2497_);
    crate::leanh::lean_ctor_set(v___x_2499_, 1, v___x_2498_);
    v___x_2500_ = crate::leanh::lean_box(1);
    v___x_2501_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2501_, 0, v___x_2499_);
    crate::leanh::lean_ctor_set(v___x_2501_, 1, v___x_2500_);
    v___x_2502_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__11;
    v___x_2503_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2503_, 0, v___x_2501_);
    crate::leanh::lean_ctor_set(v___x_2503_, 1, v___x_2502_);
    v___x_2504_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2504_, 0, v___x_2503_);
    crate::leanh::lean_ctor_set(v___x_2504_, 1, v___x_2488_);
    v___x_2505_ = lean_uint32_to_nat(v_isutcnt_2482_);
    v___x_2506_ = l_Nat_reprFast(v___x_2505_);
    v___x_2507_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2507_, 0, v___x_2506_);
    v___x_2508_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2508_, 0, v___x_2490_);
    crate::leanh::lean_ctor_set(v___x_2508_, 1, v___x_2507_);
    v___x_2509_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2509_, 0, v___x_2508_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2509_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2495_,
    );
    v___x_2510_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2510_, 0, v___x_2504_);
    crate::leanh::lean_ctor_set(v___x_2510_, 1, v___x_2509_);
    v___x_2511_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2511_, 0, v___x_2510_);
    crate::leanh::lean_ctor_set(v___x_2511_, 1, v___x_2498_);
    v___x_2512_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2512_, 0, v___x_2511_);
    crate::leanh::lean_ctor_set(v___x_2512_, 1, v___x_2500_);
    v___x_2513_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__13;
    v___x_2514_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2514_, 0, v___x_2512_);
    crate::leanh::lean_ctor_set(v___x_2514_, 1, v___x_2513_);
    v___x_2515_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2515_, 0, v___x_2514_);
    crate::leanh::lean_ctor_set(v___x_2515_, 1, v___x_2488_);
    v___x_2516_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14,
    );
    v___x_2517_ = lean_uint32_to_nat(v_isstdcnt_2483_);
    v___x_2518_ = l_Nat_reprFast(v___x_2517_);
    v___x_2519_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2519_, 0, v___x_2518_);
    v___x_2520_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2520_, 0, v___x_2516_);
    crate::leanh::lean_ctor_set(v___x_2520_, 1, v___x_2519_);
    v___x_2521_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2521_, 0, v___x_2520_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2521_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2495_,
    );
    v___x_2522_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2522_, 0, v___x_2515_);
    crate::leanh::lean_ctor_set(v___x_2522_, 1, v___x_2521_);
    v___x_2523_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2523_, 0, v___x_2522_);
    crate::leanh::lean_ctor_set(v___x_2523_, 1, v___x_2498_);
    v___x_2524_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2524_, 0, v___x_2523_);
    crate::leanh::lean_ctor_set(v___x_2524_, 1, v___x_2500_);
    v___x_2525_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__16;
    v___x_2526_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2526_, 0, v___x_2524_);
    crate::leanh::lean_ctor_set(v___x_2526_, 1, v___x_2525_);
    v___x_2527_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2527_, 0, v___x_2526_);
    crate::leanh::lean_ctor_set(v___x_2527_, 1, v___x_2488_);
    v___x_2528_ = lean_uint32_to_nat(v_leapcnt_2484_);
    v___x_2529_ = l_Nat_reprFast(v___x_2528_);
    v___x_2530_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2530_, 0, v___x_2529_);
    v___x_2531_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2531_, 0, v___x_2490_);
    crate::leanh::lean_ctor_set(v___x_2531_, 1, v___x_2530_);
    v___x_2532_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2532_, 0, v___x_2531_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2532_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2495_,
    );
    v___x_2533_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2533_, 0, v___x_2527_);
    crate::leanh::lean_ctor_set(v___x_2533_, 1, v___x_2532_);
    v___x_2534_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2534_, 0, v___x_2533_);
    crate::leanh::lean_ctor_set(v___x_2534_, 1, v___x_2498_);
    v___x_2535_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2535_, 0, v___x_2534_);
    crate::leanh::lean_ctor_set(v___x_2535_, 1, v___x_2500_);
    v___x_2536_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__18;
    v___x_2537_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2537_, 0, v___x_2535_);
    crate::leanh::lean_ctor_set(v___x_2537_, 1, v___x_2536_);
    v___x_2538_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2538_, 0, v___x_2537_);
    crate::leanh::lean_ctor_set(v___x_2538_, 1, v___x_2488_);
    v___x_2539_ = lean_uint32_to_nat(v_timecnt_2485_);
    v___x_2540_ = l_Nat_reprFast(v___x_2539_);
    v___x_2541_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2541_, 0, v___x_2540_);
    v___x_2542_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2542_, 0, v___x_2490_);
    crate::leanh::lean_ctor_set(v___x_2542_, 1, v___x_2541_);
    v___x_2543_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2543_, 0, v___x_2542_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2543_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2495_,
    );
    v___x_2544_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2544_, 0, v___x_2538_);
    crate::leanh::lean_ctor_set(v___x_2544_, 1, v___x_2543_);
    v___x_2545_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2545_, 0, v___x_2544_);
    crate::leanh::lean_ctor_set(v___x_2545_, 1, v___x_2498_);
    v___x_2546_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2546_, 0, v___x_2545_);
    crate::leanh::lean_ctor_set(v___x_2546_, 1, v___x_2500_);
    v___x_2547_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__20;
    v___x_2548_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2548_, 0, v___x_2546_);
    crate::leanh::lean_ctor_set(v___x_2548_, 1, v___x_2547_);
    v___x_2549_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2549_, 0, v___x_2548_);
    crate::leanh::lean_ctor_set(v___x_2549_, 1, v___x_2488_);
    v___x_2550_ = lean_uint32_to_nat(v_typecnt_2486_);
    v___x_2551_ = l_Nat_reprFast(v___x_2550_);
    v___x_2552_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2552_, 0, v___x_2551_);
    v___x_2553_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2553_, 0, v___x_2490_);
    crate::leanh::lean_ctor_set(v___x_2553_, 1, v___x_2552_);
    v___x_2554_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2554_, 0, v___x_2553_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2554_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2495_,
    );
    v___x_2555_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2555_, 0, v___x_2549_);
    crate::leanh::lean_ctor_set(v___x_2555_, 1, v___x_2554_);
    v___x_2556_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2556_, 0, v___x_2555_);
    crate::leanh::lean_ctor_set(v___x_2556_, 1, v___x_2498_);
    v___x_2557_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2557_, 0, v___x_2556_);
    crate::leanh::lean_ctor_set(v___x_2557_, 1, v___x_2500_);
    v___x_2558_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__22;
    v___x_2559_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2559_, 0, v___x_2557_);
    crate::leanh::lean_ctor_set(v___x_2559_, 1, v___x_2558_);
    v___x_2560_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2560_, 0, v___x_2559_);
    crate::leanh::lean_ctor_set(v___x_2560_, 1, v___x_2488_);
    v___x_2561_ = lean_uint32_to_nat(v_charcnt_2487_);
    v___x_2562_ = l_Nat_reprFast(v___x_2561_);
    v___x_2563_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2563_, 0, v___x_2562_);
    v___x_2564_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2564_, 0, v___x_2490_);
    crate::leanh::lean_ctor_set(v___x_2564_, 1, v___x_2563_);
    v___x_2565_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2565_, 0, v___x_2564_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2565_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2495_,
    );
    v___x_2566_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2566_, 0, v___x_2560_);
    crate::leanh::lean_ctor_set(v___x_2566_, 1, v___x_2565_);
    v___x_2567_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25,
    );
    v___x_2568_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26;
    v___x_2569_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2569_, 0, v___x_2568_);
    crate::leanh::lean_ctor_set(v___x_2569_, 1, v___x_2566_);
    v___x_2570_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27;
    v___x_2571_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2571_, 0, v___x_2569_);
    crate::leanh::lean_ctor_set(v___x_2571_, 1, v___x_2570_);
    v___x_2572_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2572_, 0, v___x_2567_);
    crate::leanh::lean_ctor_set(v___x_2572_, 1, v___x_2571_);
    v___x_2573_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2573_, 0, v___x_2572_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2573_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2495_,
    );
    return v___x_2573_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___boxed(
    mut v_x_2574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2575_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg(v_x_2574_);
    crate::leanh::lean_dec_ref(v_x_2574_);
    return v_res_2575_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprHeader_repr(
    mut v_x_2576_: *mut crate::leanh::LeanObject,
    mut v_prec_2577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2578_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg(v_x_2576_);
    return v___x_2578_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprHeader_repr___boxed(
    mut v_x_2579_: *mut crate::leanh::LeanObject,
    mut v_prec_2580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2581_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr(v_x_2579_, v_prec_2580_);
    crate::leanh::lean_dec(v_prec_2580_);
    crate::leanh::lean_dec_ref(v_x_2579_);
    return v_res_2581_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0() -> u8 {
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: u8 = 0;
    v___x_2584_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2585_ = lean_uint8_of_nat(v___x_2584_);
    return v___x_2585_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__1() -> u32 {
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: u32 = 0;
    v___x_2586_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2587_ = lean_uint32_of_nat(v___x_2586_);
    return v___x_2587_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2588_: u32 = 0;
    let mut v___x_2589_: u8 = 0;
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2588_ = crate::leanh::lean_uint32_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__1_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__1,
    );
    v___x_2589_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0,
    );
    v___x_2590_ = crate::leanh::lean_alloc_ctor(0, 0, (25) as u32);
    crate::leanh::lean_ctor_set_uint8(v___x_2590_, 24 as u32, v___x_2589_);
    crate::leanh::lean_ctor_set_uint32(v___x_2590_, 0 as u32, v___x_2588_);
    crate::leanh::lean_ctor_set_uint32(v___x_2590_, 4 as u32, v___x_2588_);
    crate::leanh::lean_ctor_set_uint32(v___x_2590_, 8 as u32, v___x_2588_);
    crate::leanh::lean_ctor_set_uint32(v___x_2590_, 12 as u32, v___x_2588_);
    crate::leanh::lean_ctor_set_uint32(v___x_2590_, 16 as u32, v___x_2588_);
    crate::leanh::lean_ctor_set_uint32(v___x_2590_, 20 as u32, v___x_2588_);
    return v___x_2590_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2591_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__2_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__2,
    );
    return v___x_2591_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2592_ = l_Std_Time_TimeZone_TZif_instInhabitedHeader_default;
    return v___x_2592_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2602_ = crate::leanh::lean_unsigned_to_nat(13);
    v___x_2603_ = lean_nat_to_int(v___x_2602_);
    return v___x_2603_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2607_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_2608_ = lean_nat_to_int(v___x_2607_);
    return v___x_2608_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2612_ = crate::leanh::lean_unsigned_to_nat(21);
    v___x_2613_ = lean_nat_to_int(v___x_2612_);
    return v___x_2613_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2614_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2615_ = lean_nat_to_int(v___x_2614_);
    return v___x_2615_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(
    mut v_x_2616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_gmtOffset_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDst_2618_: u8 = 0;
    let mut v_abbreviationIndex_2619_: u8 = 0;
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: u8 = 0;
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: u8 = 0;
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_gmtOffset_2617_ = crate::leanh::lean_ctor_get(v_x_2616_, 0);
                v_isDst_2618_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_2616_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_abbreviationIndex_2619_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_2616_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                );
                v___x_2620_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5;
                v___x_2621_ =
                    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__3;
                v___x_2622_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4), core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4_once), _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4);
                v___x_2660_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2661_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11), core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once), _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
                v___x_2662_ = lean_int_dec_lt(v_gmtOffset_2617_, v___x_2661_);
                if v___x_2662_ == 0 {
                    v___x_2663_ = l_Int_repr(v_gmtOffset_2617_);
                    v___x_2664_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2664_, 0, v___x_2663_);
                    v___y_2624_ = v___x_2664_;
                    state = 1;
                    continue;
                } else {
                    v___x_2665_ = l_Int_repr(v_gmtOffset_2617_);
                    v___x_2666_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2666_, 0, v___x_2665_);
                    v___x_2667_ = l_Repr_addAppParen(v___x_2666_, v___x_2660_);
                    v___y_2624_ = v___x_2667_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2625_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2625_, 0, v___x_2622_);
                crate::leanh::lean_ctor_set(v___x_2625_, 1, v___y_2624_);
                v___x_2626_ = 0;
                v___x_2627_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2627_, 0, v___x_2625_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2627_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2626_,
                );
                v___x_2628_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2628_, 0, v___x_2621_);
                crate::leanh::lean_ctor_set(v___x_2628_, 1, v___x_2627_);
                v___x_2629_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9;
                v___x_2630_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2630_, 0, v___x_2628_);
                crate::leanh::lean_ctor_set(v___x_2630_, 1, v___x_2629_);
                v___x_2631_ = crate::leanh::lean_box(1);
                v___x_2632_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2632_, 0, v___x_2630_);
                crate::leanh::lean_ctor_set(v___x_2632_, 1, v___x_2631_);
                v___x_2633_ =
                    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__6;
                v___x_2634_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2634_, 0, v___x_2632_);
                crate::leanh::lean_ctor_set(v___x_2634_, 1, v___x_2633_);
                v___x_2635_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2635_, 0, v___x_2634_);
                crate::leanh::lean_ctor_set(v___x_2635_, 1, v___x_2620_);
                v___x_2636_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7), core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7_once), _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7);
                v___x_2637_ = l_Bool_repr___redArg(v_isDst_2618_);
                v___x_2638_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2638_, 0, v___x_2636_);
                crate::leanh::lean_ctor_set(v___x_2638_, 1, v___x_2637_);
                v___x_2639_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2639_, 0, v___x_2638_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2639_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2626_,
                );
                v___x_2640_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2640_, 0, v___x_2635_);
                crate::leanh::lean_ctor_set(v___x_2640_, 1, v___x_2639_);
                v___x_2641_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2641_, 0, v___x_2640_);
                crate::leanh::lean_ctor_set(v___x_2641_, 1, v___x_2629_);
                v___x_2642_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2642_, 0, v___x_2641_);
                crate::leanh::lean_ctor_set(v___x_2642_, 1, v___x_2631_);
                v___x_2643_ =
                    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__9;
                v___x_2644_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2644_, 0, v___x_2642_);
                crate::leanh::lean_ctor_set(v___x_2644_, 1, v___x_2643_);
                v___x_2645_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2645_, 0, v___x_2644_);
                crate::leanh::lean_ctor_set(v___x_2645_, 1, v___x_2620_);
                v___x_2646_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10), core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10_once), _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10);
                v___x_2647_ = lean_uint8_to_nat(v_abbreviationIndex_2619_);
                v___x_2648_ = l_Nat_reprFast(v___x_2647_);
                v___x_2649_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2649_, 0, v___x_2648_);
                v___x_2650_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2650_, 0, v___x_2646_);
                crate::leanh::lean_ctor_set(v___x_2650_, 1, v___x_2649_);
                v___x_2651_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2651_, 0, v___x_2650_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2651_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2626_,
                );
                v___x_2652_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2652_, 0, v___x_2645_);
                crate::leanh::lean_ctor_set(v___x_2652_, 1, v___x_2651_);
                v___x_2653_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25,
                );
                v___x_2654_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26;
                v___x_2655_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2655_, 0, v___x_2654_);
                crate::leanh::lean_ctor_set(v___x_2655_, 1, v___x_2652_);
                v___x_2656_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27;
                v___x_2657_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2657_, 0, v___x_2655_);
                crate::leanh::lean_ctor_set(v___x_2657_, 1, v___x_2656_);
                v___x_2658_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2658_, 0, v___x_2653_);
                crate::leanh::lean_ctor_set(v___x_2658_, 1, v___x_2657_);
                v___x_2659_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2659_, 0, v___x_2658_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2659_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2626_,
                );
                return v___x_2659_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___boxed(
    mut v_x_2668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2669_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_x_2668_);
    crate::leanh::lean_dec_ref(v_x_2668_);
    return v_res_2669_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr(
    mut v_x_2670_: *mut crate::leanh::LeanObject,
    mut v_prec_2671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2672_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_x_2670_);
    return v___x_2672_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___boxed(
    mut v_x_2673_: *mut crate::leanh::LeanObject,
    mut v_prec_2674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2675_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr(v_x_2673_, v_prec_2674_);
    crate::leanh::lean_dec(v_prec_2674_);
    crate::leanh::lean_dec_ref(v_x_2673_);
    return v_res_2675_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2678_: u8 = 0;
    let mut v___x_2679_: u8 = 0;
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2678_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0,
    );
    v___x_2679_ = 0;
    v___x_2680_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11
        ),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11,
    );
    v___x_2681_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_2681_, 0, v___x_2680_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2681_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2679_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2681_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
        v___x_2678_,
    );
    return v___x_2681_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2682_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default___closed__0_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default___closed__0,
    );
    return v___x_2682_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2683_ = l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default;
    return v___x_2683_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2693_ = crate::leanh::lean_unsigned_to_nat(18);
    v___x_2694_ = lean_nat_to_int(v___x_2693_);
    return v___x_2694_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2698_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_2699_ = lean_nat_to_int(v___x_2698_);
    return v___x_2699_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(
    mut v_x_2700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_transitionTime_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_correction_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2705_: u8 = 0;
    let mut v___y_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2709_: u8 = 0;
    let mut v___y_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: u8 = 0;
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: u8 = 0;
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: u8 = 0;
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2756_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_transitionTime_2701_ = crate::leanh::lean_ctor_get(v_x_2700_, 0);
                v_correction_2702_ = crate::leanh::lean_ctor_get(v_x_2700_, 1);
                v_isSharedCheck_2756_ = (!crate::leanh::lean_is_exclusive(v_x_2700_)) as u8;
                if v_isSharedCheck_2756_ == 0 {
                    v___x_2704_ = v_x_2700_;
                    v_isShared_2705_ = v_isSharedCheck_2756_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_correction_2702_);
                    crate::leanh::lean_inc(v_transitionTime_2701_);
                    crate::leanh::lean_dec(v_x_2700_);
                    v___x_2704_ = crate::leanh::lean_box(0);
                    v_isShared_2705_ = v_isSharedCheck_2756_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2723_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5;
                v___x_2724_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__3;
                v___x_2725_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4_once
                    ),
                    _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4,
                );
                v___x_2748_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2749_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11), core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once), _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
                v___x_2750_ = lean_int_dec_lt(v_transitionTime_2701_, v___x_2749_);
                if v___x_2750_ == 0 {
                    v___x_2751_ = l_Int_repr(v_transitionTime_2701_);
                    crate::leanh::lean_dec(v_transitionTime_2701_);
                    v___x_2752_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2752_, 0, v___x_2751_);
                    v___y_2727_ = v___x_2752_;
                    state = 4;
                    continue;
                } else {
                    v___x_2753_ = l_Int_repr(v_transitionTime_2701_);
                    crate::leanh::lean_dec(v_transitionTime_2701_);
                    v___x_2754_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2754_, 0, v___x_2753_);
                    v___x_2755_ = l_Repr_addAppParen(v___x_2754_, v___x_2748_);
                    v___y_2727_ = v___x_2755_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v___y_2707_);
                if v_isShared_2705_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2704_, 4);
                    crate::leanh::lean_ctor_set(v___x_2704_, 1, v___y_2710_);
                    crate::leanh::lean_ctor_set(v___x_2704_, 0, v___y_2707_);
                    v___x_2712_ = v___x_2704_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2722_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2722_, 0, v___y_2707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2722_, 1, v___y_2710_);
                    v___x_2712_ = v_reuseFailAlloc_2722_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2713_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2713_, 0, v___x_2712_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2713_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___y_2709_,
                );
                v___x_2714_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2714_, 0, v___y_2708_);
                crate::leanh::lean_ctor_set(v___x_2714_, 1, v___x_2713_);
                v___x_2715_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25,
                );
                v___x_2716_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26;
                v___x_2717_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2717_, 0, v___x_2716_);
                crate::leanh::lean_ctor_set(v___x_2717_, 1, v___x_2714_);
                v___x_2718_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27;
                v___x_2719_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2719_, 0, v___x_2717_);
                crate::leanh::lean_ctor_set(v___x_2719_, 1, v___x_2718_);
                v___x_2720_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2720_, 0, v___x_2715_);
                crate::leanh::lean_ctor_set(v___x_2720_, 1, v___x_2719_);
                v___x_2721_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2721_, 0, v___x_2720_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2721_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___y_2709_,
                );
                return v___x_2721_;
            }
            4 => {
                v___x_2728_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2728_, 0, v___x_2725_);
                crate::leanh::lean_ctor_set(v___x_2728_, 1, v___y_2727_);
                v___x_2729_ = 0;
                v___x_2730_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2730_, 0, v___x_2728_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2730_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2729_,
                );
                v___x_2731_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2731_, 0, v___x_2724_);
                crate::leanh::lean_ctor_set(v___x_2731_, 1, v___x_2730_);
                v___x_2732_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9;
                v___x_2733_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2733_, 0, v___x_2731_);
                crate::leanh::lean_ctor_set(v___x_2733_, 1, v___x_2732_);
                v___x_2734_ = crate::leanh::lean_box(1);
                v___x_2735_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2735_, 0, v___x_2733_);
                crate::leanh::lean_ctor_set(v___x_2735_, 1, v___x_2734_);
                v___x_2736_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__6;
                v___x_2737_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2737_, 0, v___x_2735_);
                crate::leanh::lean_ctor_set(v___x_2737_, 1, v___x_2736_);
                v___x_2738_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2738_, 0, v___x_2737_);
                crate::leanh::lean_ctor_set(v___x_2738_, 1, v___x_2723_);
                v___x_2739_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7_once
                    ),
                    _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7,
                );
                v___x_2740_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2741_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11), core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once), _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
                v___x_2742_ = lean_int_dec_lt(v_correction_2702_, v___x_2741_);
                if v___x_2742_ == 0 {
                    v___x_2743_ = l_Int_repr(v_correction_2702_);
                    crate::leanh::lean_dec(v_correction_2702_);
                    v___x_2744_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2744_, 0, v___x_2743_);
                    v___y_2707_ = v___x_2739_;
                    v___y_2708_ = v___x_2738_;
                    v___y_2709_ = v___x_2729_;
                    v___y_2710_ = v___x_2744_;
                    state = 2;
                    continue;
                } else {
                    v___x_2745_ = l_Int_repr(v_correction_2702_);
                    crate::leanh::lean_dec(v_correction_2702_);
                    v___x_2746_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2746_, 0, v___x_2745_);
                    v___x_2747_ = l_Repr_addAppParen(v___x_2746_, v___x_2740_);
                    v___y_2707_ = v___x_2739_;
                    v___y_2708_ = v___x_2738_;
                    v___y_2709_ = v___x_2729_;
                    v___y_2710_ = v___x_2747_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr(
    mut v_x_2757_: *mut crate::leanh::LeanObject,
    mut v_prec_2758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2759_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_x_2757_);
    return v___x_2759_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___boxed(
    mut v_x_2760_: *mut crate::leanh::LeanObject,
    mut v_prec_2761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2762_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr(v_x_2760_, v_prec_2761_);
    crate::leanh::lean_dec(v_prec_2761_);
    return v_res_2762_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2765_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11
        ),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11,
    );
    v___x_2766_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2766_, 0, v___x_2765_);
    crate::leanh::lean_ctor_set(v___x_2766_, 1, v___x_2765_);
    return v___x_2766_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2767_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default___closed__0_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default___closed__0,
    );
    return v___x_2767_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2768_ = l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default;
    return v___x_2768_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10_spec__16_spec__22(
    mut v_x_2769_: *mut crate::leanh::LeanObject,
    mut v_x_2770_: *mut crate::leanh::LeanObject,
    mut v_x_2771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2776_: u8 = 0;
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: u8 = 0;
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2784_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2771_) == 0 {
                    crate::leanh::lean_dec(v_x_2769_);
                    return v_x_2770_;
                } else {
                    v_head_2772_ = crate::leanh::lean_ctor_get(v_x_2771_, 0);
                    v_tail_2773_ = crate::leanh::lean_ctor_get(v_x_2771_, 1);
                    v_isSharedCheck_2784_ = (!crate::leanh::lean_is_exclusive(v_x_2771_)) as u8;
                    if v_isSharedCheck_2784_ == 0 {
                        v___x_2775_ = v_x_2771_;
                        v_isShared_2776_ = v_isSharedCheck_2784_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2773_);
                        crate::leanh::lean_inc(v_head_2772_);
                        crate::leanh::lean_dec(v_x_2771_);
                        v___x_2775_ = crate::leanh::lean_box(0);
                        v_isShared_2776_ = v_isSharedCheck_2784_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_2769_);
                if v_isShared_2776_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2775_, 5);
                    crate::leanh::lean_ctor_set(v___x_2775_, 1, v_x_2769_);
                    crate::leanh::lean_ctor_set(v___x_2775_, 0, v_x_2770_);
                    v___x_2778_ = v___x_2775_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2783_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_x_2770_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2783_, 1, v_x_2769_);
                    v___x_2778_ = v_reuseFailAlloc_2783_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2779_ = (crate::leanh::lean_unbox(v_head_2772_) as u8);
                crate::leanh::lean_dec(v_head_2772_);
                v___x_2780_ = l_Bool_repr___redArg(v___x_2779_);
                v___x_2781_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2781_, 0, v___x_2778_);
                crate::leanh::lean_ctor_set(v___x_2781_, 1, v___x_2780_);
                v_x_2770_ = v___x_2781_;
                v_x_2771_ = v_tail_2773_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10_spec__16(
    mut v_x_2785_: *mut crate::leanh::LeanObject,
    mut v_x_2786_: *mut crate::leanh::LeanObject,
    mut v_x_2787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2792_: u8 = 0;
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: u8 = 0;
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2800_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2787_) == 0 {
                    crate::leanh::lean_dec(v_x_2785_);
                    return v_x_2786_;
                } else {
                    v_head_2788_ = crate::leanh::lean_ctor_get(v_x_2787_, 0);
                    v_tail_2789_ = crate::leanh::lean_ctor_get(v_x_2787_, 1);
                    v_isSharedCheck_2800_ = (!crate::leanh::lean_is_exclusive(v_x_2787_)) as u8;
                    if v_isSharedCheck_2800_ == 0 {
                        v___x_2791_ = v_x_2787_;
                        v_isShared_2792_ = v_isSharedCheck_2800_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2789_);
                        crate::leanh::lean_inc(v_head_2788_);
                        crate::leanh::lean_dec(v_x_2787_);
                        v___x_2791_ = crate::leanh::lean_box(0);
                        v_isShared_2792_ = v_isSharedCheck_2800_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_2785_);
                if v_isShared_2792_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2791_, 5);
                    crate::leanh::lean_ctor_set(v___x_2791_, 1, v_x_2785_);
                    crate::leanh::lean_ctor_set(v___x_2791_, 0, v_x_2786_);
                    v___x_2794_ = v___x_2791_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2799_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_x_2786_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2799_, 1, v_x_2785_);
                    v___x_2794_ = v_reuseFailAlloc_2799_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2795_ = (crate::leanh::lean_unbox(v_head_2788_) as u8);
                crate::leanh::lean_dec(v_head_2788_);
                v___x_2796_ = l_Bool_repr___redArg(v___x_2795_);
                v___x_2797_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2797_, 0, v___x_2794_);
                crate::leanh::lean_ctor_set(v___x_2797_, 1, v___x_2796_);
                v___x_2798_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10_spec__16_spec__22(v_x_2785_, v___x_2797_, v_tail_2789_);
                return v___x_2798_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10(
    mut v_x_2801_: *mut crate::leanh::LeanObject,
    mut v_x_2802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2801_) == 0 {
        let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2802_);
        v___x_2803_ = crate::leanh::lean_box(0);
        return v___x_2803_;
    } else {
        let mut v_tail_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_2804_ = crate::leanh::lean_ctor_get(v_x_2801_, 1);
        if crate::leanh::lean_obj_tag(v_tail_2804_) == 0 {
            let mut v_head_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2806_: u8 = 0;
            let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_2802_);
            v_head_2805_ = crate::leanh::lean_ctor_get(v_x_2801_, 0);
            crate::leanh::lean_inc(v_head_2805_);
            crate::leanh::lean_dec_ref_known(v_x_2801_, 2);
            v___x_2806_ = (crate::leanh::lean_unbox(v_head_2805_) as u8);
            crate::leanh::lean_dec(v_head_2805_);
            v___x_2807_ = l_Bool_repr___redArg(v___x_2806_);
            return v___x_2807_;
        } else {
            let mut v_head_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2809_: u8 = 0;
            let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_2804_);
            v_head_2808_ = crate::leanh::lean_ctor_get(v_x_2801_, 0);
            crate::leanh::lean_inc(v_head_2808_);
            crate::leanh::lean_dec_ref_known(v_x_2801_, 2);
            v___x_2809_ = (crate::leanh::lean_unbox(v_head_2808_) as u8);
            crate::leanh::lean_dec(v_head_2808_);
            v___x_2810_ = l_Bool_repr___redArg(v___x_2809_);
            v___x_2811_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10_spec__16(v_x_2802_, v___x_2810_, v_tail_2804_);
            return v___x_2811_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2817_ =
        l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__0;
    v___x_2818_ = lean_string_length(v___x_2817_);
    return v___x_2818_;
}
pub unsafe fn _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2819_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3_once), _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3);
    v___x_2820_ = lean_nat_to_int(v___x_2819_);
    return v___x_2820_;
}
pub unsafe fn l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5(
    mut v_xs_2828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: u8 = 0;
    v___x_2829_ = lean_array_get_size(v_xs_2828_);
    v___x_2830_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2831_ = lean_nat_dec_eq(v___x_2829_, v___x_2830_);
    if v___x_2831_ == 0 {
        let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2832_ = lean_array_to_list(v_xs_2828_);
        v___x_2833_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1;
        v___x_2834_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10(v___x_2832_, v___x_2833_);
        v___x_2835_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once), _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
        v___x_2836_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5;
        v___x_2837_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2837_, 0, v___x_2836_);
        crate::leanh::lean_ctor_set(v___x_2837_, 1, v___x_2834_);
        v___x_2838_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6;
        v___x_2839_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2839_, 0, v___x_2837_);
        crate::leanh::lean_ctor_set(v___x_2839_, 1, v___x_2838_);
        v___x_2840_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2840_, 0, v___x_2835_);
        crate::leanh::lean_ctor_set(v___x_2840_, 1, v___x_2839_);
        v___x_2841_ = l_Std_Format_fill(v___x_2840_);
        return v___x_2841_;
    } else {
        let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_2828_);
        v___x_2842_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8;
        return v___x_2842_;
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6___lam__0(
    mut v___y_2843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2844_ = l_String_quote(v___y_2843_);
    v___x_2845_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2845_, 0, v___x_2844_);
    return v___x_2845_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6_spec__10_spec__16(
    mut v_x_2846_: *mut crate::leanh::LeanObject,
    mut v_x_2847_: *mut crate::leanh::LeanObject,
    mut v_x_2848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2853_: u8 = 0;
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2848_) == 0 {
                    crate::leanh::lean_dec(v_x_2846_);
                    return v_x_2847_;
                } else {
                    v_head_2849_ = crate::leanh::lean_ctor_get(v_x_2848_, 0);
                    v_tail_2850_ = crate::leanh::lean_ctor_get(v_x_2848_, 1);
                    v_isSharedCheck_2861_ = (!crate::leanh::lean_is_exclusive(v_x_2848_)) as u8;
                    if v_isSharedCheck_2861_ == 0 {
                        v___x_2852_ = v_x_2848_;
                        v_isShared_2853_ = v_isSharedCheck_2861_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2850_);
                        crate::leanh::lean_inc(v_head_2849_);
                        crate::leanh::lean_dec(v_x_2848_);
                        v___x_2852_ = crate::leanh::lean_box(0);
                        v_isShared_2853_ = v_isSharedCheck_2861_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_2846_);
                if v_isShared_2853_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2852_, 5);
                    crate::leanh::lean_ctor_set(v___x_2852_, 1, v_x_2846_);
                    crate::leanh::lean_ctor_set(v___x_2852_, 0, v_x_2847_);
                    v___x_2855_ = v___x_2852_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2860_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_x_2847_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2860_, 1, v_x_2846_);
                    v___x_2855_ = v_reuseFailAlloc_2860_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2856_ = l_String_quote(v_head_2849_);
                v___x_2857_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2857_, 0, v___x_2856_);
                v___x_2858_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2858_, 0, v___x_2855_);
                crate::leanh::lean_ctor_set(v___x_2858_, 1, v___x_2857_);
                v_x_2847_ = v___x_2858_;
                v_x_2848_ = v_tail_2850_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6_spec__10(
    mut v_x_2862_: *mut crate::leanh::LeanObject,
    mut v_x_2863_: *mut crate::leanh::LeanObject,
    mut v_x_2864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2869_: u8 = 0;
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2877_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2864_) == 0 {
                    crate::leanh::lean_dec(v_x_2862_);
                    return v_x_2863_;
                } else {
                    v_head_2865_ = crate::leanh::lean_ctor_get(v_x_2864_, 0);
                    v_tail_2866_ = crate::leanh::lean_ctor_get(v_x_2864_, 1);
                    v_isSharedCheck_2877_ = (!crate::leanh::lean_is_exclusive(v_x_2864_)) as u8;
                    if v_isSharedCheck_2877_ == 0 {
                        v___x_2868_ = v_x_2864_;
                        v_isShared_2869_ = v_isSharedCheck_2877_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2866_);
                        crate::leanh::lean_inc(v_head_2865_);
                        crate::leanh::lean_dec(v_x_2864_);
                        v___x_2868_ = crate::leanh::lean_box(0);
                        v_isShared_2869_ = v_isSharedCheck_2877_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_2862_);
                if v_isShared_2869_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2868_, 5);
                    crate::leanh::lean_ctor_set(v___x_2868_, 1, v_x_2862_);
                    crate::leanh::lean_ctor_set(v___x_2868_, 0, v_x_2863_);
                    v___x_2871_ = v___x_2868_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2876_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_x_2863_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_x_2862_);
                    v___x_2871_ = v_reuseFailAlloc_2876_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2872_ = l_String_quote(v_head_2865_);
                v___x_2873_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2873_, 0, v___x_2872_);
                v___x_2874_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2874_, 0, v___x_2871_);
                crate::leanh::lean_ctor_set(v___x_2874_, 1, v___x_2873_);
                v___x_2875_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6_spec__10_spec__16(v_x_2862_, v___x_2874_, v_tail_2866_);
                return v___x_2875_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6(
    mut v_x_2878_: *mut crate::leanh::LeanObject,
    mut v_x_2879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2878_) == 0 {
        let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2879_);
        v___x_2880_ = crate::leanh::lean_box(0);
        return v___x_2880_;
    } else {
        let mut v_tail_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_2881_ = crate::leanh::lean_ctor_get(v_x_2878_, 1);
        if crate::leanh::lean_obj_tag(v_tail_2881_) == 0 {
            let mut v_head_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_2879_);
            v_head_2882_ = crate::leanh::lean_ctor_get(v_x_2878_, 0);
            crate::leanh::lean_inc(v_head_2882_);
            crate::leanh::lean_dec_ref_known(v_x_2878_, 2);
            v___x_2883_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6___lam__0(v_head_2882_);
            return v___x_2883_;
        } else {
            let mut v_head_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_2881_);
            v_head_2884_ = crate::leanh::lean_ctor_get(v_x_2878_, 0);
            crate::leanh::lean_inc(v_head_2884_);
            crate::leanh::lean_dec_ref_known(v_x_2878_, 2);
            v___x_2885_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6___lam__0(v_head_2884_);
            v___x_2886_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6_spec__10(v_x_2879_, v___x_2885_, v_tail_2881_);
            return v___x_2886_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3(
    mut v_xs_2887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: u8 = 0;
    v___x_2888_ = lean_array_get_size(v_xs_2887_);
    v___x_2889_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2890_ = lean_nat_dec_eq(v___x_2888_, v___x_2889_);
    if v___x_2890_ == 0 {
        let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2891_ = lean_array_to_list(v_xs_2887_);
        v___x_2892_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1;
        v___x_2893_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6(v___x_2891_, v___x_2892_);
        v___x_2894_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once), _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
        v___x_2895_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5;
        v___x_2896_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2896_, 0, v___x_2895_);
        crate::leanh::lean_ctor_set(v___x_2896_, 1, v___x_2893_);
        v___x_2897_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6;
        v___x_2898_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2898_, 0, v___x_2896_);
        crate::leanh::lean_ctor_set(v___x_2898_, 1, v___x_2897_);
        v___x_2899_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2899_, 0, v___x_2894_);
        crate::leanh::lean_ctor_set(v___x_2899_, 1, v___x_2898_);
        v___x_2900_ = l_Std_Format_fill(v___x_2899_);
        return v___x_2900_;
    } else {
        let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_2887_);
        v___x_2901_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8;
        return v___x_2901_;
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2_spec__4_spec__10(
    mut v_x_2902_: *mut crate::leanh::LeanObject,
    mut v_x_2903_: *mut crate::leanh::LeanObject,
    mut v_x_2904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2909_: u8 = 0;
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: u8 = 0;
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2919_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2904_) == 0 {
                    crate::leanh::lean_dec(v_x_2902_);
                    return v_x_2903_;
                } else {
                    v_head_2905_ = crate::leanh::lean_ctor_get(v_x_2904_, 0);
                    v_tail_2906_ = crate::leanh::lean_ctor_get(v_x_2904_, 1);
                    v_isSharedCheck_2919_ = (!crate::leanh::lean_is_exclusive(v_x_2904_)) as u8;
                    if v_isSharedCheck_2919_ == 0 {
                        v___x_2908_ = v_x_2904_;
                        v_isShared_2909_ = v_isSharedCheck_2919_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2906_);
                        crate::leanh::lean_inc(v_head_2905_);
                        crate::leanh::lean_dec(v_x_2904_);
                        v___x_2908_ = crate::leanh::lean_box(0);
                        v_isShared_2909_ = v_isSharedCheck_2919_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_2902_);
                if v_isShared_2909_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2908_, 5);
                    crate::leanh::lean_ctor_set(v___x_2908_, 1, v_x_2902_);
                    crate::leanh::lean_ctor_set(v___x_2908_, 0, v_x_2903_);
                    v___x_2911_ = v___x_2908_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2918_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_x_2903_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_x_2902_);
                    v___x_2911_ = v_reuseFailAlloc_2918_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2912_ = (crate::leanh::lean_unbox(v_head_2905_) as u8);
                crate::leanh::lean_dec(v_head_2905_);
                v___x_2913_ = lean_uint8_to_nat(v___x_2912_);
                v___x_2914_ = l_Nat_reprFast(v___x_2913_);
                v___x_2915_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2915_, 0, v___x_2914_);
                v___x_2916_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2916_, 0, v___x_2911_);
                crate::leanh::lean_ctor_set(v___x_2916_, 1, v___x_2915_);
                v_x_2903_ = v___x_2916_;
                v_x_2904_ = v_tail_2906_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2_spec__4(
    mut v_x_2920_: *mut crate::leanh::LeanObject,
    mut v_x_2921_: *mut crate::leanh::LeanObject,
    mut v_x_2922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2927_: u8 = 0;
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: u8 = 0;
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2937_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2922_) == 0 {
                    crate::leanh::lean_dec(v_x_2920_);
                    return v_x_2921_;
                } else {
                    v_head_2923_ = crate::leanh::lean_ctor_get(v_x_2922_, 0);
                    v_tail_2924_ = crate::leanh::lean_ctor_get(v_x_2922_, 1);
                    v_isSharedCheck_2937_ = (!crate::leanh::lean_is_exclusive(v_x_2922_)) as u8;
                    if v_isSharedCheck_2937_ == 0 {
                        v___x_2926_ = v_x_2922_;
                        v_isShared_2927_ = v_isSharedCheck_2937_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2924_);
                        crate::leanh::lean_inc(v_head_2923_);
                        crate::leanh::lean_dec(v_x_2922_);
                        v___x_2926_ = crate::leanh::lean_box(0);
                        v_isShared_2927_ = v_isSharedCheck_2937_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_2920_);
                if v_isShared_2927_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2926_, 5);
                    crate::leanh::lean_ctor_set(v___x_2926_, 1, v_x_2920_);
                    crate::leanh::lean_ctor_set(v___x_2926_, 0, v_x_2921_);
                    v___x_2929_ = v___x_2926_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2936_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_x_2921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2936_, 1, v_x_2920_);
                    v___x_2929_ = v_reuseFailAlloc_2936_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2930_ = (crate::leanh::lean_unbox(v_head_2923_) as u8);
                crate::leanh::lean_dec(v_head_2923_);
                v___x_2931_ = lean_uint8_to_nat(v___x_2930_);
                v___x_2932_ = l_Nat_reprFast(v___x_2931_);
                v___x_2933_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2933_, 0, v___x_2932_);
                v___x_2934_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2934_, 0, v___x_2929_);
                crate::leanh::lean_ctor_set(v___x_2934_, 1, v___x_2933_);
                v___x_2935_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2_spec__4_spec__10(v_x_2920_, v___x_2934_, v_tail_2924_);
                return v___x_2935_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(
    mut v___y_2938_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2939_ = lean_uint8_to_nat(v___y_2938_);
    v___x_2940_ = l_Nat_reprFast(v___x_2939_);
    v___x_2941_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2941_, 0, v___x_2940_);
    return v___x_2941_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0___boxed(
    mut v___y_2942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1967__boxed_2943_: u8 = 0;
    let mut v_res_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_1967__boxed_2943_ = (crate::leanh::lean_unbox(v___y_2942_) as u8);
    v_res_2944_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(v___y_1967__boxed_2943_);
    return v_res_2944_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2(
    mut v_x_2945_: *mut crate::leanh::LeanObject,
    mut v_x_2946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2945_) == 0 {
        let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2946_);
        v___x_2947_ = crate::leanh::lean_box(0);
        return v___x_2947_;
    } else {
        let mut v_tail_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_2948_ = crate::leanh::lean_ctor_get(v_x_2945_, 1);
        if crate::leanh::lean_obj_tag(v_tail_2948_) == 0 {
            let mut v_head_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2950_: u8 = 0;
            let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_2946_);
            v_head_2949_ = crate::leanh::lean_ctor_get(v_x_2945_, 0);
            crate::leanh::lean_inc(v_head_2949_);
            crate::leanh::lean_dec_ref_known(v_x_2945_, 2);
            v___x_2950_ = (crate::leanh::lean_unbox(v_head_2949_) as u8);
            crate::leanh::lean_dec(v_head_2949_);
            v___x_2951_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(v___x_2950_);
            return v___x_2951_;
        } else {
            let mut v_head_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2953_: u8 = 0;
            let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_2948_);
            v_head_2952_ = crate::leanh::lean_ctor_get(v_x_2945_, 0);
            crate::leanh::lean_inc(v_head_2952_);
            crate::leanh::lean_dec_ref_known(v_x_2945_, 2);
            v___x_2953_ = (crate::leanh::lean_unbox(v_head_2952_) as u8);
            crate::leanh::lean_dec(v_head_2952_);
            v___x_2954_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(v___x_2953_);
            v___x_2955_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2_spec__4(v_x_2946_, v___x_2954_, v_tail_2948_);
            return v___x_2955_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1(
    mut v_xs_2956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: u8 = 0;
    v___x_2957_ = lean_array_get_size(v_xs_2956_);
    v___x_2958_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2959_ = lean_nat_dec_eq(v___x_2957_, v___x_2958_);
    if v___x_2959_ == 0 {
        let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2960_ = lean_array_to_list(v_xs_2956_);
        v___x_2961_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1;
        v___x_2962_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2(v___x_2960_, v___x_2961_);
        v___x_2963_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once), _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
        v___x_2964_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5;
        v___x_2965_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2965_, 0, v___x_2964_);
        crate::leanh::lean_ctor_set(v___x_2965_, 1, v___x_2962_);
        v___x_2966_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6;
        v___x_2967_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2967_, 0, v___x_2965_);
        crate::leanh::lean_ctor_set(v___x_2967_, 1, v___x_2966_);
        v___x_2968_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2968_, 0, v___x_2963_);
        crate::leanh::lean_ctor_set(v___x_2968_, 1, v___x_2967_);
        v___x_2969_ = l_Std_Format_fill(v___x_2968_);
        return v___x_2969_;
    } else {
        let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_2956_);
        v___x_2970_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8;
        return v___x_2970_;
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1_spec__7(
    mut v_x_2971_: *mut crate::leanh::LeanObject,
    mut v_x_2972_: *mut crate::leanh::LeanObject,
    mut v_x_2973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2978_: u8 = 0;
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: u8 = 0;
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2994_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2973_) == 0 {
                    crate::leanh::lean_dec(v_x_2971_);
                    return v_x_2972_;
                } else {
                    v_head_2974_ = crate::leanh::lean_ctor_get(v_x_2973_, 0);
                    v_tail_2975_ = crate::leanh::lean_ctor_get(v_x_2973_, 1);
                    v_isSharedCheck_2994_ = (!crate::leanh::lean_is_exclusive(v_x_2973_)) as u8;
                    if v_isSharedCheck_2994_ == 0 {
                        v___x_2977_ = v_x_2973_;
                        v_isShared_2978_ = v_isSharedCheck_2994_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2975_);
                        crate::leanh::lean_inc(v_head_2974_);
                        crate::leanh::lean_dec(v_x_2973_);
                        v___x_2977_ = crate::leanh::lean_box(0);
                        v_isShared_2978_ = v_isSharedCheck_2994_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_2971_);
                if v_isShared_2978_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2977_, 5);
                    crate::leanh::lean_ctor_set(v___x_2977_, 1, v_x_2971_);
                    crate::leanh::lean_ctor_set(v___x_2977_, 0, v_x_2972_);
                    v___x_2980_ = v___x_2977_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2993_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_x_2972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_x_2971_);
                    v___x_2980_ = v_reuseFailAlloc_2993_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2981_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2982_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11), core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once), _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
                v___x_2983_ = lean_int_dec_lt(v_head_2974_, v___x_2982_);
                if v___x_2983_ == 0 {
                    v___x_2984_ = l_Int_repr(v_head_2974_);
                    crate::leanh::lean_dec(v_head_2974_);
                    v___x_2985_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2985_, 0, v___x_2984_);
                    v___x_2986_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2986_, 0, v___x_2980_);
                    crate::leanh::lean_ctor_set(v___x_2986_, 1, v___x_2985_);
                    v_x_2972_ = v___x_2986_;
                    v_x_2973_ = v_tail_2975_;
                    state = 0;
                    continue;
                } else {
                    v___x_2988_ = l_Int_repr(v_head_2974_);
                    crate::leanh::lean_dec(v_head_2974_);
                    v___x_2989_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2989_, 0, v___x_2988_);
                    v___x_2990_ = l_Repr_addAppParen(v___x_2989_, v___x_2981_);
                    v___x_2991_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2991_, 0, v___x_2980_);
                    crate::leanh::lean_ctor_set(v___x_2991_, 1, v___x_2990_);
                    v_x_2972_ = v___x_2991_;
                    v_x_2973_ = v_tail_2975_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1(
    mut v_x_2995_: *mut crate::leanh::LeanObject,
    mut v_x_2996_: *mut crate::leanh::LeanObject,
    mut v_x_2997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3002_: u8 = 0;
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: u8 = 0;
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3018_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2997_) == 0 {
                    crate::leanh::lean_dec(v_x_2995_);
                    return v_x_2996_;
                } else {
                    v_head_2998_ = crate::leanh::lean_ctor_get(v_x_2997_, 0);
                    v_tail_2999_ = crate::leanh::lean_ctor_get(v_x_2997_, 1);
                    v_isSharedCheck_3018_ = (!crate::leanh::lean_is_exclusive(v_x_2997_)) as u8;
                    if v_isSharedCheck_3018_ == 0 {
                        v___x_3001_ = v_x_2997_;
                        v_isShared_3002_ = v_isSharedCheck_3018_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2999_);
                        crate::leanh::lean_inc(v_head_2998_);
                        crate::leanh::lean_dec(v_x_2997_);
                        v___x_3001_ = crate::leanh::lean_box(0);
                        v_isShared_3002_ = v_isSharedCheck_3018_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_2995_);
                if v_isShared_3002_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3001_, 5);
                    crate::leanh::lean_ctor_set(v___x_3001_, 1, v_x_2995_);
                    crate::leanh::lean_ctor_set(v___x_3001_, 0, v_x_2996_);
                    v___x_3004_ = v___x_3001_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3017_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_x_2996_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3017_, 1, v_x_2995_);
                    v___x_3004_ = v_reuseFailAlloc_3017_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3005_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3006_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11), core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once), _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
                v___x_3007_ = lean_int_dec_lt(v_head_2998_, v___x_3006_);
                if v___x_3007_ == 0 {
                    v___x_3008_ = l_Int_repr(v_head_2998_);
                    crate::leanh::lean_dec(v_head_2998_);
                    v___x_3009_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3009_, 0, v___x_3008_);
                    v___x_3010_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3010_, 0, v___x_3004_);
                    crate::leanh::lean_ctor_set(v___x_3010_, 1, v___x_3009_);
                    v___x_3011_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1_spec__7(v_x_2995_, v___x_3010_, v_tail_2999_);
                    return v___x_3011_;
                } else {
                    v___x_3012_ = l_Int_repr(v_head_2998_);
                    crate::leanh::lean_dec(v_head_2998_);
                    v___x_3013_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3013_, 0, v___x_3012_);
                    v___x_3014_ = l_Repr_addAppParen(v___x_3013_, v___x_3005_);
                    v___x_3015_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3015_, 0, v___x_3004_);
                    crate::leanh::lean_ctor_set(v___x_3015_, 1, v___x_3014_);
                    v___x_3016_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1_spec__7(v_x_2995_, v___x_3015_, v_tail_2999_);
                    return v___x_3016_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(
    mut v___y_3019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: u8 = 0;
    v___x_3020_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3021_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11
        ),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11,
    );
    v___x_3022_ = lean_int_dec_lt(v___y_3019_, v___x_3021_);
    if v___x_3022_ == 0 {
        let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3023_ = l_Int_repr(v___y_3019_);
        v___x_3024_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3024_, 0, v___x_3023_);
        return v___x_3024_;
    } else {
        let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3025_ = l_Int_repr(v___y_3019_);
        v___x_3026_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3026_, 0, v___x_3025_);
        v___x_3027_ = l_Repr_addAppParen(v___x_3026_, v___x_3020_);
        return v___x_3027_;
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0___boxed(
    mut v___y_3028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3029_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(v___y_3028_);
    crate::leanh::lean_dec(v___y_3028_);
    return v_res_3029_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0(
    mut v_x_3030_: *mut crate::leanh::LeanObject,
    mut v_x_3031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3030_) == 0 {
        let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_3031_);
        v___x_3032_ = crate::leanh::lean_box(0);
        return v___x_3032_;
    } else {
        let mut v_tail_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_3033_ = crate::leanh::lean_ctor_get(v_x_3030_, 1);
        if crate::leanh::lean_obj_tag(v_tail_3033_) == 0 {
            let mut v_head_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_3031_);
            v_head_3034_ = crate::leanh::lean_ctor_get(v_x_3030_, 0);
            crate::leanh::lean_inc(v_head_3034_);
            crate::leanh::lean_dec_ref_known(v_x_3030_, 2);
            v___x_3035_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(v_head_3034_);
            crate::leanh::lean_dec(v_head_3034_);
            return v___x_3035_;
        } else {
            let mut v_head_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_3033_);
            v_head_3036_ = crate::leanh::lean_ctor_get(v_x_3030_, 0);
            crate::leanh::lean_inc(v_head_3036_);
            crate::leanh::lean_dec_ref_known(v_x_3030_, 2);
            v___x_3037_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(v_head_3036_);
            crate::leanh::lean_dec(v_head_3036_);
            v___x_3038_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1(v_x_3031_, v___x_3037_, v_tail_3033_);
            return v___x_3038_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0(
    mut v_xs_3039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: u8 = 0;
    v___x_3040_ = lean_array_get_size(v_xs_3039_);
    v___x_3041_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3042_ = lean_nat_dec_eq(v___x_3040_, v___x_3041_);
    if v___x_3042_ == 0 {
        let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3043_ = lean_array_to_list(v_xs_3039_);
        v___x_3044_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1;
        v___x_3045_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0(v___x_3043_, v___x_3044_);
        v___x_3046_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once), _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
        v___x_3047_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5;
        v___x_3048_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3048_, 0, v___x_3047_);
        crate::leanh::lean_ctor_set(v___x_3048_, 1, v___x_3045_);
        v___x_3049_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6;
        v___x_3050_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3050_, 0, v___x_3048_);
        crate::leanh::lean_ctor_set(v___x_3050_, 1, v___x_3049_);
        v___x_3051_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3051_, 0, v___x_3046_);
        crate::leanh::lean_ctor_set(v___x_3051_, 1, v___x_3050_);
        v___x_3052_ = l_Std_Format_fill(v___x_3051_);
        return v___x_3052_;
    } else {
        let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_3039_);
        v___x_3053_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8;
        return v___x_3053_;
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7_spec__13(
    mut v_x_3054_: *mut crate::leanh::LeanObject,
    mut v_x_3055_: *mut crate::leanh::LeanObject,
    mut v_x_3056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3061_: u8 = 0;
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3056_) == 0 {
                    crate::leanh::lean_dec(v_x_3054_);
                    return v_x_3055_;
                } else {
                    v_head_3057_ = crate::leanh::lean_ctor_get(v_x_3056_, 0);
                    v_tail_3058_ = crate::leanh::lean_ctor_get(v_x_3056_, 1);
                    v_isSharedCheck_3068_ = (!crate::leanh::lean_is_exclusive(v_x_3056_)) as u8;
                    if v_isSharedCheck_3068_ == 0 {
                        v___x_3060_ = v_x_3056_;
                        v_isShared_3061_ = v_isSharedCheck_3068_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3058_);
                        crate::leanh::lean_inc(v_head_3057_);
                        crate::leanh::lean_dec(v_x_3056_);
                        v___x_3060_ = crate::leanh::lean_box(0);
                        v_isShared_3061_ = v_isSharedCheck_3068_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_3054_);
                if v_isShared_3061_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3060_, 5);
                    crate::leanh::lean_ctor_set(v___x_3060_, 1, v_x_3054_);
                    crate::leanh::lean_ctor_set(v___x_3060_, 0, v_x_3055_);
                    v___x_3063_ = v___x_3060_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3067_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_x_3055_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3067_, 1, v_x_3054_);
                    v___x_3063_ = v_reuseFailAlloc_3067_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3064_ =
                    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_3057_);
                crate::leanh::lean_dec(v_head_3057_);
                v___x_3065_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3065_, 0, v___x_3063_);
                crate::leanh::lean_ctor_set(v___x_3065_, 1, v___x_3064_);
                v_x_3055_ = v___x_3065_;
                v_x_3056_ = v_tail_3058_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7(
    mut v_x_3069_: *mut crate::leanh::LeanObject,
    mut v_x_3070_: *mut crate::leanh::LeanObject,
    mut v_x_3071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3076_: u8 = 0;
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3083_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3071_) == 0 {
                    crate::leanh::lean_dec(v_x_3069_);
                    return v_x_3070_;
                } else {
                    v_head_3072_ = crate::leanh::lean_ctor_get(v_x_3071_, 0);
                    v_tail_3073_ = crate::leanh::lean_ctor_get(v_x_3071_, 1);
                    v_isSharedCheck_3083_ = (!crate::leanh::lean_is_exclusive(v_x_3071_)) as u8;
                    if v_isSharedCheck_3083_ == 0 {
                        v___x_3075_ = v_x_3071_;
                        v_isShared_3076_ = v_isSharedCheck_3083_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3073_);
                        crate::leanh::lean_inc(v_head_3072_);
                        crate::leanh::lean_dec(v_x_3071_);
                        v___x_3075_ = crate::leanh::lean_box(0);
                        v_isShared_3076_ = v_isSharedCheck_3083_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_3069_);
                if v_isShared_3076_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3075_, 5);
                    crate::leanh::lean_ctor_set(v___x_3075_, 1, v_x_3069_);
                    crate::leanh::lean_ctor_set(v___x_3075_, 0, v_x_3070_);
                    v___x_3078_ = v___x_3075_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3082_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_x_3070_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3082_, 1, v_x_3069_);
                    v___x_3078_ = v_reuseFailAlloc_3082_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3079_ =
                    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_3072_);
                crate::leanh::lean_dec(v_head_3072_);
                v___x_3080_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3080_, 0, v___x_3078_);
                crate::leanh::lean_ctor_set(v___x_3080_, 1, v___x_3079_);
                v___x_3081_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7_spec__13(v_x_3069_, v___x_3080_, v_tail_3073_);
                return v___x_3081_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4(
    mut v_x_3084_: *mut crate::leanh::LeanObject,
    mut v_x_3085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3084_) == 0 {
        let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_3085_);
        v___x_3086_ = crate::leanh::lean_box(0);
        return v___x_3086_;
    } else {
        let mut v_tail_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_3087_ = crate::leanh::lean_ctor_get(v_x_3084_, 1);
        if crate::leanh::lean_obj_tag(v_tail_3087_) == 0 {
            let mut v_head_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_3085_);
            v_head_3088_ = crate::leanh::lean_ctor_get(v_x_3084_, 0);
            crate::leanh::lean_inc(v_head_3088_);
            crate::leanh::lean_dec_ref_known(v_x_3084_, 2);
            v___x_3089_ =
                l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_3088_);
            crate::leanh::lean_dec(v_head_3088_);
            return v___x_3089_;
        } else {
            let mut v_head_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_3087_);
            v_head_3090_ = crate::leanh::lean_ctor_get(v_x_3084_, 0);
            crate::leanh::lean_inc(v_head_3090_);
            crate::leanh::lean_dec_ref_known(v_x_3084_, 2);
            v___x_3091_ =
                l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_3090_);
            crate::leanh::lean_dec(v_head_3090_);
            v___x_3092_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7(v_x_3085_, v___x_3091_, v_tail_3087_);
            return v___x_3092_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2(
    mut v_xs_3093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: u8 = 0;
    v___x_3094_ = lean_array_get_size(v_xs_3093_);
    v___x_3095_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3096_ = lean_nat_dec_eq(v___x_3094_, v___x_3095_);
    if v___x_3096_ == 0 {
        let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3097_ = lean_array_to_list(v_xs_3093_);
        v___x_3098_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1;
        v___x_3099_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4(v___x_3097_, v___x_3098_);
        v___x_3100_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once), _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
        v___x_3101_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5;
        v___x_3102_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3102_, 0, v___x_3101_);
        crate::leanh::lean_ctor_set(v___x_3102_, 1, v___x_3099_);
        v___x_3103_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6;
        v___x_3104_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3104_, 0, v___x_3102_);
        crate::leanh::lean_ctor_set(v___x_3104_, 1, v___x_3103_);
        v___x_3105_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3105_, 0, v___x_3100_);
        crate::leanh::lean_ctor_set(v___x_3105_, 1, v___x_3104_);
        v___x_3106_ = l_Std_Format_fill(v___x_3105_);
        return v___x_3106_;
    } else {
        let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_3093_);
        v___x_3107_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8;
        return v___x_3107_;
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13_spec__19(
    mut v_x_3108_: *mut crate::leanh::LeanObject,
    mut v_x_3109_: *mut crate::leanh::LeanObject,
    mut v_x_3110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3115_: u8 = 0;
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3122_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3110_) == 0 {
                    crate::leanh::lean_dec(v_x_3108_);
                    return v_x_3109_;
                } else {
                    v_head_3111_ = crate::leanh::lean_ctor_get(v_x_3110_, 0);
                    v_tail_3112_ = crate::leanh::lean_ctor_get(v_x_3110_, 1);
                    v_isSharedCheck_3122_ = (!crate::leanh::lean_is_exclusive(v_x_3110_)) as u8;
                    if v_isSharedCheck_3122_ == 0 {
                        v___x_3114_ = v_x_3110_;
                        v_isShared_3115_ = v_isSharedCheck_3122_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3112_);
                        crate::leanh::lean_inc(v_head_3111_);
                        crate::leanh::lean_dec(v_x_3110_);
                        v___x_3114_ = crate::leanh::lean_box(0);
                        v_isShared_3115_ = v_isSharedCheck_3122_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_3108_);
                if v_isShared_3115_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3114_, 5);
                    crate::leanh::lean_ctor_set(v___x_3114_, 1, v_x_3108_);
                    crate::leanh::lean_ctor_set(v___x_3114_, 0, v_x_3109_);
                    v___x_3117_ = v___x_3114_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3121_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_x_3109_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3121_, 1, v_x_3108_);
                    v___x_3117_ = v_reuseFailAlloc_3121_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3118_ =
                    l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_3111_);
                v___x_3119_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3119_, 0, v___x_3117_);
                crate::leanh::lean_ctor_set(v___x_3119_, 1, v___x_3118_);
                v_x_3109_ = v___x_3119_;
                v_x_3110_ = v_tail_3112_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13(
    mut v_x_3123_: *mut crate::leanh::LeanObject,
    mut v_x_3124_: *mut crate::leanh::LeanObject,
    mut v_x_3125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3130_: u8 = 0;
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3137_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3125_) == 0 {
                    crate::leanh::lean_dec(v_x_3123_);
                    return v_x_3124_;
                } else {
                    v_head_3126_ = crate::leanh::lean_ctor_get(v_x_3125_, 0);
                    v_tail_3127_ = crate::leanh::lean_ctor_get(v_x_3125_, 1);
                    v_isSharedCheck_3137_ = (!crate::leanh::lean_is_exclusive(v_x_3125_)) as u8;
                    if v_isSharedCheck_3137_ == 0 {
                        v___x_3129_ = v_x_3125_;
                        v_isShared_3130_ = v_isSharedCheck_3137_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3127_);
                        crate::leanh::lean_inc(v_head_3126_);
                        crate::leanh::lean_dec(v_x_3125_);
                        v___x_3129_ = crate::leanh::lean_box(0);
                        v_isShared_3130_ = v_isSharedCheck_3137_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_3123_);
                if v_isShared_3130_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3129_, 5);
                    crate::leanh::lean_ctor_set(v___x_3129_, 1, v_x_3123_);
                    crate::leanh::lean_ctor_set(v___x_3129_, 0, v_x_3124_);
                    v___x_3132_ = v___x_3129_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3136_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_x_3124_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3136_, 1, v_x_3123_);
                    v___x_3132_ = v_reuseFailAlloc_3136_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3133_ =
                    l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_3126_);
                v___x_3134_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3134_, 0, v___x_3132_);
                crate::leanh::lean_ctor_set(v___x_3134_, 1, v___x_3133_);
                v___x_3135_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13_spec__19(v_x_3123_, v___x_3134_, v_tail_3127_);
                return v___x_3135_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8(
    mut v_x_3138_: *mut crate::leanh::LeanObject,
    mut v_x_3139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3138_) == 0 {
        let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_3139_);
        v___x_3140_ = crate::leanh::lean_box(0);
        return v___x_3140_;
    } else {
        let mut v_tail_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_3141_ = crate::leanh::lean_ctor_get(v_x_3138_, 1);
        if crate::leanh::lean_obj_tag(v_tail_3141_) == 0 {
            let mut v_head_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_3139_);
            v_head_3142_ = crate::leanh::lean_ctor_get(v_x_3138_, 0);
            crate::leanh::lean_inc(v_head_3142_);
            crate::leanh::lean_dec_ref_known(v_x_3138_, 2);
            v___x_3143_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_3142_);
            return v___x_3143_;
        } else {
            let mut v_head_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_3141_);
            v_head_3144_ = crate::leanh::lean_ctor_get(v_x_3138_, 0);
            crate::leanh::lean_inc(v_head_3144_);
            crate::leanh::lean_dec_ref_known(v_x_3138_, 2);
            v___x_3145_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_3144_);
            v___x_3146_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13(v_x_3139_, v___x_3145_, v_tail_3141_);
            return v___x_3146_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4(
    mut v_xs_3147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: u8 = 0;
    v___x_3148_ = lean_array_get_size(v_xs_3147_);
    v___x_3149_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3150_ = lean_nat_dec_eq(v___x_3148_, v___x_3149_);
    if v___x_3150_ == 0 {
        let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3151_ = lean_array_to_list(v_xs_3147_);
        v___x_3152_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1;
        v___x_3153_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8(v___x_3151_, v___x_3152_);
        v___x_3154_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once), _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
        v___x_3155_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5;
        v___x_3156_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3156_, 0, v___x_3155_);
        crate::leanh::lean_ctor_set(v___x_3156_, 1, v___x_3153_);
        v___x_3157_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6;
        v___x_3158_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3158_, 0, v___x_3156_);
        crate::leanh::lean_ctor_set(v___x_3158_, 1, v___x_3157_);
        v___x_3159_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3159_, 0, v___x_3154_);
        crate::leanh::lean_ctor_set(v___x_3159_, 1, v___x_3158_);
        v___x_3160_ = l_Std_Format_fill(v___x_3159_);
        return v___x_3160_;
    } else {
        let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_3147_);
        v___x_3161_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8;
        return v___x_3161_;
    }
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3171_ = crate::leanh::lean_unsigned_to_nat(10);
    v___x_3172_ = lean_nat_to_int(v___x_3171_);
    return v___x_3172_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3176_ = crate::leanh::lean_unsigned_to_nat(19);
    v___x_3177_ = lean_nat_to_int(v___x_3176_);
    return v___x_3177_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3187_ = crate::leanh::lean_unsigned_to_nat(17);
    v___x_3188_ = lean_nat_to_int(v___x_3187_);
    return v___x_3188_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3192_ = crate::leanh::lean_unsigned_to_nat(15);
    v___x_3193_ = lean_nat_to_int(v___x_3192_);
    return v___x_3193_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(
    mut v_x_3200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_header_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitionTimes_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitionIndices_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localTimeTypes_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_abbreviations_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leapSeconds_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stdWallIndicators_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_utLocalIndicators_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_header_3201_ = crate::leanh::lean_ctor_get(v_x_3200_, 0);
    crate::leanh::lean_inc_ref(v_header_3201_);
    v_transitionTimes_3202_ = crate::leanh::lean_ctor_get(v_x_3200_, 1);
    crate::leanh::lean_inc_ref(v_transitionTimes_3202_);
    v_transitionIndices_3203_ = crate::leanh::lean_ctor_get(v_x_3200_, 2);
    crate::leanh::lean_inc_ref(v_transitionIndices_3203_);
    v_localTimeTypes_3204_ = crate::leanh::lean_ctor_get(v_x_3200_, 3);
    crate::leanh::lean_inc_ref(v_localTimeTypes_3204_);
    v_abbreviations_3205_ = crate::leanh::lean_ctor_get(v_x_3200_, 4);
    crate::leanh::lean_inc_ref(v_abbreviations_3205_);
    v_leapSeconds_3206_ = crate::leanh::lean_ctor_get(v_x_3200_, 5);
    crate::leanh::lean_inc_ref(v_leapSeconds_3206_);
    v_stdWallIndicators_3207_ = crate::leanh::lean_ctor_get(v_x_3200_, 6);
    crate::leanh::lean_inc_ref(v_stdWallIndicators_3207_);
    v_utLocalIndicators_3208_ = crate::leanh::lean_ctor_get(v_x_3200_, 7);
    crate::leanh::lean_inc_ref(v_utLocalIndicators_3208_);
    crate::leanh::lean_dec_ref(v_x_3200_);
    v___x_3209_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5;
    v___x_3210_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__3;
    v___x_3211_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4,
    );
    v___x_3212_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg(v_header_3201_);
    crate::leanh::lean_dec_ref(v_header_3201_);
    v___x_3213_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3213_, 0, v___x_3211_);
    crate::leanh::lean_ctor_set(v___x_3213_, 1, v___x_3212_);
    v___x_3214_ = 0;
    v___x_3215_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3215_, 0, v___x_3213_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3215_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3214_,
    );
    v___x_3216_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3216_, 0, v___x_3210_);
    crate::leanh::lean_ctor_set(v___x_3216_, 1, v___x_3215_);
    v___x_3217_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9;
    v___x_3218_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3218_, 0, v___x_3216_);
    crate::leanh::lean_ctor_set(v___x_3218_, 1, v___x_3217_);
    v___x_3219_ = crate::leanh::lean_box(1);
    v___x_3220_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3220_, 0, v___x_3218_);
    crate::leanh::lean_ctor_set(v___x_3220_, 1, v___x_3219_);
    v___x_3221_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__6;
    v___x_3222_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3222_, 0, v___x_3220_);
    crate::leanh::lean_ctor_set(v___x_3222_, 1, v___x_3221_);
    v___x_3223_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3223_, 0, v___x_3222_);
    crate::leanh::lean_ctor_set(v___x_3223_, 1, v___x_3209_);
    v___x_3224_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7,
    );
    v___x_3225_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0(
        v_transitionTimes_3202_,
    );
    v___x_3226_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3226_, 0, v___x_3224_);
    crate::leanh::lean_ctor_set(v___x_3226_, 1, v___x_3225_);
    v___x_3227_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3227_, 0, v___x_3226_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3227_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3214_,
    );
    v___x_3228_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3228_, 0, v___x_3223_);
    crate::leanh::lean_ctor_set(v___x_3228_, 1, v___x_3227_);
    v___x_3229_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3229_, 0, v___x_3228_);
    crate::leanh::lean_ctor_set(v___x_3229_, 1, v___x_3217_);
    v___x_3230_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3230_, 0, v___x_3229_);
    crate::leanh::lean_ctor_set(v___x_3230_, 1, v___x_3219_);
    v___x_3231_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__9;
    v___x_3232_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3232_, 0, v___x_3230_);
    crate::leanh::lean_ctor_set(v___x_3232_, 1, v___x_3231_);
    v___x_3233_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3233_, 0, v___x_3232_);
    crate::leanh::lean_ctor_set(v___x_3233_, 1, v___x_3209_);
    v___x_3234_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10,
    );
    v___x_3235_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1(
        v_transitionIndices_3203_,
    );
    v___x_3236_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3236_, 0, v___x_3234_);
    crate::leanh::lean_ctor_set(v___x_3236_, 1, v___x_3235_);
    v___x_3237_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3237_, 0, v___x_3236_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3237_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3214_,
    );
    v___x_3238_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3238_, 0, v___x_3233_);
    crate::leanh::lean_ctor_set(v___x_3238_, 1, v___x_3237_);
    v___x_3239_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3239_, 0, v___x_3238_);
    crate::leanh::lean_ctor_set(v___x_3239_, 1, v___x_3217_);
    v___x_3240_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3240_, 0, v___x_3239_);
    crate::leanh::lean_ctor_set(v___x_3240_, 1, v___x_3219_);
    v___x_3241_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__11;
    v___x_3242_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3242_, 0, v___x_3240_);
    crate::leanh::lean_ctor_set(v___x_3242_, 1, v___x_3241_);
    v___x_3243_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3243_, 0, v___x_3242_);
    crate::leanh::lean_ctor_set(v___x_3243_, 1, v___x_3209_);
    v___x_3244_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4,
    );
    v___x_3245_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2(
        v_localTimeTypes_3204_,
    );
    v___x_3246_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3246_, 0, v___x_3244_);
    crate::leanh::lean_ctor_set(v___x_3246_, 1, v___x_3245_);
    v___x_3247_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3247_, 0, v___x_3246_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3247_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3214_,
    );
    v___x_3248_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3248_, 0, v___x_3243_);
    crate::leanh::lean_ctor_set(v___x_3248_, 1, v___x_3247_);
    v___x_3249_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3249_, 0, v___x_3248_);
    crate::leanh::lean_ctor_set(v___x_3249_, 1, v___x_3217_);
    v___x_3250_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3250_, 0, v___x_3249_);
    crate::leanh::lean_ctor_set(v___x_3250_, 1, v___x_3219_);
    v___x_3251_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__13;
    v___x_3252_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3252_, 0, v___x_3250_);
    crate::leanh::lean_ctor_set(v___x_3252_, 1, v___x_3251_);
    v___x_3253_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3253_, 0, v___x_3252_);
    crate::leanh::lean_ctor_set(v___x_3253_, 1, v___x_3209_);
    v___x_3254_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14,
    );
    v___x_3255_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3(
        v_abbreviations_3205_,
    );
    v___x_3256_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3256_, 0, v___x_3254_);
    crate::leanh::lean_ctor_set(v___x_3256_, 1, v___x_3255_);
    v___x_3257_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3257_, 0, v___x_3256_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3257_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3214_,
    );
    v___x_3258_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3258_, 0, v___x_3253_);
    crate::leanh::lean_ctor_set(v___x_3258_, 1, v___x_3257_);
    v___x_3259_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3259_, 0, v___x_3258_);
    crate::leanh::lean_ctor_set(v___x_3259_, 1, v___x_3217_);
    v___x_3260_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3260_, 0, v___x_3259_);
    crate::leanh::lean_ctor_set(v___x_3260_, 1, v___x_3219_);
    v___x_3261_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__16;
    v___x_3262_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3262_, 0, v___x_3260_);
    crate::leanh::lean_ctor_set(v___x_3262_, 1, v___x_3261_);
    v___x_3263_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3263_, 0, v___x_3262_);
    crate::leanh::lean_ctor_set(v___x_3263_, 1, v___x_3209_);
    v___x_3264_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17,
    );
    v___x_3265_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4(
        v_leapSeconds_3206_,
    );
    v___x_3266_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3266_, 0, v___x_3264_);
    crate::leanh::lean_ctor_set(v___x_3266_, 1, v___x_3265_);
    v___x_3267_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3267_, 0, v___x_3266_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3267_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3214_,
    );
    v___x_3268_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3268_, 0, v___x_3263_);
    crate::leanh::lean_ctor_set(v___x_3268_, 1, v___x_3267_);
    v___x_3269_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3269_, 0, v___x_3268_);
    crate::leanh::lean_ctor_set(v___x_3269_, 1, v___x_3217_);
    v___x_3270_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3270_, 0, v___x_3269_);
    crate::leanh::lean_ctor_set(v___x_3270_, 1, v___x_3219_);
    v___x_3271_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__19;
    v___x_3272_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3272_, 0, v___x_3270_);
    crate::leanh::lean_ctor_set(v___x_3272_, 1, v___x_3271_);
    v___x_3273_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3273_, 0, v___x_3272_);
    crate::leanh::lean_ctor_set(v___x_3273_, 1, v___x_3209_);
    v___x_3274_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5(
        v_stdWallIndicators_3207_,
    );
    v___x_3275_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3275_, 0, v___x_3234_);
    crate::leanh::lean_ctor_set(v___x_3275_, 1, v___x_3274_);
    v___x_3276_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3276_, 0, v___x_3275_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3276_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3214_,
    );
    v___x_3277_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3277_, 0, v___x_3273_);
    crate::leanh::lean_ctor_set(v___x_3277_, 1, v___x_3276_);
    v___x_3278_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3278_, 0, v___x_3277_);
    crate::leanh::lean_ctor_set(v___x_3278_, 1, v___x_3217_);
    v___x_3279_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3279_, 0, v___x_3278_);
    crate::leanh::lean_ctor_set(v___x_3279_, 1, v___x_3219_);
    v___x_3280_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__21;
    v___x_3281_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3281_, 0, v___x_3279_);
    crate::leanh::lean_ctor_set(v___x_3281_, 1, v___x_3280_);
    v___x_3282_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3282_, 0, v___x_3281_);
    crate::leanh::lean_ctor_set(v___x_3282_, 1, v___x_3209_);
    v___x_3283_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5(
        v_utLocalIndicators_3208_,
    );
    v___x_3284_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3284_, 0, v___x_3234_);
    crate::leanh::lean_ctor_set(v___x_3284_, 1, v___x_3283_);
    v___x_3285_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3285_, 0, v___x_3284_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3285_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3214_,
    );
    v___x_3286_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3286_, 0, v___x_3282_);
    crate::leanh::lean_ctor_set(v___x_3286_, 1, v___x_3285_);
    v___x_3287_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25,
    );
    v___x_3288_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26;
    v___x_3289_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3289_, 0, v___x_3288_);
    crate::leanh::lean_ctor_set(v___x_3289_, 1, v___x_3286_);
    v___x_3290_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27;
    v___x_3291_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3291_, 0, v___x_3289_);
    crate::leanh::lean_ctor_set(v___x_3291_, 1, v___x_3290_);
    v___x_3292_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3292_, 0, v___x_3287_);
    crate::leanh::lean_ctor_set(v___x_3292_, 1, v___x_3291_);
    v___x_3293_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3293_, 0, v___x_3292_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3293_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3214_,
    );
    return v___x_3293_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprTZifV1_repr(
    mut v_x_3294_: *mut crate::leanh::LeanObject,
    mut v_prec_3295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3296_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(v_x_3294_);
    return v___x_3296_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___boxed(
    mut v_x_3297_: *mut crate::leanh::LeanObject,
    mut v_prec_3298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3299_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr(v_x_3297_, v_prec_3298_);
    crate::leanh::lean_dec(v_prec_3298_);
    return v_res_3299_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3304_ = l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__0;
    v___x_3305_ = l_Std_Time_TimeZone_TZif_instInhabitedHeader_default;
    v___x_3306_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3306_, 0, v___x_3305_);
    crate::leanh::lean_ctor_set(v___x_3306_, 1, v___x_3304_);
    crate::leanh::lean_ctor_set(v___x_3306_, 2, v___x_3304_);
    crate::leanh::lean_ctor_set(v___x_3306_, 3, v___x_3304_);
    crate::leanh::lean_ctor_set(v___x_3306_, 4, v___x_3304_);
    crate::leanh::lean_ctor_set(v___x_3306_, 5, v___x_3304_);
    crate::leanh::lean_ctor_set(v___x_3306_, 6, v___x_3304_);
    crate::leanh::lean_ctor_set(v___x_3306_, 7, v___x_3304_);
    return v___x_3306_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3307_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1,
    );
    return v___x_3307_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3308_ = l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default;
    return v___x_3308_;
}
pub unsafe fn l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0(
    mut v_x_3315_: *mut crate::leanh::LeanObject,
    mut v_x_3316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3321_: u8 = 0;
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3329_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3315_) == 0 {
                    v___x_3317_ = l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__1;
                    return v___x_3317_;
                } else {
                    v_val_3318_ = crate::leanh::lean_ctor_get(v_x_3315_, 0);
                    v_isSharedCheck_3329_ = (!crate::leanh::lean_is_exclusive(v_x_3315_)) as u8;
                    if v_isSharedCheck_3329_ == 0 {
                        v___x_3320_ = v_x_3315_;
                        v_isShared_3321_ = v_isSharedCheck_3329_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3318_);
                        crate::leanh::lean_dec(v_x_3315_);
                        v___x_3320_ = crate::leanh::lean_box(0);
                        v_isShared_3321_ = v_isSharedCheck_3329_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3322_ = l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__3;
                v___x_3323_ = l_String_quote(v_val_3318_);
                if v_isShared_3321_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3320_, 3);
                    crate::leanh::lean_ctor_set(v___x_3320_, 0, v___x_3323_);
                    v___x_3325_ = v___x_3320_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3328_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3328_, 0, v___x_3323_);
                    v___x_3325_ = v_reuseFailAlloc_3328_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3326_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3326_, 0, v___x_3322_);
                crate::leanh::lean_ctor_set(v___x_3326_, 1, v___x_3325_);
                v___x_3327_ = l_Repr_addAppParen(v___x_3326_, v_x_3316_);
                return v___x_3327_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___boxed(
    mut v_x_3330_: *mut crate::leanh::LeanObject,
    mut v_x_3331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3332_ = l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0(
        v_x_3330_, v_x_3331_,
    );
    crate::leanh::lean_dec(v_x_3331_);
    return v_res_3332_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg(
    mut v_x_3345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toTZifV1_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_footer_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3350_: u8 = 0;
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: u8 = 0;
    let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toTZifV1_3346_ = crate::leanh::lean_ctor_get(v_x_3345_, 0);
                v_footer_3347_ = crate::leanh::lean_ctor_get(v_x_3345_, 1);
                v_isSharedCheck_3381_ = (!crate::leanh::lean_is_exclusive(v_x_3345_)) as u8;
                if v_isSharedCheck_3381_ == 0 {
                    v___x_3349_ = v_x_3345_;
                    v_isShared_3350_ = v_isSharedCheck_3381_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_footer_3347_);
                    crate::leanh::lean_inc(v_toTZifV1_3346_);
                    crate::leanh::lean_dec(v_x_3345_);
                    v___x_3349_ = crate::leanh::lean_box(0);
                    v_isShared_3350_ = v_isSharedCheck_3381_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3351_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5;
                v___x_3352_ = l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__3;
                v___x_3353_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14_once
                    ),
                    _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14,
                );
                v___x_3354_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3355_ =
                    l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(v_toTZifV1_3346_);
                if v_isShared_3350_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3349_, 4);
                    crate::leanh::lean_ctor_set(v___x_3349_, 1, v___x_3355_);
                    crate::leanh::lean_ctor_set(v___x_3349_, 0, v___x_3353_);
                    v___x_3357_ = v___x_3349_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3380_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3353_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3380_, 1, v___x_3355_);
                    v___x_3357_ = v_reuseFailAlloc_3380_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3358_ = 0;
                v___x_3359_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3359_, 0, v___x_3357_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3359_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3358_,
                );
                v___x_3360_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3360_, 0, v___x_3352_);
                crate::leanh::lean_ctor_set(v___x_3360_, 1, v___x_3359_);
                v___x_3361_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9;
                v___x_3362_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3362_, 0, v___x_3360_);
                crate::leanh::lean_ctor_set(v___x_3362_, 1, v___x_3361_);
                v___x_3363_ = crate::leanh::lean_box(1);
                v___x_3364_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3364_, 0, v___x_3362_);
                crate::leanh::lean_ctor_set(v___x_3364_, 1, v___x_3363_);
                v___x_3365_ = l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__5;
                v___x_3366_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3366_, 0, v___x_3364_);
                crate::leanh::lean_ctor_set(v___x_3366_, 1, v___x_3365_);
                v___x_3367_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3367_, 0, v___x_3366_);
                crate::leanh::lean_ctor_set(v___x_3367_, 1, v___x_3351_);
                v___x_3368_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4_once
                    ),
                    _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4,
                );
                v___x_3369_ =
                    l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0(
                        v_footer_3347_,
                        v___x_3354_,
                    );
                v___x_3370_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3370_, 0, v___x_3368_);
                crate::leanh::lean_ctor_set(v___x_3370_, 1, v___x_3369_);
                v___x_3371_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3371_, 0, v___x_3370_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3371_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3358_,
                );
                v___x_3372_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3372_, 0, v___x_3367_);
                crate::leanh::lean_ctor_set(v___x_3372_, 1, v___x_3371_);
                v___x_3373_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25,
                );
                v___x_3374_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26;
                v___x_3375_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3375_, 0, v___x_3374_);
                crate::leanh::lean_ctor_set(v___x_3375_, 1, v___x_3372_);
                v___x_3376_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27;
                v___x_3377_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3377_, 0, v___x_3375_);
                crate::leanh::lean_ctor_set(v___x_3377_, 1, v___x_3376_);
                v___x_3378_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3378_, 0, v___x_3373_);
                crate::leanh::lean_ctor_set(v___x_3378_, 1, v___x_3377_);
                v___x_3379_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3379_, 0, v___x_3378_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3379_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3358_,
                );
                return v___x_3379_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprTZifV2_repr(
    mut v_x_3382_: *mut crate::leanh::LeanObject,
    mut v_prec_3383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3384_ = l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg(v_x_3382_);
    return v___x_3384_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___boxed(
    mut v_x_3385_: *mut crate::leanh::LeanObject,
    mut v_prec_3386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3387_ = l_Std_Time_TimeZone_TZif_instReprTZifV2_repr(v_x_3385_, v_prec_3386_);
    crate::leanh::lean_dec(v_prec_3386_);
    return v_res_3387_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3390_ = crate::leanh::lean_box(0);
    v___x_3391_ = l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default;
    v___x_3392_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3392_, 0, v___x_3391_);
    crate::leanh::lean_ctor_set(v___x_3392_, 1, v___x_3390_);
    return v___x_3392_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3393_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0,
    );
    return v___x_3393_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3394_ = l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default;
    return v___x_3394_;
}
pub unsafe fn l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0(
    mut v_x_3395_: *mut crate::leanh::LeanObject,
    mut v_x_3396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3395_) == 0 {
        let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3397_ =
            l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__1;
        return v___x_3397_;
    } else {
        let mut v_val_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3398_ = crate::leanh::lean_ctor_get(v_x_3395_, 0);
        crate::leanh::lean_inc(v_val_3398_);
        crate::leanh::lean_dec_ref_known(v_x_3395_, 1);
        v___x_3399_ =
            l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__3;
        v___x_3400_ = l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg(v_val_3398_);
        v___x_3401_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3401_, 0, v___x_3399_);
        crate::leanh::lean_ctor_set(v___x_3401_, 1, v___x_3400_);
        v___x_3402_ = l_Repr_addAppParen(v___x_3401_, v_x_3396_);
        return v___x_3402_;
    }
}
pub unsafe fn l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0___boxed(
    mut v_x_3403_: *mut crate::leanh::LeanObject,
    mut v_x_3404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3405_ = l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0(
        v_x_3403_, v_x_3404_,
    );
    crate::leanh::lean_dec(v_x_3404_);
    return v_res_3405_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3415_ = crate::leanh::lean_unsigned_to_nat(6);
    v___x_3416_ = lean_nat_to_int(v___x_3415_);
    return v___x_3416_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg(
    mut v_x_3420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v1_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v2_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3425_: u8 = 0;
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: u8 = 0;
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_v1_3421_ = crate::leanh::lean_ctor_get(v_x_3420_, 0);
                v_v2_3422_ = crate::leanh::lean_ctor_get(v_x_3420_, 1);
                v_isSharedCheck_3455_ = (!crate::leanh::lean_is_exclusive(v_x_3420_)) as u8;
                if v_isSharedCheck_3455_ == 0 {
                    v___x_3424_ = v_x_3420_;
                    v_isShared_3425_ = v_isSharedCheck_3455_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v2_3422_);
                    crate::leanh::lean_inc(v_v1_3421_);
                    crate::leanh::lean_dec(v_x_3420_);
                    v___x_3424_ = crate::leanh::lean_box(0);
                    v_isShared_3425_ = v_isSharedCheck_3455_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3426_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5;
                v___x_3427_ = l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__3;
                v___x_3428_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4_once
                    ),
                    _init_l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4,
                );
                v___x_3429_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3430_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(v_v1_3421_);
                if v_isShared_3425_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3424_, 4);
                    crate::leanh::lean_ctor_set(v___x_3424_, 1, v___x_3430_);
                    crate::leanh::lean_ctor_set(v___x_3424_, 0, v___x_3428_);
                    v___x_3432_ = v___x_3424_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3454_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3428_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3454_, 1, v___x_3430_);
                    v___x_3432_ = v_reuseFailAlloc_3454_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3433_ = 0;
                v___x_3434_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3434_, 0, v___x_3432_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3434_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3433_,
                );
                v___x_3435_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3435_, 0, v___x_3427_);
                crate::leanh::lean_ctor_set(v___x_3435_, 1, v___x_3434_);
                v___x_3436_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9;
                v___x_3437_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3437_, 0, v___x_3435_);
                crate::leanh::lean_ctor_set(v___x_3437_, 1, v___x_3436_);
                v___x_3438_ = crate::leanh::lean_box(1);
                v___x_3439_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3439_, 0, v___x_3437_);
                crate::leanh::lean_ctor_set(v___x_3439_, 1, v___x_3438_);
                v___x_3440_ = l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__6;
                v___x_3441_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3441_, 0, v___x_3439_);
                crate::leanh::lean_ctor_set(v___x_3441_, 1, v___x_3440_);
                v___x_3442_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3442_, 0, v___x_3441_);
                crate::leanh::lean_ctor_set(v___x_3442_, 1, v___x_3426_);
                v___x_3443_ =
                    l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0(
                        v_v2_3422_,
                        v___x_3429_,
                    );
                v___x_3444_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3444_, 0, v___x_3428_);
                crate::leanh::lean_ctor_set(v___x_3444_, 1, v___x_3443_);
                v___x_3445_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3445_, 0, v___x_3444_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3445_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3433_,
                );
                v___x_3446_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3446_, 0, v___x_3442_);
                crate::leanh::lean_ctor_set(v___x_3446_, 1, v___x_3445_);
                v___x_3447_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25,
                );
                v___x_3448_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26;
                v___x_3449_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3449_, 0, v___x_3448_);
                crate::leanh::lean_ctor_set(v___x_3449_, 1, v___x_3446_);
                v___x_3450_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27;
                v___x_3451_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3451_, 0, v___x_3449_);
                crate::leanh::lean_ctor_set(v___x_3451_, 1, v___x_3450_);
                v___x_3452_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3452_, 0, v___x_3447_);
                crate::leanh::lean_ctor_set(v___x_3452_, 1, v___x_3451_);
                v___x_3453_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3453_, 0, v___x_3452_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3453_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3433_,
                );
                return v___x_3453_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprTZif_repr(
    mut v_x_3456_: *mut crate::leanh::LeanObject,
    mut v_prec_3457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3458_ = l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg(v_x_3456_);
    return v___x_3458_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprTZif_repr___boxed(
    mut v_x_3459_: *mut crate::leanh::LeanObject,
    mut v_prec_3460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3461_ = l_Std_Time_TimeZone_TZif_instReprTZif_repr(v_x_3459_, v_prec_3460_);
    crate::leanh::lean_dec(v_prec_3460_);
    return v_res_3461_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3464_ = crate::leanh::lean_box(0);
    v___x_3465_ = l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default;
    v___x_3466_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3466_, 0, v___x_3465_);
    crate::leanh::lean_ctor_set(v___x_3466_, 1, v___x_3464_);
    return v___x_3466_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedTZif_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3467_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0,
    );
    return v___x_3467_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedTZif() -> *mut crate::leanh::LeanObject {
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3468_ = l_Std_Time_TimeZone_TZif_instInhabitedTZif_default;
    return v___x_3468_;
}
pub unsafe fn _init_l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3469_: u32 = 0;
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3469_ = l_instInhabitedUInt32;
    v___x_3470_ = crate::leanh::lean_box_uint32(v___x_3469_);
    return v___x_3470_;
}
pub unsafe fn l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0(
    mut v_msg_3471_: *mut crate::leanh::LeanObject,
) -> u32 {
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: u32 = 0;
    v___x_3472_ = l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1;
    v___x_3473_ = lean_panic_fn_borrowed(v___x_3472_, v_msg_3471_);
    v___x_3474_ = crate::leanh::lean_unbox_uint32(v___x_3473_);
    crate::leanh::lean_dec(v___x_3473_);
    return v___x_3474_;
}
pub unsafe fn l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed(
    mut v_msg_3475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3476_: u32 = 0;
    let mut v_r_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3476_ = l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0(v_msg_3475_);
    v_r_3477_ = crate::leanh::lean_box_uint32(v_res_3476_);
    return v_r_3477_;
}
pub unsafe fn _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3481_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__2;
    v___x_3482_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_3483_ = crate::leanh::lean_unsigned_to_nat(181);
    v___x_3484_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__1;
    v___x_3485_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__0;
    v___x_3486_ = l_mkPanicMessageWithDecl(
        v___x_3485_,
        v___x_3484_,
        v___x_3483_,
        v___x_3482_,
        v___x_3481_,
    );
    return v___x_3486_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(
    mut v_bs_3487_: *mut crate::leanh::LeanObject,
) -> u32 {
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: u8 = 0;
    v___x_3488_ = lean_byte_array_size(v_bs_3487_);
    v___x_3489_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_3490_ = lean_nat_dec_eq(v___x_3488_, v___x_3489_);
    if v___x_3490_ == 0 {
        let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3492_: u32 = 0;
        v___x_3491_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3), core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3_once), _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3);
        v___x_3492_ = l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0(v___x_3491_);
        return v___x_3492_;
    } else {
        let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3494_: u8 = 0;
        let mut v___x_3495_: u32 = 0;
        let mut v___x_3496_: u32 = 0;
        let mut v___x_3497_: u32 = 0;
        let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3499_: u8 = 0;
        let mut v___x_3500_: u32 = 0;
        let mut v___x_3501_: u32 = 0;
        let mut v___x_3502_: u32 = 0;
        let mut v___x_3503_: u32 = 0;
        let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3505_: u8 = 0;
        let mut v___x_3506_: u32 = 0;
        let mut v___x_3507_: u32 = 0;
        let mut v___x_3508_: u32 = 0;
        let mut v___x_3509_: u32 = 0;
        let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3511_: u8 = 0;
        let mut v___x_3512_: u32 = 0;
        let mut v___x_3513_: u32 = 0;
        v___x_3493_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_3494_ = lean_byte_array_get(v_bs_3487_, v___x_3493_);
        v___x_3495_ = lean_uint8_to_uint32(v___x_3494_);
        v___x_3496_ = 24;
        v___x_3497_ = lean_uint32_shift_left(v___x_3495_, v___x_3496_);
        v___x_3498_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_3499_ = lean_byte_array_get(v_bs_3487_, v___x_3498_);
        v___x_3500_ = lean_uint8_to_uint32(v___x_3499_);
        v___x_3501_ = 16;
        v___x_3502_ = lean_uint32_shift_left(v___x_3500_, v___x_3501_);
        v___x_3503_ = lean_uint32_lor(v___x_3497_, v___x_3502_);
        v___x_3504_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_3505_ = lean_byte_array_get(v_bs_3487_, v___x_3504_);
        v___x_3506_ = lean_uint8_to_uint32(v___x_3505_);
        v___x_3507_ = 8;
        v___x_3508_ = lean_uint32_shift_left(v___x_3506_, v___x_3507_);
        v___x_3509_ = lean_uint32_lor(v___x_3503_, v___x_3508_);
        v___x_3510_ = crate::leanh::lean_unsigned_to_nat(3);
        v___x_3511_ = lean_byte_array_get(v_bs_3487_, v___x_3510_);
        v___x_3512_ = lean_uint8_to_uint32(v___x_3511_);
        v___x_3513_ = lean_uint32_lor(v___x_3509_, v___x_3512_);
        return v___x_3513_;
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___boxed(
    mut v_bs_3514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3515_: u32 = 0;
    let mut v_r_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3515_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(v_bs_3514_);
    crate::leanh::lean_dec_ref(v_bs_3514_);
    v_r_3516_ = crate::leanh::lean_box_uint32(v_res_3515_);
    return v_r_3516_;
}
pub unsafe fn _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3517_ = crate::leanh::lean_unsigned_to_nat(31);
    v___x_3518_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3519_ = lean_nat_shiftl(v___x_3518_, v___x_3517_);
    return v___x_3519_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32(
    mut v_bs_3520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3521_: u32 = 0;
    let mut v_n_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: u8 = 0;
    v___x_3521_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(v_bs_3520_);
    v_n_3522_ = lean_uint32_to_nat(v___x_3521_);
    v___x_3523_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___closed__0), core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___closed__0_once), _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___closed__0);
    v___x_3524_ = lean_nat_dec_lt(v_n_3522_, v___x_3523_);
    if v___x_3524_ == 0 {
        let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3525_ = crate::leanh::lean_cstr_to_nat(b"4294967296\0".as_ptr().cast());
        v___x_3526_ = lean_nat_sub(v___x_3525_, v_n_3522_);
        crate::leanh::lean_dec(v_n_3522_);
        v___x_3527_ = l_Int_negOfNat(v___x_3526_);
        crate::leanh::lean_dec(v___x_3526_);
        return v___x_3527_;
    } else {
        let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3528_ = lean_nat_to_int(v_n_3522_);
        return v___x_3528_;
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___boxed(
    mut v_bs_3529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3530_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32(v_bs_3529_);
    crate::leanh::lean_dec_ref(v_bs_3529_);
    return v_res_3530_;
}
pub unsafe fn _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3531_ = crate::leanh::lean_unsigned_to_nat(63);
    v___x_3532_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3533_ = lean_nat_shiftl(v___x_3532_, v___x_3531_);
    return v___x_3533_;
}
pub unsafe fn _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3534_ = crate::leanh::lean_cstr_to_nat(b"18446744073709551616\0".as_ptr().cast());
    return v___x_3534_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64(
    mut v_bs_3535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3536_: u64 = 0;
    let mut v_n_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: u8 = 0;
    v___x_3536_ = l_ByteArray_toUInt64BE_x21(v_bs_3535_);
    v_n_3537_ = lean_uint64_to_nat(v___x_3536_);
    v___x_3538_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0), core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0_once), _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0);
    v___x_3539_ = lean_nat_dec_lt(v_n_3537_, v___x_3538_);
    if v___x_3539_ == 0 {
        let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3540_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1), core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1_once), _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1);
        v___x_3541_ = lean_nat_sub(v___x_3540_, v_n_3537_);
        crate::leanh::lean_dec(v_n_3537_);
        v___x_3542_ = l_Int_negOfNat(v___x_3541_);
        crate::leanh::lean_dec(v___x_3541_);
        return v___x_3542_;
    } else {
        let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3543_ = lean_nat_to_int(v_n_3537_);
        return v___x_3543_;
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___boxed(
    mut v_bs_3544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3545_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64(v_bs_3544_);
    crate::leanh::lean_dec_ref(v_bs_3544_);
    return v_res_3545_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(
    mut v_upperBound_3546_: *mut crate::leanh::LeanObject,
    mut v_p_3547_: *mut crate::leanh::LeanObject,
    mut v_a_3548_: *mut crate::leanh::LeanObject,
    mut v_b_3549_: *mut crate::leanh::LeanObject,
    mut v___y_3550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3551_: u8 = 0;
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3564_: u8 = 0;
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3568_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3551_ = lean_nat_dec_lt(v_a_3548_, v_upperBound_3546_);
                if v___x_3551_ == 0 {
                    crate::leanh::lean_dec(v_a_3548_);
                    crate::leanh::lean_dec_ref(v_p_3547_);
                    v___x_3552_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3552_, 0, v___y_3550_);
                    crate::leanh::lean_ctor_set(v___x_3552_, 1, v_b_3549_);
                    return v___x_3552_;
                } else {
                    crate::leanh::lean_inc_ref(v_p_3547_);
                    v___x_3553_ = crate::leanh::lean_apply_1(v_p_3547_, v___y_3550_);
                    if crate::leanh::lean_obj_tag(v___x_3553_) == 0 {
                        v_pos_3554_ = crate::leanh::lean_ctor_get(v___x_3553_, 0);
                        crate::leanh::lean_inc(v_pos_3554_);
                        v_res_3555_ = crate::leanh::lean_ctor_get(v___x_3553_, 1);
                        crate::leanh::lean_inc(v_res_3555_);
                        crate::leanh::lean_dec_ref_known(v___x_3553_, 2);
                        v___x_3556_ = lean_array_push(v_b_3549_, v_res_3555_);
                        v___x_3557_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3558_ = lean_nat_add(v_a_3548_, v___x_3557_);
                        crate::leanh::lean_dec(v_a_3548_);
                        v_a_3548_ = v___x_3558_;
                        v_b_3549_ = v___x_3556_;
                        v___y_3550_ = v_pos_3554_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_3549_);
                        crate::leanh::lean_dec(v_a_3548_);
                        crate::leanh::lean_dec_ref(v_p_3547_);
                        v_pos_3560_ = crate::leanh::lean_ctor_get(v___x_3553_, 0);
                        v_err_3561_ = crate::leanh::lean_ctor_get(v___x_3553_, 1);
                        v_isSharedCheck_3568_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3553_)) as u8;
                        if v_isSharedCheck_3568_ == 0 {
                            v___x_3563_ = v___x_3553_;
                            v_isShared_3564_ = v_isSharedCheck_3568_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_err_3561_);
                            crate::leanh::lean_inc(v_pos_3560_);
                            crate::leanh::lean_dec(v___x_3553_);
                            v___x_3563_ = crate::leanh::lean_box(0);
                            v_isShared_3564_ = v_isSharedCheck_3568_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3564_ == 0 {
                    v___x_3566_ = v___x_3563_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3567_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_pos_3560_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3567_, 1, v_err_3561_);
                    v___x_3566_ = v_reuseFailAlloc_3567_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3566_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg___boxed(
    mut v_upperBound_3569_: *mut crate::leanh::LeanObject,
    mut v_p_3570_: *mut crate::leanh::LeanObject,
    mut v_a_3571_: *mut crate::leanh::LeanObject,
    mut v_b_3572_: *mut crate::leanh::LeanObject,
    mut v___y_3573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3574_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(v_upperBound_3569_, v_p_3570_, v_a_3571_, v_b_3572_, v___y_3573_);
    crate::leanh::lean_dec(v_upperBound_3569_);
    return v_res_3574_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(
    mut v_n_3577_: *mut crate::leanh::LeanObject,
    mut v_p_3578_: *mut crate::leanh::LeanObject,
    mut v_a_3579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3580_ = crate::leanh::lean_unsigned_to_nat(0);
    v_result_3581_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg___closed__0;
    v___x_3582_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(v_n_3577_, v_p_3578_, v___x_3580_, v_result_3581_, v_a_3579_);
    return v___x_3582_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg___boxed(
    mut v_n_3583_: *mut crate::leanh::LeanObject,
    mut v_p_3584_: *mut crate::leanh::LeanObject,
    mut v_a_3585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3586_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(
        v_n_3583_, v_p_3584_, v_a_3585_,
    );
    crate::leanh::lean_dec(v_n_3583_);
    return v_res_3586_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN(
    mut v_00_u03b1_3587_: *mut crate::leanh::LeanObject,
    mut v_n_3588_: *mut crate::leanh::LeanObject,
    mut v_p_3589_: *mut crate::leanh::LeanObject,
    mut v_a_3590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3591_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(
        v_n_3588_, v_p_3589_, v_a_3590_,
    );
    return v___x_3591_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___boxed(
    mut v_00_u03b1_3592_: *mut crate::leanh::LeanObject,
    mut v_n_3593_: *mut crate::leanh::LeanObject,
    mut v_p_3594_: *mut crate::leanh::LeanObject,
    mut v_a_3595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3596_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN(
        v_00_u03b1_3592_,
        v_n_3593_,
        v_p_3594_,
        v_a_3595_,
    );
    crate::leanh::lean_dec(v_n_3593_);
    return v_res_3596_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0(
    mut v_00_u03b1_3597_: *mut crate::leanh::LeanObject,
    mut v_upperBound_3598_: *mut crate::leanh::LeanObject,
    mut v_p_3599_: *mut crate::leanh::LeanObject,
    mut v_inst_3600_: *mut crate::leanh::LeanObject,
    mut v_R_3601_: *mut crate::leanh::LeanObject,
    mut v_a_3602_: *mut crate::leanh::LeanObject,
    mut v_b_3603_: *mut crate::leanh::LeanObject,
    mut v_c_3604_: *mut crate::leanh::LeanObject,
    mut v___y_3605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3606_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(v_upperBound_3598_, v_p_3599_, v_a_3602_, v_b_3603_, v___y_3605_);
    return v___x_3606_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___boxed(
    mut v_00_u03b1_3607_: *mut crate::leanh::LeanObject,
    mut v_upperBound_3608_: *mut crate::leanh::LeanObject,
    mut v_p_3609_: *mut crate::leanh::LeanObject,
    mut v_inst_3610_: *mut crate::leanh::LeanObject,
    mut v_R_3611_: *mut crate::leanh::LeanObject,
    mut v_a_3612_: *mut crate::leanh::LeanObject,
    mut v_b_3613_: *mut crate::leanh::LeanObject,
    mut v_c_3614_: *mut crate::leanh::LeanObject,
    mut v___y_3615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3616_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0(v_00_u03b1_3607_, v_upperBound_3608_, v_p_3609_, v_inst_3610_, v_R_3611_, v_a_3612_, v_b_3613_, v_c_3614_, v___y_3615_);
    crate::leanh::lean_dec(v_upperBound_3608_);
    return v_res_3616_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu64(
    mut v_a_3617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3624_: u8 = 0;
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: u64 = 0;
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3631_: u8 = 0;
    let mut v_pos_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3636_: u8 = 0;
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3640_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3618_ = crate::leanh::lean_unsigned_to_nat(8);
                v___x_3619_ = l_Std_Internal_Parsec_ByteArray_take(v___x_3618_, v_a_3617_);
                if crate::leanh::lean_obj_tag(v___x_3619_) == 0 {
                    v_pos_3620_ = crate::leanh::lean_ctor_get(v___x_3619_, 0);
                    v_res_3621_ = crate::leanh::lean_ctor_get(v___x_3619_, 1);
                    v_isSharedCheck_3631_ = (!crate::leanh::lean_is_exclusive(v___x_3619_)) as u8;
                    if v_isSharedCheck_3631_ == 0 {
                        v___x_3623_ = v___x_3619_;
                        v_isShared_3624_ = v_isSharedCheck_3631_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_res_3621_);
                        crate::leanh::lean_inc(v_pos_3620_);
                        crate::leanh::lean_dec(v___x_3619_);
                        v___x_3623_ = crate::leanh::lean_box(0);
                        v_isShared_3624_ = v_isSharedCheck_3631_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_3632_ = crate::leanh::lean_ctor_get(v___x_3619_, 0);
                    v_err_3633_ = crate::leanh::lean_ctor_get(v___x_3619_, 1);
                    v_isSharedCheck_3640_ = (!crate::leanh::lean_is_exclusive(v___x_3619_)) as u8;
                    if v_isSharedCheck_3640_ == 0 {
                        v___x_3635_ = v___x_3619_;
                        v_isShared_3636_ = v_isSharedCheck_3640_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_3633_);
                        crate::leanh::lean_inc(v_pos_3632_);
                        crate::leanh::lean_dec(v___x_3619_);
                        v___x_3635_ = crate::leanh::lean_box(0);
                        v_isShared_3636_ = v_isSharedCheck_3640_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3625_ = l_ByteSlice_toByteArray(v_res_3621_);
                v___x_3626_ = l_ByteArray_toUInt64LE_x21(v___x_3625_);
                crate::leanh::lean_dec_ref(v___x_3625_);
                v___x_3627_ = crate::leanh::lean_box_uint64(v___x_3626_);
                if v_isShared_3624_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3623_, 1, v___x_3627_);
                    v___x_3629_ = v___x_3623_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3630_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_pos_3620_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 1, v___x_3627_);
                    v___x_3629_ = v_reuseFailAlloc_3630_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3629_;
            }
            3 => {
                if v_isShared_3636_ == 0 {
                    v___x_3638_ = v___x_3635_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3639_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_pos_3632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3639_, 1, v_err_3633_);
                    v___x_3638_ = v_reuseFailAlloc_3639_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3638_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi64(
    mut v_a_3641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3648_: u8 = 0;
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3654_: u8 = 0;
    let mut v_pos_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3659_: u8 = 0;
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3663_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3642_ = crate::leanh::lean_unsigned_to_nat(8);
                v___x_3643_ = l_Std_Internal_Parsec_ByteArray_take(v___x_3642_, v_a_3641_);
                if crate::leanh::lean_obj_tag(v___x_3643_) == 0 {
                    v_pos_3644_ = crate::leanh::lean_ctor_get(v___x_3643_, 0);
                    v_res_3645_ = crate::leanh::lean_ctor_get(v___x_3643_, 1);
                    v_isSharedCheck_3654_ = (!crate::leanh::lean_is_exclusive(v___x_3643_)) as u8;
                    if v_isSharedCheck_3654_ == 0 {
                        v___x_3647_ = v___x_3643_;
                        v_isShared_3648_ = v_isSharedCheck_3654_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_res_3645_);
                        crate::leanh::lean_inc(v_pos_3644_);
                        crate::leanh::lean_dec(v___x_3643_);
                        v___x_3647_ = crate::leanh::lean_box(0);
                        v_isShared_3648_ = v_isSharedCheck_3654_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_3655_ = crate::leanh::lean_ctor_get(v___x_3643_, 0);
                    v_err_3656_ = crate::leanh::lean_ctor_get(v___x_3643_, 1);
                    v_isSharedCheck_3663_ = (!crate::leanh::lean_is_exclusive(v___x_3643_)) as u8;
                    if v_isSharedCheck_3663_ == 0 {
                        v___x_3658_ = v___x_3643_;
                        v_isShared_3659_ = v_isSharedCheck_3663_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_3656_);
                        crate::leanh::lean_inc(v_pos_3655_);
                        crate::leanh::lean_dec(v___x_3643_);
                        v___x_3658_ = crate::leanh::lean_box(0);
                        v_isShared_3659_ = v_isSharedCheck_3663_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3649_ = l_ByteSlice_toByteArray(v_res_3645_);
                v___x_3650_ =
                    l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64(
                        v___x_3649_,
                    );
                crate::leanh::lean_dec_ref(v___x_3649_);
                if v_isShared_3648_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3647_, 1, v___x_3650_);
                    v___x_3652_ = v___x_3647_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3653_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_pos_3644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3653_, 1, v___x_3650_);
                    v___x_3652_ = v_reuseFailAlloc_3653_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3652_;
            }
            3 => {
                if v_isShared_3659_ == 0 {
                    v___x_3661_ = v___x_3658_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3662_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_pos_3655_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_err_3656_);
                    v___x_3661_ = v_reuseFailAlloc_3662_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3661_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(
    mut v_a_3664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3671_: u8 = 0;
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: u32 = 0;
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3678_: u8 = 0;
    let mut v_pos_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3683_: u8 = 0;
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3687_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3665_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3666_ = l_Std_Internal_Parsec_ByteArray_take(v___x_3665_, v_a_3664_);
                if crate::leanh::lean_obj_tag(v___x_3666_) == 0 {
                    v_pos_3667_ = crate::leanh::lean_ctor_get(v___x_3666_, 0);
                    v_res_3668_ = crate::leanh::lean_ctor_get(v___x_3666_, 1);
                    v_isSharedCheck_3678_ = (!crate::leanh::lean_is_exclusive(v___x_3666_)) as u8;
                    if v_isSharedCheck_3678_ == 0 {
                        v___x_3670_ = v___x_3666_;
                        v_isShared_3671_ = v_isSharedCheck_3678_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_res_3668_);
                        crate::leanh::lean_inc(v_pos_3667_);
                        crate::leanh::lean_dec(v___x_3666_);
                        v___x_3670_ = crate::leanh::lean_box(0);
                        v_isShared_3671_ = v_isSharedCheck_3678_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_3679_ = crate::leanh::lean_ctor_get(v___x_3666_, 0);
                    v_err_3680_ = crate::leanh::lean_ctor_get(v___x_3666_, 1);
                    v_isSharedCheck_3687_ = (!crate::leanh::lean_is_exclusive(v___x_3666_)) as u8;
                    if v_isSharedCheck_3687_ == 0 {
                        v___x_3682_ = v___x_3666_;
                        v_isShared_3683_ = v_isSharedCheck_3687_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_3680_);
                        crate::leanh::lean_inc(v_pos_3679_);
                        crate::leanh::lean_dec(v___x_3666_);
                        v___x_3682_ = crate::leanh::lean_box(0);
                        v_isShared_3683_ = v_isSharedCheck_3687_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3672_ = l_ByteSlice_toByteArray(v_res_3668_);
                v___x_3673_ =
                    l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(
                        v___x_3672_,
                    );
                crate::leanh::lean_dec_ref(v___x_3672_);
                v___x_3674_ = crate::leanh::lean_box_uint32(v___x_3673_);
                if v_isShared_3671_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3670_, 1, v___x_3674_);
                    v___x_3676_ = v___x_3670_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3677_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_pos_3667_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3677_, 1, v___x_3674_);
                    v___x_3676_ = v_reuseFailAlloc_3677_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3676_;
            }
            3 => {
                if v_isShared_3683_ == 0 {
                    v___x_3685_ = v___x_3682_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3686_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_pos_3679_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3686_, 1, v_err_3680_);
                    v___x_3685_ = v_reuseFailAlloc_3686_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3685_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi32(
    mut v_a_3688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3695_: u8 = 0;
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3701_: u8 = 0;
    let mut v_pos_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3706_: u8 = 0;
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3710_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3689_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3690_ = l_Std_Internal_Parsec_ByteArray_take(v___x_3689_, v_a_3688_);
                if crate::leanh::lean_obj_tag(v___x_3690_) == 0 {
                    v_pos_3691_ = crate::leanh::lean_ctor_get(v___x_3690_, 0);
                    v_res_3692_ = crate::leanh::lean_ctor_get(v___x_3690_, 1);
                    v_isSharedCheck_3701_ = (!crate::leanh::lean_is_exclusive(v___x_3690_)) as u8;
                    if v_isSharedCheck_3701_ == 0 {
                        v___x_3694_ = v___x_3690_;
                        v_isShared_3695_ = v_isSharedCheck_3701_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_res_3692_);
                        crate::leanh::lean_inc(v_pos_3691_);
                        crate::leanh::lean_dec(v___x_3690_);
                        v___x_3694_ = crate::leanh::lean_box(0);
                        v_isShared_3695_ = v_isSharedCheck_3701_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_3702_ = crate::leanh::lean_ctor_get(v___x_3690_, 0);
                    v_err_3703_ = crate::leanh::lean_ctor_get(v___x_3690_, 1);
                    v_isSharedCheck_3710_ = (!crate::leanh::lean_is_exclusive(v___x_3690_)) as u8;
                    if v_isSharedCheck_3710_ == 0 {
                        v___x_3705_ = v___x_3690_;
                        v_isShared_3706_ = v_isSharedCheck_3710_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_3703_);
                        crate::leanh::lean_inc(v_pos_3702_);
                        crate::leanh::lean_dec(v___x_3690_);
                        v___x_3705_ = crate::leanh::lean_box(0);
                        v_isShared_3706_ = v_isSharedCheck_3710_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3696_ = l_ByteSlice_toByteArray(v_res_3692_);
                v___x_3697_ =
                    l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32(
                        v___x_3696_,
                    );
                crate::leanh::lean_dec_ref(v___x_3696_);
                if v_isShared_3695_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3694_, 1, v___x_3697_);
                    v___x_3699_ = v___x_3694_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3700_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_pos_3691_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3700_, 1, v___x_3697_);
                    v___x_3699_ = v_reuseFailAlloc_3700_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3699_;
            }
            3 => {
                if v_isShared_3706_ == 0 {
                    v___x_3708_ = v___x_3705_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3709_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_pos_3702_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3709_, 1, v_err_3703_);
                    v___x_3708_ = v_reuseFailAlloc_3709_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3708_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(
    mut v_a_3711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: u8 = 0;
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3720_: u8 = 0;
    let mut v_c_3721_: u8 = 0;
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3729_: u8 = 0;
    let mut v_unused_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3712_ = crate::leanh::lean_ctor_get(v_a_3711_, 0);
                v_idx_3713_ = crate::leanh::lean_ctor_get(v_a_3711_, 1);
                v___x_3714_ = lean_byte_array_size(v_array_3712_);
                v___x_3715_ = lean_nat_dec_lt(v_idx_3713_, v___x_3714_);
                if v___x_3715_ == 0 {
                    v___x_3716_ = crate::leanh::lean_box(0);
                    v___x_3717_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3717_, 0, v_a_3711_);
                    crate::leanh::lean_ctor_set(v___x_3717_, 1, v___x_3716_);
                    return v___x_3717_;
                } else {
                    crate::leanh::lean_inc(v_idx_3713_);
                    crate::leanh::lean_inc_ref(v_array_3712_);
                    v_isSharedCheck_3729_ = (!crate::leanh::lean_is_exclusive(v_a_3711_)) as u8;
                    if v_isSharedCheck_3729_ == 0 {
                        v_unused_3730_ = crate::leanh::lean_ctor_get(v_a_3711_, 1);
                        crate::leanh::lean_dec(v_unused_3730_);
                        v_unused_3731_ = crate::leanh::lean_ctor_get(v_a_3711_, 0);
                        crate::leanh::lean_dec(v_unused_3731_);
                        v___x_3719_ = v_a_3711_;
                        v_isShared_3720_ = v_isSharedCheck_3729_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_3711_);
                        v___x_3719_ = crate::leanh::lean_box(0);
                        v_isShared_3720_ = v_isSharedCheck_3729_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_c_3721_ = lean_byte_array_fget(v_array_3712_, v_idx_3713_);
                v___x_3722_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3723_ = lean_nat_add(v_idx_3713_, v___x_3722_);
                crate::leanh::lean_dec(v_idx_3713_);
                if v_isShared_3720_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3719_, 1, v___x_3723_);
                    v_it_x27_3725_ = v___x_3719_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3728_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_array_3712_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3728_, 1, v___x_3723_);
                    v_it_x27_3725_ = v_reuseFailAlloc_3728_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3726_ = crate::leanh::lean_box((v_c_3721_) as usize);
                v___x_3727_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3727_, 0, v_it_x27_3725_);
                crate::leanh::lean_ctor_set(v___x_3727_, 1, v___x_3726_);
                return v___x_3727_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pbool(
    mut v_a_3732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3738_: u8 = 0;
    let mut v___x_3739_: u8 = 0;
    let mut v___x_3740_: u8 = 0;
    let mut v___x_3741_: u8 = 0;
    let mut v___x_3742_: u8 = 0;
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: u8 = 0;
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3752_: u8 = 0;
    let mut v_pos_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3756_: u8 = 0;
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3761_: u8 = 0;
    let mut v_unused_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3733_ =
                    l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(
                        v_a_3732_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3733_) == 0 {
                    v_pos_3734_ = crate::leanh::lean_ctor_get(v___x_3733_, 0);
                    v_res_3735_ = crate::leanh::lean_ctor_get(v___x_3733_, 1);
                    v_isSharedCheck_3752_ = (!crate::leanh::lean_is_exclusive(v___x_3733_)) as u8;
                    if v_isSharedCheck_3752_ == 0 {
                        v___x_3737_ = v___x_3733_;
                        v_isShared_3738_ = v_isSharedCheck_3752_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_res_3735_);
                        crate::leanh::lean_inc(v_pos_3734_);
                        crate::leanh::lean_dec(v___x_3733_);
                        v___x_3737_ = crate::leanh::lean_box(0);
                        v_isShared_3738_ = v_isSharedCheck_3752_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_3753_ = crate::leanh::lean_ctor_get(v___x_3733_, 0);
                    v_isSharedCheck_3761_ = (!crate::leanh::lean_is_exclusive(v___x_3733_)) as u8;
                    if v_isSharedCheck_3761_ == 0 {
                        v_unused_3762_ = crate::leanh::lean_ctor_get(v___x_3733_, 1);
                        crate::leanh::lean_dec(v_unused_3762_);
                        v___x_3755_ = v___x_3733_;
                        v_isShared_3756_ = v_isSharedCheck_3761_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_pos_3753_);
                        crate::leanh::lean_dec(v___x_3733_);
                        v___x_3755_ = crate::leanh::lean_box(0);
                        v_isShared_3756_ = v_isSharedCheck_3761_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3739_ = 0;
                v___x_3740_ = (crate::leanh::lean_unbox(v_res_3735_) as u8);
                crate::leanh::lean_dec(v_res_3735_);
                v___x_3741_ = lean_uint8_dec_eq(v___x_3740_, v___x_3739_);
                if v___x_3741_ == 0 {
                    v___x_3742_ = 1;
                    v___x_3743_ = crate::leanh::lean_box((v___x_3742_) as usize);
                    if v_isShared_3738_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3737_, 1, v___x_3743_);
                        v___x_3745_ = v___x_3737_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3746_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_pos_3734_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3746_, 1, v___x_3743_);
                        v___x_3745_ = v_reuseFailAlloc_3746_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3747_ = 0;
                    v___x_3748_ = crate::leanh::lean_box((v___x_3747_) as usize);
                    if v_isShared_3738_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3737_, 1, v___x_3748_);
                        v___x_3750_ = v___x_3737_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3751_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_pos_3734_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3751_, 1, v___x_3748_);
                        v___x_3750_ = v_reuseFailAlloc_3751_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3745_;
            }
            3 => {
                return v___x_3750_;
            }
            4 => {
                v___x_3757_ = crate::leanh::lean_box(0);
                if v_isShared_3756_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3755_, 1, v___x_3757_);
                    v___x_3759_ = v___x_3755_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3760_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_pos_3753_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3760_, 1, v___x_3757_);
                    v___x_3759_ = v_reuseFailAlloc_3760_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3759_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_utf8_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3763_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__17;
    v_utf8_3764_ = lean_string_to_utf8(v___x_3763_);
    return v_utf8_3764_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader(
    mut v_a_3765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_utf8_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3795_: u8 = 0;
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: u8 = 0;
    let mut v___x_3798_: u32 = 0;
    let mut v___x_3799_: u32 = 0;
    let mut v___x_3800_: u32 = 0;
    let mut v___x_3801_: u32 = 0;
    let mut v___x_3802_: u32 = 0;
    let mut v___x_3803_: u32 = 0;
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3807_: u8 = 0;
    let mut v_pos_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3812_: u8 = 0;
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3816_: u8 = 0;
    let mut v_pos_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3821_: u8 = 0;
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3825_: u8 = 0;
    let mut v_pos_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3830_: u8 = 0;
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3834_: u8 = 0;
    let mut v_pos_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3839_: u8 = 0;
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3843_: u8 = 0;
    let mut v_pos_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3848_: u8 = 0;
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3852_: u8 = 0;
    let mut v_pos_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3857_: u8 = 0;
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3861_: u8 = 0;
    let mut v_pos_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3866_: u8 = 0;
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3870_: u8 = 0;
    let mut v_pos_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3874_: u8 = 0;
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3879_: u8 = 0;
    let mut v_unused_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3885_: u8 = 0;
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3889_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_utf8_3766_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0), core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0_once), _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0);
                v___x_3767_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_3766_, v_a_3765_);
                if crate::leanh::lean_obj_tag(v___x_3767_) == 0 {
                    v_pos_3768_ = crate::leanh::lean_ctor_get(v___x_3767_, 0);
                    crate::leanh::lean_inc(v_pos_3768_);
                    crate::leanh::lean_dec_ref_known(v___x_3767_, 2);
                    v___x_3769_ =
                        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(
                            v_pos_3768_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_3769_) == 0 {
                        v_pos_3770_ = crate::leanh::lean_ctor_get(v___x_3769_, 0);
                        crate::leanh::lean_inc(v_pos_3770_);
                        v_res_3771_ = crate::leanh::lean_ctor_get(v___x_3769_, 1);
                        crate::leanh::lean_inc(v_res_3771_);
                        crate::leanh::lean_dec_ref_known(v___x_3769_, 2);
                        v___x_3772_ = crate::leanh::lean_unsigned_to_nat(15);
                        v___x_3773_ =
                            l_Std_Internal_Parsec_ByteArray_take(v___x_3772_, v_pos_3770_);
                        if crate::leanh::lean_obj_tag(v___x_3773_) == 0 {
                            v_pos_3774_ = crate::leanh::lean_ctor_get(v___x_3773_, 0);
                            crate::leanh::lean_inc(v_pos_3774_);
                            crate::leanh::lean_dec_ref_known(v___x_3773_, 2);
                            v___x_3775_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_3774_);
                            if crate::leanh::lean_obj_tag(v___x_3775_) == 0 {
                                v_pos_3776_ = crate::leanh::lean_ctor_get(v___x_3775_, 0);
                                crate::leanh::lean_inc(v_pos_3776_);
                                v_res_3777_ = crate::leanh::lean_ctor_get(v___x_3775_, 1);
                                crate::leanh::lean_inc(v_res_3777_);
                                crate::leanh::lean_dec_ref_known(v___x_3775_, 2);
                                v___x_3778_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_3776_);
                                if crate::leanh::lean_obj_tag(v___x_3778_) == 0 {
                                    v_pos_3779_ = crate::leanh::lean_ctor_get(v___x_3778_, 0);
                                    crate::leanh::lean_inc(v_pos_3779_);
                                    v_res_3780_ = crate::leanh::lean_ctor_get(v___x_3778_, 1);
                                    crate::leanh::lean_inc(v_res_3780_);
                                    crate::leanh::lean_dec_ref_known(v___x_3778_, 2);
                                    v___x_3781_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_3779_);
                                    if crate::leanh::lean_obj_tag(v___x_3781_) == 0 {
                                        v_pos_3782_ = crate::leanh::lean_ctor_get(v___x_3781_, 0);
                                        crate::leanh::lean_inc(v_pos_3782_);
                                        v_res_3783_ = crate::leanh::lean_ctor_get(v___x_3781_, 1);
                                        crate::leanh::lean_inc(v_res_3783_);
                                        crate::leanh::lean_dec_ref_known(v___x_3781_, 2);
                                        v___x_3784_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_3782_);
                                        if crate::leanh::lean_obj_tag(v___x_3784_) == 0 {
                                            v_pos_3785_ =
                                                crate::leanh::lean_ctor_get(v___x_3784_, 0);
                                            crate::leanh::lean_inc(v_pos_3785_);
                                            v_res_3786_ =
                                                crate::leanh::lean_ctor_get(v___x_3784_, 1);
                                            crate::leanh::lean_inc(v_res_3786_);
                                            crate::leanh::lean_dec_ref_known(v___x_3784_, 2);
                                            v___x_3787_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_3785_);
                                            if crate::leanh::lean_obj_tag(v___x_3787_) == 0 {
                                                v_pos_3788_ =
                                                    crate::leanh::lean_ctor_get(v___x_3787_, 0);
                                                crate::leanh::lean_inc(v_pos_3788_);
                                                v_res_3789_ =
                                                    crate::leanh::lean_ctor_get(v___x_3787_, 1);
                                                crate::leanh::lean_inc(v_res_3789_);
                                                crate::leanh::lean_dec_ref_known(v___x_3787_, 2);
                                                v___x_3790_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_3788_);
                                                if crate::leanh::lean_obj_tag(v___x_3790_) == 0 {
                                                    v_pos_3791_ =
                                                        crate::leanh::lean_ctor_get(v___x_3790_, 0);
                                                    v_res_3792_ =
                                                        crate::leanh::lean_ctor_get(v___x_3790_, 1);
                                                    v_isSharedCheck_3807_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_3790_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_3807_ == 0 {
                                                        v___x_3794_ = v___x_3790_;
                                                        v_isShared_3795_ = v_isSharedCheck_3807_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_res_3792_);
                                                        crate::leanh::lean_inc(v_pos_3791_);
                                                        crate::leanh::lean_dec(v___x_3790_);
                                                        v___x_3794_ = crate::leanh::lean_box(0);
                                                        v_isShared_3795_ = v_isSharedCheck_3807_;
                                                        state = 1;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_res_3789_);
                                                    crate::leanh::lean_dec(v_res_3786_);
                                                    crate::leanh::lean_dec(v_res_3783_);
                                                    crate::leanh::lean_dec(v_res_3780_);
                                                    crate::leanh::lean_dec(v_res_3777_);
                                                    crate::leanh::lean_dec(v_res_3771_);
                                                    v_pos_3808_ =
                                                        crate::leanh::lean_ctor_get(v___x_3790_, 0);
                                                    v_err_3809_ =
                                                        crate::leanh::lean_ctor_get(v___x_3790_, 1);
                                                    v_isSharedCheck_3816_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_3790_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_3816_ == 0 {
                                                        v___x_3811_ = v___x_3790_;
                                                        v_isShared_3812_ = v_isSharedCheck_3816_;
                                                        state = 3;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_err_3809_);
                                                        crate::leanh::lean_inc(v_pos_3808_);
                                                        crate::leanh::lean_dec(v___x_3790_);
                                                        v___x_3811_ = crate::leanh::lean_box(0);
                                                        v_isShared_3812_ = v_isSharedCheck_3816_;
                                                        state = 3;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_res_3786_);
                                                crate::leanh::lean_dec(v_res_3783_);
                                                crate::leanh::lean_dec(v_res_3780_);
                                                crate::leanh::lean_dec(v_res_3777_);
                                                crate::leanh::lean_dec(v_res_3771_);
                                                v_pos_3817_ =
                                                    crate::leanh::lean_ctor_get(v___x_3787_, 0);
                                                v_err_3818_ =
                                                    crate::leanh::lean_ctor_get(v___x_3787_, 1);
                                                v_isSharedCheck_3825_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_3787_))
                                                        as u8;
                                                if v_isSharedCheck_3825_ == 0 {
                                                    v___x_3820_ = v___x_3787_;
                                                    v_isShared_3821_ = v_isSharedCheck_3825_;
                                                    state = 5;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_err_3818_);
                                                    crate::leanh::lean_inc(v_pos_3817_);
                                                    crate::leanh::lean_dec(v___x_3787_);
                                                    v___x_3820_ = crate::leanh::lean_box(0);
                                                    v_isShared_3821_ = v_isSharedCheck_3825_;
                                                    state = 5;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_res_3783_);
                                            crate::leanh::lean_dec(v_res_3780_);
                                            crate::leanh::lean_dec(v_res_3777_);
                                            crate::leanh::lean_dec(v_res_3771_);
                                            v_pos_3826_ =
                                                crate::leanh::lean_ctor_get(v___x_3784_, 0);
                                            v_err_3827_ =
                                                crate::leanh::lean_ctor_get(v___x_3784_, 1);
                                            v_isSharedCheck_3834_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_3784_))
                                                    as u8;
                                            if v_isSharedCheck_3834_ == 0 {
                                                v___x_3829_ = v___x_3784_;
                                                v_isShared_3830_ = v_isSharedCheck_3834_;
                                                state = 7;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_err_3827_);
                                                crate::leanh::lean_inc(v_pos_3826_);
                                                crate::leanh::lean_dec(v___x_3784_);
                                                v___x_3829_ = crate::leanh::lean_box(0);
                                                v_isShared_3830_ = v_isSharedCheck_3834_;
                                                state = 7;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_res_3780_);
                                        crate::leanh::lean_dec(v_res_3777_);
                                        crate::leanh::lean_dec(v_res_3771_);
                                        v_pos_3835_ = crate::leanh::lean_ctor_get(v___x_3781_, 0);
                                        v_err_3836_ = crate::leanh::lean_ctor_get(v___x_3781_, 1);
                                        v_isSharedCheck_3843_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3781_)) as u8;
                                        if v_isSharedCheck_3843_ == 0 {
                                            v___x_3838_ = v___x_3781_;
                                            v_isShared_3839_ = v_isSharedCheck_3843_;
                                            state = 9;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_err_3836_);
                                            crate::leanh::lean_inc(v_pos_3835_);
                                            crate::leanh::lean_dec(v___x_3781_);
                                            v___x_3838_ = crate::leanh::lean_box(0);
                                            v_isShared_3839_ = v_isSharedCheck_3843_;
                                            state = 9;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_res_3777_);
                                    crate::leanh::lean_dec(v_res_3771_);
                                    v_pos_3844_ = crate::leanh::lean_ctor_get(v___x_3778_, 0);
                                    v_err_3845_ = crate::leanh::lean_ctor_get(v___x_3778_, 1);
                                    v_isSharedCheck_3852_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3778_)) as u8;
                                    if v_isSharedCheck_3852_ == 0 {
                                        v___x_3847_ = v___x_3778_;
                                        v_isShared_3848_ = v_isSharedCheck_3852_;
                                        state = 11;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_err_3845_);
                                        crate::leanh::lean_inc(v_pos_3844_);
                                        crate::leanh::lean_dec(v___x_3778_);
                                        v___x_3847_ = crate::leanh::lean_box(0);
                                        v_isShared_3848_ = v_isSharedCheck_3852_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_res_3771_);
                                v_pos_3853_ = crate::leanh::lean_ctor_get(v___x_3775_, 0);
                                v_err_3854_ = crate::leanh::lean_ctor_get(v___x_3775_, 1);
                                v_isSharedCheck_3861_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3775_)) as u8;
                                if v_isSharedCheck_3861_ == 0 {
                                    v___x_3856_ = v___x_3775_;
                                    v_isShared_3857_ = v_isSharedCheck_3861_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_err_3854_);
                                    crate::leanh::lean_inc(v_pos_3853_);
                                    crate::leanh::lean_dec(v___x_3775_);
                                    v___x_3856_ = crate::leanh::lean_box(0);
                                    v_isShared_3857_ = v_isSharedCheck_3861_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_res_3771_);
                            v_pos_3862_ = crate::leanh::lean_ctor_get(v___x_3773_, 0);
                            v_err_3863_ = crate::leanh::lean_ctor_get(v___x_3773_, 1);
                            v_isSharedCheck_3870_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3773_)) as u8;
                            if v_isSharedCheck_3870_ == 0 {
                                v___x_3865_ = v___x_3773_;
                                v_isShared_3866_ = v_isSharedCheck_3870_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_err_3863_);
                                crate::leanh::lean_inc(v_pos_3862_);
                                crate::leanh::lean_dec(v___x_3773_);
                                v___x_3865_ = crate::leanh::lean_box(0);
                                v_isShared_3866_ = v_isSharedCheck_3870_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        v_pos_3871_ = crate::leanh::lean_ctor_get(v___x_3769_, 0);
                        v_isSharedCheck_3879_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3769_)) as u8;
                        if v_isSharedCheck_3879_ == 0 {
                            v_unused_3880_ = crate::leanh::lean_ctor_get(v___x_3769_, 1);
                            crate::leanh::lean_dec(v_unused_3880_);
                            v___x_3873_ = v___x_3769_;
                            v_isShared_3874_ = v_isSharedCheck_3879_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_pos_3871_);
                            crate::leanh::lean_dec(v___x_3769_);
                            v___x_3873_ = crate::leanh::lean_box(0);
                            v_isShared_3874_ = v_isSharedCheck_3879_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    v_pos_3881_ = crate::leanh::lean_ctor_get(v___x_3767_, 0);
                    v_err_3882_ = crate::leanh::lean_ctor_get(v___x_3767_, 1);
                    v_isSharedCheck_3889_ = (!crate::leanh::lean_is_exclusive(v___x_3767_)) as u8;
                    if v_isSharedCheck_3889_ == 0 {
                        v___x_3884_ = v___x_3767_;
                        v_isShared_3885_ = v_isSharedCheck_3889_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_3882_);
                        crate::leanh::lean_inc(v_pos_3881_);
                        crate::leanh::lean_dec(v___x_3767_);
                        v___x_3884_ = crate::leanh::lean_box(0);
                        v_isShared_3885_ = v_isSharedCheck_3889_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3796_ = crate::leanh::lean_alloc_ctor(0, 0, (25) as u32);
                v___x_3797_ = (crate::leanh::lean_unbox(v_res_3771_) as u8);
                crate::leanh::lean_dec(v_res_3771_);
                crate::leanh::lean_ctor_set_uint8(v___x_3796_, 24 as u32, v___x_3797_);
                v___x_3798_ = crate::leanh::lean_unbox_uint32(v_res_3777_);
                crate::leanh::lean_dec(v_res_3777_);
                crate::leanh::lean_ctor_set_uint32(v___x_3796_, 0 as u32, v___x_3798_);
                v___x_3799_ = crate::leanh::lean_unbox_uint32(v_res_3780_);
                crate::leanh::lean_dec(v_res_3780_);
                crate::leanh::lean_ctor_set_uint32(v___x_3796_, 4 as u32, v___x_3799_);
                v___x_3800_ = crate::leanh::lean_unbox_uint32(v_res_3783_);
                crate::leanh::lean_dec(v_res_3783_);
                crate::leanh::lean_ctor_set_uint32(v___x_3796_, 8 as u32, v___x_3800_);
                v___x_3801_ = crate::leanh::lean_unbox_uint32(v_res_3786_);
                crate::leanh::lean_dec(v_res_3786_);
                crate::leanh::lean_ctor_set_uint32(v___x_3796_, 12 as u32, v___x_3801_);
                v___x_3802_ = crate::leanh::lean_unbox_uint32(v_res_3789_);
                crate::leanh::lean_dec(v_res_3789_);
                crate::leanh::lean_ctor_set_uint32(v___x_3796_, 16 as u32, v___x_3802_);
                v___x_3803_ = crate::leanh::lean_unbox_uint32(v_res_3792_);
                crate::leanh::lean_dec(v_res_3792_);
                crate::leanh::lean_ctor_set_uint32(v___x_3796_, 20 as u32, v___x_3803_);
                if v_isShared_3795_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3794_, 1, v___x_3796_);
                    v___x_3805_ = v___x_3794_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3806_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_pos_3791_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3806_, 1, v___x_3796_);
                    v___x_3805_ = v_reuseFailAlloc_3806_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3805_;
            }
            3 => {
                if v_isShared_3812_ == 0 {
                    v___x_3814_ = v___x_3811_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3815_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_pos_3808_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3815_, 1, v_err_3809_);
                    v___x_3814_ = v_reuseFailAlloc_3815_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3814_;
            }
            5 => {
                if v_isShared_3821_ == 0 {
                    v___x_3823_ = v___x_3820_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3824_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_pos_3817_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3824_, 1, v_err_3818_);
                    v___x_3823_ = v_reuseFailAlloc_3824_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3823_;
            }
            7 => {
                if v_isShared_3830_ == 0 {
                    v___x_3832_ = v___x_3829_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3833_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_pos_3826_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3833_, 1, v_err_3827_);
                    v___x_3832_ = v_reuseFailAlloc_3833_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3832_;
            }
            9 => {
                if v_isShared_3839_ == 0 {
                    v___x_3841_ = v___x_3838_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3842_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_pos_3835_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3842_, 1, v_err_3836_);
                    v___x_3841_ = v_reuseFailAlloc_3842_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3841_;
            }
            11 => {
                if v_isShared_3848_ == 0 {
                    v___x_3850_ = v___x_3847_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3851_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_pos_3844_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3851_, 1, v_err_3845_);
                    v___x_3850_ = v_reuseFailAlloc_3851_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3850_;
            }
            13 => {
                if v_isShared_3857_ == 0 {
                    v___x_3859_ = v___x_3856_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3860_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_pos_3853_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 1, v_err_3854_);
                    v___x_3859_ = v_reuseFailAlloc_3860_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3859_;
            }
            15 => {
                if v_isShared_3866_ == 0 {
                    v___x_3868_ = v___x_3865_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3869_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_pos_3862_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3869_, 1, v_err_3863_);
                    v___x_3868_ = v_reuseFailAlloc_3869_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3868_;
            }
            17 => {
                v___x_3875_ = crate::leanh::lean_box(0);
                if v_isShared_3874_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3873_, 1, v___x_3875_);
                    v___x_3877_ = v___x_3873_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3878_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_pos_3871_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3878_, 1, v___x_3875_);
                    v___x_3877_ = v_reuseFailAlloc_3878_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3877_;
            }
            19 => {
                if v_isShared_3885_ == 0 {
                    v___x_3887_ = v___x_3884_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3888_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_pos_3881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3888_, 1, v_err_3882_);
                    v___x_3887_ = v_reuseFailAlloc_3888_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3887_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeType(
    mut v_a_3890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3902_: u8 = 0;
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: u8 = 0;
    let mut v___x_3905_: u8 = 0;
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3909_: u8 = 0;
    let mut v_pos_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3913_: u8 = 0;
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3918_: u8 = 0;
    let mut v_unused_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3923_: u8 = 0;
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3928_: u8 = 0;
    let mut v_unused_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3934_: u8 = 0;
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3938_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3891_ =
                    l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi32(
                        v_a_3890_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3891_) == 0 {
                    v_pos_3892_ = crate::leanh::lean_ctor_get(v___x_3891_, 0);
                    crate::leanh::lean_inc(v_pos_3892_);
                    v_res_3893_ = crate::leanh::lean_ctor_get(v___x_3891_, 1);
                    crate::leanh::lean_inc(v_res_3893_);
                    crate::leanh::lean_dec_ref_known(v___x_3891_, 2);
                    v___x_3894_ =
                        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pbool(
                            v_pos_3892_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_3894_) == 0 {
                        v_pos_3895_ = crate::leanh::lean_ctor_get(v___x_3894_, 0);
                        crate::leanh::lean_inc(v_pos_3895_);
                        v_res_3896_ = crate::leanh::lean_ctor_get(v___x_3894_, 1);
                        crate::leanh::lean_inc(v_res_3896_);
                        crate::leanh::lean_dec_ref_known(v___x_3894_, 2);
                        v___x_3897_ =
                            l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(
                                v_pos_3895_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_3897_) == 0 {
                            v_pos_3898_ = crate::leanh::lean_ctor_get(v___x_3897_, 0);
                            v_res_3899_ = crate::leanh::lean_ctor_get(v___x_3897_, 1);
                            v_isSharedCheck_3909_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3897_)) as u8;
                            if v_isSharedCheck_3909_ == 0 {
                                v___x_3901_ = v___x_3897_;
                                v_isShared_3902_ = v_isSharedCheck_3909_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_res_3899_);
                                crate::leanh::lean_inc(v_pos_3898_);
                                crate::leanh::lean_dec(v___x_3897_);
                                v___x_3901_ = crate::leanh::lean_box(0);
                                v_isShared_3902_ = v_isSharedCheck_3909_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_res_3896_);
                            crate::leanh::lean_dec(v_res_3893_);
                            v_pos_3910_ = crate::leanh::lean_ctor_get(v___x_3897_, 0);
                            v_isSharedCheck_3918_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3897_)) as u8;
                            if v_isSharedCheck_3918_ == 0 {
                                v_unused_3919_ = crate::leanh::lean_ctor_get(v___x_3897_, 1);
                                crate::leanh::lean_dec(v_unused_3919_);
                                v___x_3912_ = v___x_3897_;
                                v_isShared_3913_ = v_isSharedCheck_3918_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_pos_3910_);
                                crate::leanh::lean_dec(v___x_3897_);
                                v___x_3912_ = crate::leanh::lean_box(0);
                                v_isShared_3913_ = v_isSharedCheck_3918_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_res_3893_);
                        v_pos_3920_ = crate::leanh::lean_ctor_get(v___x_3894_, 0);
                        v_isSharedCheck_3928_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3894_)) as u8;
                        if v_isSharedCheck_3928_ == 0 {
                            v_unused_3929_ = crate::leanh::lean_ctor_get(v___x_3894_, 1);
                            crate::leanh::lean_dec(v_unused_3929_);
                            v___x_3922_ = v___x_3894_;
                            v_isShared_3923_ = v_isSharedCheck_3928_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_pos_3920_);
                            crate::leanh::lean_dec(v___x_3894_);
                            v___x_3922_ = crate::leanh::lean_box(0);
                            v_isShared_3923_ = v_isSharedCheck_3928_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_pos_3930_ = crate::leanh::lean_ctor_get(v___x_3891_, 0);
                    v_err_3931_ = crate::leanh::lean_ctor_get(v___x_3891_, 1);
                    v_isSharedCheck_3938_ = (!crate::leanh::lean_is_exclusive(v___x_3891_)) as u8;
                    if v_isSharedCheck_3938_ == 0 {
                        v___x_3933_ = v___x_3891_;
                        v_isShared_3934_ = v_isSharedCheck_3938_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_3931_);
                        crate::leanh::lean_inc(v_pos_3930_);
                        crate::leanh::lean_dec(v___x_3891_);
                        v___x_3933_ = crate::leanh::lean_box(0);
                        v_isShared_3934_ = v_isSharedCheck_3938_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3903_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_3903_, 0, v_res_3893_);
                v___x_3904_ = (crate::leanh::lean_unbox(v_res_3896_) as u8);
                crate::leanh::lean_dec(v_res_3896_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3903_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3904_,
                );
                v___x_3905_ = (crate::leanh::lean_unbox(v_res_3899_) as u8);
                crate::leanh::lean_dec(v_res_3899_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3903_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    v___x_3905_,
                );
                if v_isShared_3902_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3901_, 1, v___x_3903_);
                    v___x_3907_ = v___x_3901_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3908_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_pos_3898_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3908_, 1, v___x_3903_);
                    v___x_3907_ = v_reuseFailAlloc_3908_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3907_;
            }
            3 => {
                v___x_3914_ = crate::leanh::lean_box(0);
                if v_isShared_3913_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3912_, 1, v___x_3914_);
                    v___x_3916_ = v___x_3912_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3917_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_pos_3910_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 1, v___x_3914_);
                    v___x_3916_ = v_reuseFailAlloc_3917_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3916_;
            }
            5 => {
                v___x_3924_ = crate::leanh::lean_box(0);
                if v_isShared_3923_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3922_, 1, v___x_3924_);
                    v___x_3926_ = v___x_3922_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3927_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_pos_3920_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3927_, 1, v___x_3924_);
                    v___x_3926_ = v_reuseFailAlloc_3927_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3926_;
            }
            7 => {
                if v_isShared_3934_ == 0 {
                    v___x_3936_ = v___x_3933_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3937_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_pos_3930_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3937_, 1, v_err_3931_);
                    v___x_3936_ = v_reuseFailAlloc_3937_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3936_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSecond(
    mut v_p_3939_: *mut crate::leanh::LeanObject,
    mut v_a_3940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3949_: u8 = 0;
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3954_: u8 = 0;
    let mut v_pos_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3959_: u8 = 0;
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3963_: u8 = 0;
    let mut v_pos_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3968_: u8 = 0;
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3972_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3941_ = crate::leanh::lean_apply_1(v_p_3939_, v_a_3940_);
                if crate::leanh::lean_obj_tag(v___x_3941_) == 0 {
                    v_pos_3942_ = crate::leanh::lean_ctor_get(v___x_3941_, 0);
                    crate::leanh::lean_inc(v_pos_3942_);
                    v_res_3943_ = crate::leanh::lean_ctor_get(v___x_3941_, 1);
                    crate::leanh::lean_inc(v_res_3943_);
                    crate::leanh::lean_dec_ref_known(v___x_3941_, 2);
                    v___x_3944_ =
                        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi32(
                            v_pos_3942_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_3944_) == 0 {
                        v_pos_3945_ = crate::leanh::lean_ctor_get(v___x_3944_, 0);
                        v_res_3946_ = crate::leanh::lean_ctor_get(v___x_3944_, 1);
                        v_isSharedCheck_3954_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3944_)) as u8;
                        if v_isSharedCheck_3954_ == 0 {
                            v___x_3948_ = v___x_3944_;
                            v_isShared_3949_ = v_isSharedCheck_3954_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_res_3946_);
                            crate::leanh::lean_inc(v_pos_3945_);
                            crate::leanh::lean_dec(v___x_3944_);
                            v___x_3948_ = crate::leanh::lean_box(0);
                            v_isShared_3949_ = v_isSharedCheck_3954_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_res_3943_);
                        v_pos_3955_ = crate::leanh::lean_ctor_get(v___x_3944_, 0);
                        v_err_3956_ = crate::leanh::lean_ctor_get(v___x_3944_, 1);
                        v_isSharedCheck_3963_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3944_)) as u8;
                        if v_isSharedCheck_3963_ == 0 {
                            v___x_3958_ = v___x_3944_;
                            v_isShared_3959_ = v_isSharedCheck_3963_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_err_3956_);
                            crate::leanh::lean_inc(v_pos_3955_);
                            crate::leanh::lean_dec(v___x_3944_);
                            v___x_3958_ = crate::leanh::lean_box(0);
                            v_isShared_3959_ = v_isSharedCheck_3963_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_pos_3964_ = crate::leanh::lean_ctor_get(v___x_3941_, 0);
                    v_err_3965_ = crate::leanh::lean_ctor_get(v___x_3941_, 1);
                    v_isSharedCheck_3972_ = (!crate::leanh::lean_is_exclusive(v___x_3941_)) as u8;
                    if v_isSharedCheck_3972_ == 0 {
                        v___x_3967_ = v___x_3941_;
                        v_isShared_3968_ = v_isSharedCheck_3972_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_3965_);
                        crate::leanh::lean_inc(v_pos_3964_);
                        crate::leanh::lean_dec(v___x_3941_);
                        v___x_3967_ = crate::leanh::lean_box(0);
                        v_isShared_3968_ = v_isSharedCheck_3972_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3950_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3950_, 0, v_res_3943_);
                crate::leanh::lean_ctor_set(v___x_3950_, 1, v_res_3946_);
                if v_isShared_3949_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3948_, 1, v___x_3950_);
                    v___x_3952_ = v___x_3948_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3953_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_pos_3945_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3953_, 1, v___x_3950_);
                    v___x_3952_ = v_reuseFailAlloc_3953_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3952_;
            }
            3 => {
                if v_isShared_3959_ == 0 {
                    v___x_3961_ = v___x_3958_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3962_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_pos_3955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3962_, 1, v_err_3956_);
                    v___x_3961_ = v_reuseFailAlloc_3962_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3961_;
            }
            5 => {
                if v_isShared_3968_ == 0 {
                    v___x_3970_ = v___x_3967_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3971_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_pos_3964_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3971_, 1, v_err_3965_);
                    v___x_3970_ = v_reuseFailAlloc_3971_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3970_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes(
    mut v_size_3973_: *mut crate::leanh::LeanObject,
    mut v_n_3974_: u32,
    mut v_a_3975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3976_ = lean_uint32_to_nat(v_n_3974_);
    v___x_3977_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(
        v___x_3976_,
        v_size_3973_,
        v_a_3975_,
    );
    crate::leanh::lean_dec(v___x_3976_);
    return v___x_3977_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes___boxed(
    mut v_size_3978_: *mut crate::leanh::LeanObject,
    mut v_n_3979_: *mut crate::leanh::LeanObject,
    mut v_a_3980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_3981_: u32 = 0;
    let mut v_res_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_3981_ = crate::leanh::lean_unbox_uint32(v_n_3979_);
    crate::leanh::lean_dec(v_n_3979_);
    v_res_3982_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes(
            v_size_3978_,
            v_n_boxed_3981_,
            v_a_3980_,
        );
    return v_res_3982_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(
    mut v_n_3983_: u32,
    mut v_a_3984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3985_ = lean_uint32_to_nat(v_n_3983_);
    v___x_3986_ = crate::leanh::lean_alloc_closure(
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8
            as *mut core::ffi::c_void,
        1,
        0,
    );
    v___x_3987_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(
        v___x_3985_,
        v___x_3986_,
        v_a_3984_,
    );
    crate::leanh::lean_dec(v___x_3985_);
    return v___x_3987_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices___boxed(
    mut v_n_3988_: *mut crate::leanh::LeanObject,
    mut v_a_3989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_3990_: u32 = 0;
    let mut v_res_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_3990_ = crate::leanh::lean_unbox_uint32(v_n_3988_);
    crate::leanh::lean_dec(v_n_3988_);
    v_res_3991_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(
            v_n_boxed_3990_,
            v_a_3989_,
        );
    return v_res_3991_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(
    mut v_n_3992_: u32,
    mut v_a_3993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3994_ = lean_uint32_to_nat(v_n_3992_);
    v___x_3995_ = crate::leanh::lean_alloc_closure(
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeType
            as *mut core::ffi::c_void,
        1,
        0,
    );
    v___x_3996_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(
        v___x_3994_,
        v___x_3995_,
        v_a_3993_,
    );
    crate::leanh::lean_dec(v___x_3994_);
    return v___x_3996_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes___boxed(
    mut v_n_3997_: *mut crate::leanh::LeanObject,
    mut v_a_3998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_3999_: u32 = 0;
    let mut v_res_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_3999_ = crate::leanh::lean_unbox_uint32(v_n_3997_);
    crate::leanh::lean_dec(v_n_3997_);
    v_res_4000_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(
            v_n_boxed_3999_,
            v_a_3998_,
        );
    return v_res_4000_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(
    mut v_upperBound_4002_: *mut crate::leanh::LeanObject,
    mut v_res_4003_: *mut crate::leanh::LeanObject,
    mut v_a_4004_: *mut crate::leanh::LeanObject,
    mut v_b_4005_: *mut crate::leanh::LeanObject,
    mut v___y_4006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4007_: u8 = 0;
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4013_: u8 = 0;
    let mut v___x_4014_: u8 = 0;
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: u8 = 0;
    let mut v___x_4018_: u8 = 0;
    let mut v___x_4019_: u8 = 0;
    let mut v___x_4020_: u8 = 0;
    let mut v___x_4021_: u32 = 0;
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_current_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4035_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4007_ = lean_nat_dec_lt(v_a_4004_, v_upperBound_4002_);
                if v___x_4007_ == 0 {
                    crate::leanh::lean_dec(v_a_4004_);
                    v___x_4008_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4008_, 0, v___y_4006_);
                    crate::leanh::lean_ctor_set(v___x_4008_, 1, v_b_4005_);
                    return v___x_4008_;
                } else {
                    v_fst_4009_ = crate::leanh::lean_ctor_get(v_b_4005_, 0);
                    v_snd_4010_ = crate::leanh::lean_ctor_get(v_b_4005_, 1);
                    v_isSharedCheck_4035_ = (!crate::leanh::lean_is_exclusive(v_b_4005_)) as u8;
                    if v_isSharedCheck_4035_ == 0 {
                        v___x_4012_ = v_b_4005_;
                        v_isShared_4013_ = v_isSharedCheck_4035_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4010_);
                        crate::leanh::lean_inc(v_fst_4009_);
                        crate::leanh::lean_dec(v_b_4005_);
                        v___x_4012_ = crate::leanh::lean_box(0);
                        v_isShared_4013_ = v_isSharedCheck_4035_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4014_ = l_instInhabitedUInt8;
                v___x_4015_ = crate::leanh::lean_box((v___x_4014_) as usize);
                v___x_4016_ = lean_array_get(v___x_4015_, v_res_4003_, v_a_4004_);
                crate::leanh::lean_dec(v___x_4015_);
                v___x_4017_ = 0;
                v___x_4018_ = (crate::leanh::lean_unbox(v___x_4016_) as u8);
                v___x_4019_ = lean_uint8_dec_eq(v___x_4018_, v___x_4017_);
                if v___x_4019_ == 0 {
                    v___x_4020_ = (crate::leanh::lean_unbox(v___x_4016_) as u8);
                    crate::leanh::lean_dec(v___x_4016_);
                    v___x_4021_ = lean_uint8_to_uint32(v___x_4020_);
                    v___x_4022_ = lean_string_push(v_snd_4010_, v___x_4021_);
                    if v_isShared_4013_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4012_, 1, v___x_4022_);
                        v___x_4024_ = v___x_4012_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4028_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_fst_4009_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4028_, 1, v___x_4022_);
                        v___x_4024_ = v_reuseFailAlloc_4028_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4016_);
                    crate::leanh::lean_dec(v_a_4004_);
                    v_current_4029_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0;
                    v___x_4030_ = lean_array_push(v_fst_4009_, v_snd_4010_);
                    if v_isShared_4013_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4012_, 1, v_current_4029_);
                        crate::leanh::lean_ctor_set(v___x_4012_, 0, v___x_4030_);
                        v___x_4032_ = v___x_4012_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4034_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4034_, 0, v___x_4030_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4034_, 1, v_current_4029_);
                        v___x_4032_ = v_reuseFailAlloc_4034_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4025_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4026_ = lean_nat_add(v_a_4004_, v___x_4025_);
                crate::leanh::lean_dec(v_a_4004_);
                v_a_4004_ = v___x_4026_;
                v_b_4005_ = v___x_4024_;
                state = 0;
                continue;
            }
            3 => {
                v___x_4033_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4033_, 0, v___y_4006_);
                crate::leanh::lean_ctor_set(v___x_4033_, 1, v___x_4032_);
                return v___x_4033_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___boxed(
    mut v_upperBound_4036_: *mut crate::leanh::LeanObject,
    mut v_res_4037_: *mut crate::leanh::LeanObject,
    mut v_a_4038_: *mut crate::leanh::LeanObject,
    mut v_b_4039_: *mut crate::leanh::LeanObject,
    mut v___y_4040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4041_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(v_upperBound_4036_, v_res_4037_, v_a_4038_, v_b_4039_, v___y_4040_);
    crate::leanh::lean_dec_ref(v_res_4037_);
    crate::leanh::lean_dec(v_upperBound_4036_);
    return v_res_4041_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1(
    mut v___x_4042_: *mut crate::leanh::LeanObject,
    mut v_res_4043_: *mut crate::leanh::LeanObject,
    mut v_as_4044_: *mut crate::leanh::LeanObject,
    mut v_sz_4045_: usize,
    mut v_i_4046_: usize,
    mut v_b_4047_: *mut crate::leanh::LeanObject,
    mut v___y_4048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4049_: u8 = 0;
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_abbreviationIndex_4052_: u8 = 0;
    let mut v_fst_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4057_: u8 = 0;
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4068_: u8 = 0;
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: usize = 0;
    let mut v___x_4072_: usize = 0;
    let mut v_reuseFailAlloc_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4075_: u8 = 0;
    let mut v_reuseFailAlloc_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4077_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4049_ = lean_usize_dec_lt(v_i_4046_, v_sz_4045_);
                if v___x_4049_ == 0 {
                    v___x_4050_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4050_, 0, v___y_4048_);
                    crate::leanh::lean_ctor_set(v___x_4050_, 1, v_b_4047_);
                    return v___x_4050_;
                } else {
                    v_a_4051_ = lean_array_uget_borrowed(v_as_4044_, v_i_4046_);
                    v_abbreviationIndex_4052_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_4051_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    );
                    v_fst_4053_ = crate::leanh::lean_ctor_get(v_b_4047_, 0);
                    v_snd_4054_ = crate::leanh::lean_ctor_get(v_b_4047_, 1);
                    v_isSharedCheck_4077_ = (!crate::leanh::lean_is_exclusive(v_b_4047_)) as u8;
                    if v_isSharedCheck_4077_ == 0 {
                        v___x_4056_ = v_b_4047_;
                        v_isShared_4057_ = v_isSharedCheck_4077_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4054_);
                        crate::leanh::lean_inc(v_fst_4053_);
                        crate::leanh::lean_dec(v_b_4047_);
                        v___x_4056_ = crate::leanh::lean_box(0);
                        v_isShared_4057_ = v_isSharedCheck_4077_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4058_ = lean_uint8_to_nat(v_abbreviationIndex_4052_);
                if v_isShared_4057_ == 0 {
                    v___x_4060_ = v___x_4056_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4076_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_fst_4053_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4076_, 1, v_snd_4054_);
                    v___x_4060_ = v_reuseFailAlloc_4076_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4061_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(v___x_4042_, v_res_4043_, v___x_4058_, v___x_4060_, v___y_4048_);
                if crate::leanh::lean_obj_tag(v___x_4061_) == 0 {
                    v_res_4062_ = crate::leanh::lean_ctor_get(v___x_4061_, 1);
                    crate::leanh::lean_inc(v_res_4062_);
                    v_pos_4063_ = crate::leanh::lean_ctor_get(v___x_4061_, 0);
                    crate::leanh::lean_inc(v_pos_4063_);
                    crate::leanh::lean_dec_ref_known(v___x_4061_, 2);
                    v_fst_4064_ = crate::leanh::lean_ctor_get(v_res_4062_, 0);
                    v_snd_4065_ = crate::leanh::lean_ctor_get(v_res_4062_, 1);
                    v_isSharedCheck_4075_ = (!crate::leanh::lean_is_exclusive(v_res_4062_)) as u8;
                    if v_isSharedCheck_4075_ == 0 {
                        v___x_4067_ = v_res_4062_;
                        v_isShared_4068_ = v_isSharedCheck_4075_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4065_);
                        crate::leanh::lean_inc(v_fst_4064_);
                        crate::leanh::lean_dec(v_res_4062_);
                        v___x_4067_ = crate::leanh::lean_box(0);
                        v_isShared_4068_ = v_isSharedCheck_4075_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_4061_;
                }
            }
            3 => {
                if v_isShared_4068_ == 0 {
                    v___x_4070_ = v___x_4067_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4074_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_fst_4064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4074_, 1, v_snd_4065_);
                    v___x_4070_ = v_reuseFailAlloc_4074_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4071_ = 1usize;
                v___x_4072_ = lean_usize_add(v_i_4046_, v___x_4071_);
                v_i_4046_ = v___x_4072_;
                v_b_4047_ = v___x_4070_;
                v___y_4048_ = v_pos_4063_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1___boxed(
    mut v___x_4078_: *mut crate::leanh::LeanObject,
    mut v_res_4079_: *mut crate::leanh::LeanObject,
    mut v_as_4080_: *mut crate::leanh::LeanObject,
    mut v_sz_4081_: *mut crate::leanh::LeanObject,
    mut v_i_4082_: *mut crate::leanh::LeanObject,
    mut v_b_4083_: *mut crate::leanh::LeanObject,
    mut v___y_4084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4085_: usize = 0;
    let mut v_i_boxed_4086_: usize = 0;
    let mut v_res_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4085_ = crate::leanh::lean_unbox_usize(v_sz_4081_);
    crate::leanh::lean_dec(v_sz_4081_);
    v_i_boxed_4086_ = crate::leanh::lean_unbox_usize(v_i_4082_);
    crate::leanh::lean_dec(v_i_4082_);
    v_res_4087_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1(v___x_4078_, v_res_4079_, v_as_4080_, v_sz_boxed_4085_, v_i_boxed_4086_, v_b_4083_, v___y_4084_);
    crate::leanh::lean_dec_ref(v_as_4080_);
    crate::leanh::lean_dec_ref(v_res_4079_);
    crate::leanh::lean_dec(v___x_4078_);
    return v_res_4087_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(
    mut v_times_4093_: *mut crate::leanh::LeanObject,
    mut v_n_4094_: u32,
    mut v_a_4095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4102_: usize = 0;
    let mut v___x_4103_: usize = 0;
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4109_: u8 = 0;
    let mut v_fst_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4114_: u8 = 0;
    let mut v_pos_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4119_: u8 = 0;
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4123_: u8 = 0;
    let mut v_pos_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4128_: u8 = 0;
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4132_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4096_ = lean_uint32_to_nat(v_n_4094_);
                v___x_4097_ = crate::leanh::lean_alloc_closure(
                    l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8
                        as *mut core::ffi::c_void,
                    1,
                    0,
                );
                v___x_4098_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_4096_, v___x_4097_, v_a_4095_);
                if crate::leanh::lean_obj_tag(v___x_4098_) == 0 {
                    v_pos_4099_ = crate::leanh::lean_ctor_get(v___x_4098_, 0);
                    crate::leanh::lean_inc(v_pos_4099_);
                    v_res_4100_ = crate::leanh::lean_ctor_get(v___x_4098_, 1);
                    crate::leanh::lean_inc(v_res_4100_);
                    crate::leanh::lean_dec_ref_known(v___x_4098_, 2);
                    v___x_4101_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__1;
                    v_sz_4102_ = lean_array_size(v_times_4093_);
                    v___x_4103_ = 0usize;
                    v___x_4104_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1(v___x_4096_, v_res_4100_, v_times_4093_, v_sz_4102_, v___x_4103_, v___x_4101_, v_pos_4099_);
                    crate::leanh::lean_dec(v_res_4100_);
                    crate::leanh::lean_dec(v___x_4096_);
                    if crate::leanh::lean_obj_tag(v___x_4104_) == 0 {
                        v_res_4105_ = crate::leanh::lean_ctor_get(v___x_4104_, 1);
                        v_pos_4106_ = crate::leanh::lean_ctor_get(v___x_4104_, 0);
                        v_isSharedCheck_4114_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4104_)) as u8;
                        if v_isSharedCheck_4114_ == 0 {
                            v___x_4108_ = v___x_4104_;
                            v_isShared_4109_ = v_isSharedCheck_4114_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_res_4105_);
                            crate::leanh::lean_inc(v_pos_4106_);
                            crate::leanh::lean_dec(v___x_4104_);
                            v___x_4108_ = crate::leanh::lean_box(0);
                            v_isShared_4109_ = v_isSharedCheck_4114_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_pos_4115_ = crate::leanh::lean_ctor_get(v___x_4104_, 0);
                        v_err_4116_ = crate::leanh::lean_ctor_get(v___x_4104_, 1);
                        v_isSharedCheck_4123_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4104_)) as u8;
                        if v_isSharedCheck_4123_ == 0 {
                            v___x_4118_ = v___x_4104_;
                            v_isShared_4119_ = v_isSharedCheck_4123_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_err_4116_);
                            crate::leanh::lean_inc(v_pos_4115_);
                            crate::leanh::lean_dec(v___x_4104_);
                            v___x_4118_ = crate::leanh::lean_box(0);
                            v_isShared_4119_ = v_isSharedCheck_4123_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4096_);
                    v_pos_4124_ = crate::leanh::lean_ctor_get(v___x_4098_, 0);
                    v_err_4125_ = crate::leanh::lean_ctor_get(v___x_4098_, 1);
                    v_isSharedCheck_4132_ = (!crate::leanh::lean_is_exclusive(v___x_4098_)) as u8;
                    if v_isSharedCheck_4132_ == 0 {
                        v___x_4127_ = v___x_4098_;
                        v_isShared_4128_ = v_isSharedCheck_4132_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_4125_);
                        crate::leanh::lean_inc(v_pos_4124_);
                        crate::leanh::lean_dec(v___x_4098_);
                        v___x_4127_ = crate::leanh::lean_box(0);
                        v_isShared_4128_ = v_isSharedCheck_4132_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4110_ = crate::leanh::lean_ctor_get(v_res_4105_, 0);
                crate::leanh::lean_inc(v_fst_4110_);
                crate::leanh::lean_dec(v_res_4105_);
                if v_isShared_4109_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4108_, 1, v_fst_4110_);
                    v___x_4112_ = v___x_4108_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4113_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_pos_4106_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 1, v_fst_4110_);
                    v___x_4112_ = v_reuseFailAlloc_4113_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4112_;
            }
            3 => {
                if v_isShared_4119_ == 0 {
                    v___x_4121_ = v___x_4118_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4122_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_pos_4115_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4122_, 1, v_err_4116_);
                    v___x_4121_ = v_reuseFailAlloc_4122_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4121_;
            }
            5 => {
                if v_isShared_4128_ == 0 {
                    v___x_4130_ = v___x_4127_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4131_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_pos_4124_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4131_, 1, v_err_4125_);
                    v___x_4130_ = v_reuseFailAlloc_4131_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4130_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___boxed(
    mut v_times_4133_: *mut crate::leanh::LeanObject,
    mut v_n_4134_: *mut crate::leanh::LeanObject,
    mut v_a_4135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_4136_: u32 = 0;
    let mut v_res_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_4136_ = crate::leanh::lean_unbox_uint32(v_n_4134_);
    crate::leanh::lean_dec(v_n_4134_);
    v_res_4137_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(
            v_times_4133_,
            v_n_boxed_4136_,
            v_a_4135_,
        );
    crate::leanh::lean_dec_ref(v_times_4133_);
    return v_res_4137_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0(
    mut v_upperBound_4138_: *mut crate::leanh::LeanObject,
    mut v_res_4139_: *mut crate::leanh::LeanObject,
    mut v_inst_4140_: *mut crate::leanh::LeanObject,
    mut v_R_4141_: *mut crate::leanh::LeanObject,
    mut v_a_4142_: *mut crate::leanh::LeanObject,
    mut v_b_4143_: *mut crate::leanh::LeanObject,
    mut v_c_4144_: *mut crate::leanh::LeanObject,
    mut v___y_4145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4146_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(v_upperBound_4138_, v_res_4139_, v_a_4142_, v_b_4143_, v___y_4145_);
    return v___x_4146_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___boxed(
    mut v_upperBound_4147_: *mut crate::leanh::LeanObject,
    mut v_res_4148_: *mut crate::leanh::LeanObject,
    mut v_inst_4149_: *mut crate::leanh::LeanObject,
    mut v_R_4150_: *mut crate::leanh::LeanObject,
    mut v_a_4151_: *mut crate::leanh::LeanObject,
    mut v_b_4152_: *mut crate::leanh::LeanObject,
    mut v_c_4153_: *mut crate::leanh::LeanObject,
    mut v___y_4154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4155_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0(v_upperBound_4147_, v_res_4148_, v_inst_4149_, v_R_4150_, v_a_4151_, v_b_4152_, v_c_4153_, v___y_4154_);
    crate::leanh::lean_dec_ref(v_res_4148_);
    crate::leanh::lean_dec(v_upperBound_4147_);
    return v_res_4155_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(
    mut v_size_4156_: *mut crate::leanh::LeanObject,
    mut v_n_4157_: u32,
    mut v_a_4158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4159_ = lean_uint32_to_nat(v_n_4157_);
    v___x_4160_ = crate::leanh::lean_alloc_closure(
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSecond
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_4160_, 0, v_size_4156_);
    v___x_4161_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(
        v___x_4159_,
        v___x_4160_,
        v_a_4158_,
    );
    crate::leanh::lean_dec(v___x_4159_);
    return v___x_4161_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds___boxed(
    mut v_size_4162_: *mut crate::leanh::LeanObject,
    mut v_n_4163_: *mut crate::leanh::LeanObject,
    mut v_a_4164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_4165_: u32 = 0;
    let mut v_res_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_4165_ = crate::leanh::lean_unbox_uint32(v_n_4163_);
    crate::leanh::lean_dec(v_n_4163_);
    v_res_4166_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(
            v_size_4162_,
            v_n_boxed_4165_,
            v_a_4164_,
        );
    return v_res_4166_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(
    mut v_n_4167_: u32,
    mut v_a_4168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4169_ = lean_uint32_to_nat(v_n_4167_);
    v___x_4170_ = crate::leanh::lean_alloc_closure(
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pbool
            as *mut core::ffi::c_void,
        1,
        0,
    );
    v___x_4171_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(
        v___x_4169_,
        v___x_4170_,
        v_a_4168_,
    );
    crate::leanh::lean_dec(v___x_4169_);
    return v___x_4171_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators___boxed(
    mut v_n_4172_: *mut crate::leanh::LeanObject,
    mut v_a_4173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_4174_: u32 = 0;
    let mut v_res_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_4174_ = crate::leanh::lean_unbox_uint32(v_n_4172_);
    crate::leanh::lean_dec(v_n_4172_);
    v_res_4175_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(
            v_n_boxed_4174_,
            v_a_4173_,
        );
    return v_res_4175_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV1(
    mut v_a_4176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isutcnt_4180_: u32 = 0;
    let mut v_isstdcnt_4181_: u32 = 0;
    let mut v_leapcnt_4182_: u32 = 0;
    let mut v_timecnt_4183_: u32 = 0;
    let mut v_typecnt_4184_: u32 = 0;
    let mut v_charcnt_4185_: u32 = 0;
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4210_: u8 = 0;
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4215_: u8 = 0;
    let mut v_pos_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4220_: u8 = 0;
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4224_: u8 = 0;
    let mut v_pos_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4229_: u8 = 0;
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4233_: u8 = 0;
    let mut v_pos_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4238_: u8 = 0;
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4242_: u8 = 0;
    let mut v_pos_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4247_: u8 = 0;
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4251_: u8 = 0;
    let mut v_pos_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4256_: u8 = 0;
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4260_: u8 = 0;
    let mut v_pos_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4265_: u8 = 0;
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4269_: u8 = 0;
    let mut v_pos_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4274_: u8 = 0;
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4278_: u8 = 0;
    let mut v_pos_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4283_: u8 = 0;
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4287_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4177_ =
                    l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader(
                        v_a_4176_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4177_) == 0 {
                    v_res_4178_ = crate::leanh::lean_ctor_get(v___x_4177_, 1);
                    crate::leanh::lean_inc(v_res_4178_);
                    v_pos_4179_ = crate::leanh::lean_ctor_get(v___x_4177_, 0);
                    crate::leanh::lean_inc(v_pos_4179_);
                    crate::leanh::lean_dec_ref_known(v___x_4177_, 2);
                    v_isutcnt_4180_ = crate::leanh::lean_ctor_get_uint32(v_res_4178_, 0 as u32);
                    v_isstdcnt_4181_ = crate::leanh::lean_ctor_get_uint32(v_res_4178_, 4 as u32);
                    v_leapcnt_4182_ = crate::leanh::lean_ctor_get_uint32(v_res_4178_, 8 as u32);
                    v_timecnt_4183_ = crate::leanh::lean_ctor_get_uint32(v_res_4178_, 12 as u32);
                    v_typecnt_4184_ = crate::leanh::lean_ctor_get_uint32(v_res_4178_, 16 as u32);
                    v_charcnt_4185_ = crate::leanh::lean_ctor_get_uint32(v_res_4178_, 20 as u32);
                    v___x_4186_ = crate::leanh::lean_alloc_closure(
                        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi32
                            as *mut core::ffi::c_void,
                        1,
                        0,
                    );
                    crate::leanh::lean_inc_ref(v___x_4186_);
                    v___x_4187_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes(v___x_4186_, v_timecnt_4183_, v_pos_4179_);
                    if crate::leanh::lean_obj_tag(v___x_4187_) == 0 {
                        v_pos_4188_ = crate::leanh::lean_ctor_get(v___x_4187_, 0);
                        crate::leanh::lean_inc(v_pos_4188_);
                        v_res_4189_ = crate::leanh::lean_ctor_get(v___x_4187_, 1);
                        crate::leanh::lean_inc(v_res_4189_);
                        crate::leanh::lean_dec_ref_known(v___x_4187_, 2);
                        v___x_4190_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(v_timecnt_4183_, v_pos_4188_);
                        if crate::leanh::lean_obj_tag(v___x_4190_) == 0 {
                            v_pos_4191_ = crate::leanh::lean_ctor_get(v___x_4190_, 0);
                            crate::leanh::lean_inc(v_pos_4191_);
                            v_res_4192_ = crate::leanh::lean_ctor_get(v___x_4190_, 1);
                            crate::leanh::lean_inc(v_res_4192_);
                            crate::leanh::lean_dec_ref_known(v___x_4190_, 2);
                            v___x_4193_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(v_typecnt_4184_, v_pos_4191_);
                            if crate::leanh::lean_obj_tag(v___x_4193_) == 0 {
                                v_pos_4194_ = crate::leanh::lean_ctor_get(v___x_4193_, 0);
                                crate::leanh::lean_inc(v_pos_4194_);
                                v_res_4195_ = crate::leanh::lean_ctor_get(v___x_4193_, 1);
                                crate::leanh::lean_inc(v_res_4195_);
                                crate::leanh::lean_dec_ref_known(v___x_4193_, 2);
                                v___x_4196_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(v_res_4195_, v_charcnt_4185_, v_pos_4194_);
                                if crate::leanh::lean_obj_tag(v___x_4196_) == 0 {
                                    v_pos_4197_ = crate::leanh::lean_ctor_get(v___x_4196_, 0);
                                    crate::leanh::lean_inc(v_pos_4197_);
                                    v_res_4198_ = crate::leanh::lean_ctor_get(v___x_4196_, 1);
                                    crate::leanh::lean_inc(v_res_4198_);
                                    crate::leanh::lean_dec_ref_known(v___x_4196_, 2);
                                    v___x_4199_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(v___x_4186_, v_leapcnt_4182_, v_pos_4197_);
                                    if crate::leanh::lean_obj_tag(v___x_4199_) == 0 {
                                        v_pos_4200_ = crate::leanh::lean_ctor_get(v___x_4199_, 0);
                                        crate::leanh::lean_inc(v_pos_4200_);
                                        v_res_4201_ = crate::leanh::lean_ctor_get(v___x_4199_, 1);
                                        crate::leanh::lean_inc(v_res_4201_);
                                        crate::leanh::lean_dec_ref_known(v___x_4199_, 2);
                                        v___x_4202_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_isstdcnt_4181_, v_pos_4200_);
                                        if crate::leanh::lean_obj_tag(v___x_4202_) == 0 {
                                            v_pos_4203_ =
                                                crate::leanh::lean_ctor_get(v___x_4202_, 0);
                                            crate::leanh::lean_inc(v_pos_4203_);
                                            v_res_4204_ =
                                                crate::leanh::lean_ctor_get(v___x_4202_, 1);
                                            crate::leanh::lean_inc(v_res_4204_);
                                            crate::leanh::lean_dec_ref_known(v___x_4202_, 2);
                                            v___x_4205_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_isutcnt_4180_, v_pos_4203_);
                                            if crate::leanh::lean_obj_tag(v___x_4205_) == 0 {
                                                v_pos_4206_ =
                                                    crate::leanh::lean_ctor_get(v___x_4205_, 0);
                                                v_res_4207_ =
                                                    crate::leanh::lean_ctor_get(v___x_4205_, 1);
                                                v_isSharedCheck_4215_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_4205_))
                                                        as u8;
                                                if v_isSharedCheck_4215_ == 0 {
                                                    v___x_4209_ = v___x_4205_;
                                                    v_isShared_4210_ = v_isSharedCheck_4215_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_res_4207_);
                                                    crate::leanh::lean_inc(v_pos_4206_);
                                                    crate::leanh::lean_dec(v___x_4205_);
                                                    v___x_4209_ = crate::leanh::lean_box(0);
                                                    v_isShared_4210_ = v_isSharedCheck_4215_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_res_4204_);
                                                crate::leanh::lean_dec(v_res_4201_);
                                                crate::leanh::lean_dec(v_res_4198_);
                                                crate::leanh::lean_dec(v_res_4195_);
                                                crate::leanh::lean_dec(v_res_4192_);
                                                crate::leanh::lean_dec(v_res_4189_);
                                                crate::leanh::lean_dec(v_res_4178_);
                                                v_pos_4216_ =
                                                    crate::leanh::lean_ctor_get(v___x_4205_, 0);
                                                v_err_4217_ =
                                                    crate::leanh::lean_ctor_get(v___x_4205_, 1);
                                                v_isSharedCheck_4224_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_4205_))
                                                        as u8;
                                                if v_isSharedCheck_4224_ == 0 {
                                                    v___x_4219_ = v___x_4205_;
                                                    v_isShared_4220_ = v_isSharedCheck_4224_;
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_err_4217_);
                                                    crate::leanh::lean_inc(v_pos_4216_);
                                                    crate::leanh::lean_dec(v___x_4205_);
                                                    v___x_4219_ = crate::leanh::lean_box(0);
                                                    v_isShared_4220_ = v_isSharedCheck_4224_;
                                                    state = 3;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_res_4201_);
                                            crate::leanh::lean_dec(v_res_4198_);
                                            crate::leanh::lean_dec(v_res_4195_);
                                            crate::leanh::lean_dec(v_res_4192_);
                                            crate::leanh::lean_dec(v_res_4189_);
                                            crate::leanh::lean_dec(v_res_4178_);
                                            v_pos_4225_ =
                                                crate::leanh::lean_ctor_get(v___x_4202_, 0);
                                            v_err_4226_ =
                                                crate::leanh::lean_ctor_get(v___x_4202_, 1);
                                            v_isSharedCheck_4233_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_4202_))
                                                    as u8;
                                            if v_isSharedCheck_4233_ == 0 {
                                                v___x_4228_ = v___x_4202_;
                                                v_isShared_4229_ = v_isSharedCheck_4233_;
                                                state = 5;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_err_4226_);
                                                crate::leanh::lean_inc(v_pos_4225_);
                                                crate::leanh::lean_dec(v___x_4202_);
                                                v___x_4228_ = crate::leanh::lean_box(0);
                                                v_isShared_4229_ = v_isSharedCheck_4233_;
                                                state = 5;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_res_4198_);
                                        crate::leanh::lean_dec(v_res_4195_);
                                        crate::leanh::lean_dec(v_res_4192_);
                                        crate::leanh::lean_dec(v_res_4189_);
                                        crate::leanh::lean_dec(v_res_4178_);
                                        v_pos_4234_ = crate::leanh::lean_ctor_get(v___x_4199_, 0);
                                        v_err_4235_ = crate::leanh::lean_ctor_get(v___x_4199_, 1);
                                        v_isSharedCheck_4242_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4199_)) as u8;
                                        if v_isSharedCheck_4242_ == 0 {
                                            v___x_4237_ = v___x_4199_;
                                            v_isShared_4238_ = v_isSharedCheck_4242_;
                                            state = 7;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_err_4235_);
                                            crate::leanh::lean_inc(v_pos_4234_);
                                            crate::leanh::lean_dec(v___x_4199_);
                                            v___x_4237_ = crate::leanh::lean_box(0);
                                            v_isShared_4238_ = v_isSharedCheck_4242_;
                                            state = 7;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_res_4195_);
                                    crate::leanh::lean_dec(v_res_4192_);
                                    crate::leanh::lean_dec(v_res_4189_);
                                    crate::leanh::lean_dec_ref(v___x_4186_);
                                    crate::leanh::lean_dec(v_res_4178_);
                                    v_pos_4243_ = crate::leanh::lean_ctor_get(v___x_4196_, 0);
                                    v_err_4244_ = crate::leanh::lean_ctor_get(v___x_4196_, 1);
                                    v_isSharedCheck_4251_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4196_)) as u8;
                                    if v_isSharedCheck_4251_ == 0 {
                                        v___x_4246_ = v___x_4196_;
                                        v_isShared_4247_ = v_isSharedCheck_4251_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_err_4244_);
                                        crate::leanh::lean_inc(v_pos_4243_);
                                        crate::leanh::lean_dec(v___x_4196_);
                                        v___x_4246_ = crate::leanh::lean_box(0);
                                        v_isShared_4247_ = v_isSharedCheck_4251_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_res_4192_);
                                crate::leanh::lean_dec(v_res_4189_);
                                crate::leanh::lean_dec_ref(v___x_4186_);
                                crate::leanh::lean_dec(v_res_4178_);
                                v_pos_4252_ = crate::leanh::lean_ctor_get(v___x_4193_, 0);
                                v_err_4253_ = crate::leanh::lean_ctor_get(v___x_4193_, 1);
                                v_isSharedCheck_4260_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4193_)) as u8;
                                if v_isSharedCheck_4260_ == 0 {
                                    v___x_4255_ = v___x_4193_;
                                    v_isShared_4256_ = v_isSharedCheck_4260_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_err_4253_);
                                    crate::leanh::lean_inc(v_pos_4252_);
                                    crate::leanh::lean_dec(v___x_4193_);
                                    v___x_4255_ = crate::leanh::lean_box(0);
                                    v_isShared_4256_ = v_isSharedCheck_4260_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_res_4189_);
                            crate::leanh::lean_dec_ref(v___x_4186_);
                            crate::leanh::lean_dec(v_res_4178_);
                            v_pos_4261_ = crate::leanh::lean_ctor_get(v___x_4190_, 0);
                            v_err_4262_ = crate::leanh::lean_ctor_get(v___x_4190_, 1);
                            v_isSharedCheck_4269_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4190_)) as u8;
                            if v_isSharedCheck_4269_ == 0 {
                                v___x_4264_ = v___x_4190_;
                                v_isShared_4265_ = v_isSharedCheck_4269_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_err_4262_);
                                crate::leanh::lean_inc(v_pos_4261_);
                                crate::leanh::lean_dec(v___x_4190_);
                                v___x_4264_ = crate::leanh::lean_box(0);
                                v_isShared_4265_ = v_isSharedCheck_4269_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_4186_);
                        crate::leanh::lean_dec(v_res_4178_);
                        v_pos_4270_ = crate::leanh::lean_ctor_get(v___x_4187_, 0);
                        v_err_4271_ = crate::leanh::lean_ctor_get(v___x_4187_, 1);
                        v_isSharedCheck_4278_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4187_)) as u8;
                        if v_isSharedCheck_4278_ == 0 {
                            v___x_4273_ = v___x_4187_;
                            v_isShared_4274_ = v_isSharedCheck_4278_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_err_4271_);
                            crate::leanh::lean_inc(v_pos_4270_);
                            crate::leanh::lean_dec(v___x_4187_);
                            v___x_4273_ = crate::leanh::lean_box(0);
                            v_isShared_4274_ = v_isSharedCheck_4278_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    v_pos_4279_ = crate::leanh::lean_ctor_get(v___x_4177_, 0);
                    v_err_4280_ = crate::leanh::lean_ctor_get(v___x_4177_, 1);
                    v_isSharedCheck_4287_ = (!crate::leanh::lean_is_exclusive(v___x_4177_)) as u8;
                    if v_isSharedCheck_4287_ == 0 {
                        v___x_4282_ = v___x_4177_;
                        v_isShared_4283_ = v_isSharedCheck_4287_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_4280_);
                        crate::leanh::lean_inc(v_pos_4279_);
                        crate::leanh::lean_dec(v___x_4177_);
                        v___x_4282_ = crate::leanh::lean_box(0);
                        v_isShared_4283_ = v_isSharedCheck_4287_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4211_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4211_, 0, v_res_4178_);
                crate::leanh::lean_ctor_set(v___x_4211_, 1, v_res_4189_);
                crate::leanh::lean_ctor_set(v___x_4211_, 2, v_res_4192_);
                crate::leanh::lean_ctor_set(v___x_4211_, 3, v_res_4195_);
                crate::leanh::lean_ctor_set(v___x_4211_, 4, v_res_4198_);
                crate::leanh::lean_ctor_set(v___x_4211_, 5, v_res_4201_);
                crate::leanh::lean_ctor_set(v___x_4211_, 6, v_res_4204_);
                crate::leanh::lean_ctor_set(v___x_4211_, 7, v_res_4207_);
                if v_isShared_4210_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4209_, 1, v___x_4211_);
                    v___x_4213_ = v___x_4209_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4214_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_pos_4206_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4214_, 1, v___x_4211_);
                    v___x_4213_ = v_reuseFailAlloc_4214_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4213_;
            }
            3 => {
                if v_isShared_4220_ == 0 {
                    v___x_4222_ = v___x_4219_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4223_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_pos_4216_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4223_, 1, v_err_4217_);
                    v___x_4222_ = v_reuseFailAlloc_4223_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4222_;
            }
            5 => {
                if v_isShared_4229_ == 0 {
                    v___x_4231_ = v___x_4228_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4232_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_pos_4225_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4232_, 1, v_err_4226_);
                    v___x_4231_ = v_reuseFailAlloc_4232_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4231_;
            }
            7 => {
                if v_isShared_4238_ == 0 {
                    v___x_4240_ = v___x_4237_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4241_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_pos_4234_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4241_, 1, v_err_4235_);
                    v___x_4240_ = v_reuseFailAlloc_4241_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4240_;
            }
            9 => {
                if v_isShared_4247_ == 0 {
                    v___x_4249_ = v___x_4246_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4250_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_pos_4243_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4250_, 1, v_err_4244_);
                    v___x_4249_ = v_reuseFailAlloc_4250_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4249_;
            }
            11 => {
                if v_isShared_4256_ == 0 {
                    v___x_4258_ = v___x_4255_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4259_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_pos_4252_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4259_, 1, v_err_4253_);
                    v___x_4258_ = v_reuseFailAlloc_4259_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4258_;
            }
            13 => {
                if v_isShared_4265_ == 0 {
                    v___x_4267_ = v___x_4264_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4268_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4268_, 0, v_pos_4261_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4268_, 1, v_err_4262_);
                    v___x_4267_ = v_reuseFailAlloc_4268_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4267_;
            }
            15 => {
                if v_isShared_4274_ == 0 {
                    v___x_4276_ = v___x_4273_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4277_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_pos_4270_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4277_, 1, v_err_4271_);
                    v___x_4276_ = v_reuseFailAlloc_4277_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4276_;
            }
            17 => {
                if v_isShared_4283_ == 0 {
                    v___x_4285_ = v___x_4282_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4286_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_pos_4279_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4286_, 1, v_err_4280_);
                    v___x_4285_ = v_reuseFailAlloc_4286_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1(
    mut v_as_4288_: *mut crate::leanh::LeanObject,
    mut v_sz_4289_: usize,
    mut v_i_4290_: usize,
    mut v_b_4291_: *mut crate::leanh::LeanObject,
    mut v___y_4292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4293_: u8 = 0;
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: u8 = 0;
    let mut v___x_4297_: u32 = 0;
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: usize = 0;
    let mut v___x_4300_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4293_ = lean_usize_dec_lt(v_i_4290_, v_sz_4289_);
                if v___x_4293_ == 0 {
                    v___x_4294_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4294_, 0, v___y_4292_);
                    crate::leanh::lean_ctor_set(v___x_4294_, 1, v_b_4291_);
                    return v___x_4294_;
                } else {
                    v_a_4295_ = lean_array_uget_borrowed(v_as_4288_, v_i_4290_);
                    v___x_4296_ = (crate::leanh::lean_unbox(v_a_4295_) as u8);
                    v___x_4297_ = lean_uint8_to_uint32(v___x_4296_);
                    v___x_4298_ = lean_string_push(v_b_4291_, v___x_4297_);
                    v___x_4299_ = 1usize;
                    v___x_4300_ = lean_usize_add(v_i_4290_, v___x_4299_);
                    v_i_4290_ = v___x_4300_;
                    v_b_4291_ = v___x_4298_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1___boxed(
    mut v_as_4302_: *mut crate::leanh::LeanObject,
    mut v_sz_4303_: *mut crate::leanh::LeanObject,
    mut v_i_4304_: *mut crate::leanh::LeanObject,
    mut v_b_4305_: *mut crate::leanh::LeanObject,
    mut v___y_4306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4307_: usize = 0;
    let mut v_i_boxed_4308_: usize = 0;
    let mut v_res_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4307_ = crate::leanh::lean_unbox_usize(v_sz_4303_);
    crate::leanh::lean_dec(v_sz_4303_);
    v_i_boxed_4308_ = crate::leanh::lean_unbox_usize(v_i_4304_);
    crate::leanh::lean_dec(v_i_4304_);
    v_res_4309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1(v_as_4302_, v_sz_boxed_4307_, v_i_boxed_4308_, v_b_4305_, v___y_4306_);
    crate::leanh::lean_dec_ref(v_as_4302_);
    return v_res_4309_;
}
pub unsafe fn l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0(
    mut v_acc_4313_: *mut crate::leanh::LeanObject,
    mut v_a_4314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: u8 = 0;
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: u8 = 0;
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: u8 = 0;
    let mut v_c_4330_: u8 = 0;
    let mut v___x_4331_: u8 = 0;
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4334_: u8 = 0;
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_x27_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4343_: u8 = 0;
    let mut v_unused_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4315_ = crate::leanh::lean_ctor_get(v_a_4314_, 0);
                v_idx_4316_ = crate::leanh::lean_ctor_get(v_a_4314_, 1);
                crate::leanh::lean_inc(v_idx_4316_);
                v___x_4326_ = lean_byte_array_size(v_array_4315_);
                v___x_4327_ = lean_nat_dec_lt(v_idx_4316_, v___x_4326_);
                if v___x_4327_ == 0 {
                    v___x_4328_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_idx_4316_);
                    v_pos_4318_ = v_a_4314_;
                    v_idx_4319_ = v_idx_4316_;
                    v_err_4320_ = v___x_4328_;
                    state = 1;
                    continue;
                } else {
                    v___x_4329_ = 10;
                    v_c_4330_ = lean_byte_array_fget(v_array_4315_, v_idx_4316_);
                    v___x_4331_ = lean_uint8_dec_eq(v_c_4330_, v___x_4329_);
                    if v___x_4331_ == 0 {
                        if v___x_4327_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc_ref(v_array_4315_);
                            v_isSharedCheck_4343_ =
                                (!crate::leanh::lean_is_exclusive(v_a_4314_)) as u8;
                            if v_isSharedCheck_4343_ == 0 {
                                v_unused_4344_ = crate::leanh::lean_ctor_get(v_a_4314_, 1);
                                crate::leanh::lean_dec(v_unused_4344_);
                                v_unused_4345_ = crate::leanh::lean_ctor_get(v_a_4314_, 0);
                                crate::leanh::lean_dec(v_unused_4345_);
                                v___x_4333_ = v_a_4314_;
                                v_isShared_4334_ = v_isSharedCheck_4343_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_4314_);
                                v___x_4333_ = crate::leanh::lean_box(0);
                                v_isShared_4334_ = v_isSharedCheck_4343_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4321_ = lean_nat_dec_eq(v_idx_4316_, v_idx_4319_);
                crate::leanh::lean_dec(v_idx_4319_);
                crate::leanh::lean_dec(v_idx_4316_);
                if v___x_4321_ == 0 {
                    crate::leanh::lean_dec_ref(v_acc_4313_);
                    crate::leanh::lean_inc(v_err_4320_);
                    v___x_4322_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4322_, 0, v_pos_4318_);
                    crate::leanh::lean_ctor_set(v___x_4322_, 1, v_err_4320_);
                    return v___x_4322_;
                } else {
                    v___x_4323_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4323_, 0, v_pos_4318_);
                    crate::leanh::lean_ctor_set(v___x_4323_, 1, v_acc_4313_);
                    return v___x_4323_;
                }
            }
            2 => {
                v___x_4325_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__1;
                crate::leanh::lean_inc(v_idx_4316_);
                v_pos_4318_ = v_a_4314_;
                v_idx_4319_ = v_idx_4316_;
                v_err_4320_ = v___x_4325_;
                state = 1;
                continue;
            }
            3 => {
                v___x_4335_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4336_ = lean_nat_add(v_idx_4316_, v___x_4335_);
                crate::leanh::lean_dec(v_idx_4316_);
                if v_isShared_4334_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4333_, 1, v___x_4336_);
                    v_it_x27_4338_ = v___x_4333_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4342_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_array_4315_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4342_, 1, v___x_4336_);
                    v_it_x27_4338_ = v_reuseFailAlloc_4342_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4339_ = crate::leanh::lean_box((v_c_4330_) as usize);
                v___x_4340_ = lean_array_push(v_acc_4313_, v___x_4339_);
                v_acc_4313_ = v___x_4340_;
                v_a_4314_ = v_it_x27_4338_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter(
    mut v_a_4348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4354_: u8 = 0;
    let mut v___x_4355_: u8 = 0;
    let mut v___x_4356_: u8 = 0;
    let mut v___x_4357_: u8 = 0;
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4367_: usize = 0;
    let mut v___x_4368_: usize = 0;
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4374_: u8 = 0;
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4379_: u8 = 0;
    let mut v_pos_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4384_: u8 = 0;
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4388_: u8 = 0;
    let mut v_pos_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4393_: u8 = 0;
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4397_: u8 = 0;
    let mut v_isSharedCheck_4398_: u8 = 0;
    let mut v_pos_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4402_: u8 = 0;
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4407_: u8 = 0;
    let mut v_unused_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4349_ =
                    l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(
                        v_a_4348_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4349_) == 0 {
                    v_pos_4350_ = crate::leanh::lean_ctor_get(v___x_4349_, 0);
                    v_res_4351_ = crate::leanh::lean_ctor_get(v___x_4349_, 1);
                    v_isSharedCheck_4398_ = (!crate::leanh::lean_is_exclusive(v___x_4349_)) as u8;
                    if v_isSharedCheck_4398_ == 0 {
                        v___x_4353_ = v___x_4349_;
                        v_isShared_4354_ = v_isSharedCheck_4398_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_res_4351_);
                        crate::leanh::lean_inc(v_pos_4350_);
                        crate::leanh::lean_dec(v___x_4349_);
                        v___x_4353_ = crate::leanh::lean_box(0);
                        v_isShared_4354_ = v_isSharedCheck_4398_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_4399_ = crate::leanh::lean_ctor_get(v___x_4349_, 0);
                    v_isSharedCheck_4407_ = (!crate::leanh::lean_is_exclusive(v___x_4349_)) as u8;
                    if v_isSharedCheck_4407_ == 0 {
                        v_unused_4408_ = crate::leanh::lean_ctor_get(v___x_4349_, 1);
                        crate::leanh::lean_dec(v_unused_4408_);
                        v___x_4401_ = v___x_4349_;
                        v_isShared_4402_ = v_isSharedCheck_4407_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_pos_4399_);
                        crate::leanh::lean_dec(v___x_4349_);
                        v___x_4401_ = crate::leanh::lean_box(0);
                        v_isShared_4402_ = v_isSharedCheck_4407_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4355_ = 10;
                v___x_4356_ = (crate::leanh::lean_unbox(v_res_4351_) as u8);
                crate::leanh::lean_dec(v_res_4351_);
                v___x_4357_ = lean_uint8_dec_eq(v___x_4356_, v___x_4355_);
                if v___x_4357_ == 0 {
                    v___x_4358_ = crate::leanh::lean_box(0);
                    if v_isShared_4354_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4353_, 1, v___x_4358_);
                        v___x_4360_ = v___x_4353_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4361_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_pos_4350_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4361_, 1, v___x_4358_);
                        v___x_4360_ = v_reuseFailAlloc_4361_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4353_);
                    v___x_4362_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter___closed__0;
                    v___x_4363_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0(v___x_4362_, v_pos_4350_);
                    if crate::leanh::lean_obj_tag(v___x_4363_) == 0 {
                        v_pos_4364_ = crate::leanh::lean_ctor_get(v___x_4363_, 0);
                        crate::leanh::lean_inc(v_pos_4364_);
                        v_res_4365_ = crate::leanh::lean_ctor_get(v___x_4363_, 1);
                        crate::leanh::lean_inc(v_res_4365_);
                        crate::leanh::lean_dec_ref_known(v___x_4363_, 2);
                        v___x_4366_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0;
                        v_sz_4367_ = lean_array_size(v_res_4365_);
                        v___x_4368_ = 0usize;
                        v___x_4369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1(v_res_4365_, v_sz_4367_, v___x_4368_, v___x_4366_, v_pos_4364_);
                        crate::leanh::lean_dec(v_res_4365_);
                        if crate::leanh::lean_obj_tag(v___x_4369_) == 0 {
                            v_pos_4370_ = crate::leanh::lean_ctor_get(v___x_4369_, 0);
                            v_res_4371_ = crate::leanh::lean_ctor_get(v___x_4369_, 1);
                            v_isSharedCheck_4379_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4369_)) as u8;
                            if v_isSharedCheck_4379_ == 0 {
                                v___x_4373_ = v___x_4369_;
                                v_isShared_4374_ = v_isSharedCheck_4379_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_res_4371_);
                                crate::leanh::lean_inc(v_pos_4370_);
                                crate::leanh::lean_dec(v___x_4369_);
                                v___x_4373_ = crate::leanh::lean_box(0);
                                v_isShared_4374_ = v_isSharedCheck_4379_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_pos_4380_ = crate::leanh::lean_ctor_get(v___x_4369_, 0);
                            v_err_4381_ = crate::leanh::lean_ctor_get(v___x_4369_, 1);
                            v_isSharedCheck_4388_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4369_)) as u8;
                            if v_isSharedCheck_4388_ == 0 {
                                v___x_4383_ = v___x_4369_;
                                v_isShared_4384_ = v_isSharedCheck_4388_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_err_4381_);
                                crate::leanh::lean_inc(v_pos_4380_);
                                crate::leanh::lean_dec(v___x_4369_);
                                v___x_4383_ = crate::leanh::lean_box(0);
                                v_isShared_4384_ = v_isSharedCheck_4388_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v_pos_4389_ = crate::leanh::lean_ctor_get(v___x_4363_, 0);
                        v_err_4390_ = crate::leanh::lean_ctor_get(v___x_4363_, 1);
                        v_isSharedCheck_4397_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4363_)) as u8;
                        if v_isSharedCheck_4397_ == 0 {
                            v___x_4392_ = v___x_4363_;
                            v_isShared_4393_ = v_isSharedCheck_4397_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_err_4390_);
                            crate::leanh::lean_inc(v_pos_4389_);
                            crate::leanh::lean_dec(v___x_4363_);
                            v___x_4392_ = crate::leanh::lean_box(0);
                            v_isShared_4393_ = v_isSharedCheck_4397_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4360_;
            }
            3 => {
                v___x_4375_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4375_, 0, v_res_4371_);
                if v_isShared_4374_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4373_, 1, v___x_4375_);
                    v___x_4377_ = v___x_4373_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4378_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_pos_4370_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4378_, 1, v___x_4375_);
                    v___x_4377_ = v_reuseFailAlloc_4378_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4377_;
            }
            5 => {
                if v_isShared_4384_ == 0 {
                    v___x_4386_ = v___x_4383_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4387_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_pos_4380_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4387_, 1, v_err_4381_);
                    v___x_4386_ = v_reuseFailAlloc_4387_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4386_;
            }
            7 => {
                if v_isShared_4393_ == 0 {
                    v___x_4395_ = v___x_4392_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4396_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_pos_4389_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4396_, 1, v_err_4390_);
                    v___x_4395_ = v_reuseFailAlloc_4396_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4395_;
            }
            9 => {
                v___x_4403_ = crate::leanh::lean_box(0);
                if v_isShared_4402_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4401_, 1, v___x_4403_);
                    v___x_4405_ = v___x_4401_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4406_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_pos_4399_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4406_, 1, v___x_4403_);
                    v___x_4405_ = v_reuseFailAlloc_4406_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4405_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV2(
    mut v_a_4409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4416_: u8 = 0;
    let mut v_idx_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: u8 = 0;
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4426_: u8 = 0;
    let mut v_unused_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isutcnt_4431_: u32 = 0;
    let mut v_isstdcnt_4432_: u32 = 0;
    let mut v_leapcnt_4433_: u32 = 0;
    let mut v_timecnt_4434_: u32 = 0;
    let mut v_typecnt_4435_: u32 = 0;
    let mut v_charcnt_4436_: u32 = 0;
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4461_: u8 = 0;
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4467_: u8 = 0;
    let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4476_: u8 = 0;
    let mut v_pos_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4479_: u8 = 0;
    let mut v_pos_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_a_4409_);
                v___x_4428_ =
                    l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader(
                        v_a_4409_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4428_) == 0 {
                    v_res_4429_ = crate::leanh::lean_ctor_get(v___x_4428_, 1);
                    crate::leanh::lean_inc(v_res_4429_);
                    v_pos_4430_ = crate::leanh::lean_ctor_get(v___x_4428_, 0);
                    crate::leanh::lean_inc(v_pos_4430_);
                    crate::leanh::lean_dec_ref_known(v___x_4428_, 2);
                    v_isutcnt_4431_ = crate::leanh::lean_ctor_get_uint32(v_res_4429_, 0 as u32);
                    v_isstdcnt_4432_ = crate::leanh::lean_ctor_get_uint32(v_res_4429_, 4 as u32);
                    v_leapcnt_4433_ = crate::leanh::lean_ctor_get_uint32(v_res_4429_, 8 as u32);
                    v_timecnt_4434_ = crate::leanh::lean_ctor_get_uint32(v_res_4429_, 12 as u32);
                    v_typecnt_4435_ = crate::leanh::lean_ctor_get_uint32(v_res_4429_, 16 as u32);
                    v_charcnt_4436_ = crate::leanh::lean_ctor_get_uint32(v_res_4429_, 20 as u32);
                    v___x_4437_ = crate::leanh::lean_alloc_closure(
                        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi64
                            as *mut core::ffi::c_void,
                        1,
                        0,
                    );
                    crate::leanh::lean_inc_ref(v___x_4437_);
                    v___x_4438_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes(v___x_4437_, v_timecnt_4434_, v_pos_4430_);
                    if crate::leanh::lean_obj_tag(v___x_4438_) == 0 {
                        v_pos_4439_ = crate::leanh::lean_ctor_get(v___x_4438_, 0);
                        crate::leanh::lean_inc(v_pos_4439_);
                        v_res_4440_ = crate::leanh::lean_ctor_get(v___x_4438_, 1);
                        crate::leanh::lean_inc(v_res_4440_);
                        crate::leanh::lean_dec_ref_known(v___x_4438_, 2);
                        v___x_4441_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(v_timecnt_4434_, v_pos_4439_);
                        if crate::leanh::lean_obj_tag(v___x_4441_) == 0 {
                            v_pos_4442_ = crate::leanh::lean_ctor_get(v___x_4441_, 0);
                            crate::leanh::lean_inc(v_pos_4442_);
                            v_res_4443_ = crate::leanh::lean_ctor_get(v___x_4441_, 1);
                            crate::leanh::lean_inc(v_res_4443_);
                            crate::leanh::lean_dec_ref_known(v___x_4441_, 2);
                            v___x_4444_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(v_typecnt_4435_, v_pos_4442_);
                            if crate::leanh::lean_obj_tag(v___x_4444_) == 0 {
                                v_pos_4445_ = crate::leanh::lean_ctor_get(v___x_4444_, 0);
                                crate::leanh::lean_inc(v_pos_4445_);
                                v_res_4446_ = crate::leanh::lean_ctor_get(v___x_4444_, 1);
                                crate::leanh::lean_inc(v_res_4446_);
                                crate::leanh::lean_dec_ref_known(v___x_4444_, 2);
                                v___x_4447_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(v_res_4446_, v_charcnt_4436_, v_pos_4445_);
                                if crate::leanh::lean_obj_tag(v___x_4447_) == 0 {
                                    v_pos_4448_ = crate::leanh::lean_ctor_get(v___x_4447_, 0);
                                    crate::leanh::lean_inc(v_pos_4448_);
                                    v_res_4449_ = crate::leanh::lean_ctor_get(v___x_4447_, 1);
                                    crate::leanh::lean_inc(v_res_4449_);
                                    crate::leanh::lean_dec_ref_known(v___x_4447_, 2);
                                    v___x_4450_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(v___x_4437_, v_leapcnt_4433_, v_pos_4448_);
                                    if crate::leanh::lean_obj_tag(v___x_4450_) == 0 {
                                        v_pos_4451_ = crate::leanh::lean_ctor_get(v___x_4450_, 0);
                                        crate::leanh::lean_inc(v_pos_4451_);
                                        v_res_4452_ = crate::leanh::lean_ctor_get(v___x_4450_, 1);
                                        crate::leanh::lean_inc(v_res_4452_);
                                        crate::leanh::lean_dec_ref_known(v___x_4450_, 2);
                                        v___x_4453_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_isstdcnt_4432_, v_pos_4451_);
                                        if crate::leanh::lean_obj_tag(v___x_4453_) == 0 {
                                            v_pos_4454_ =
                                                crate::leanh::lean_ctor_get(v___x_4453_, 0);
                                            crate::leanh::lean_inc(v_pos_4454_);
                                            v_res_4455_ =
                                                crate::leanh::lean_ctor_get(v___x_4453_, 1);
                                            crate::leanh::lean_inc(v_res_4455_);
                                            crate::leanh::lean_dec_ref_known(v___x_4453_, 2);
                                            v___x_4456_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_isutcnt_4431_, v_pos_4454_);
                                            if crate::leanh::lean_obj_tag(v___x_4456_) == 0 {
                                                v_pos_4457_ =
                                                    crate::leanh::lean_ctor_get(v___x_4456_, 0);
                                                v_res_4458_ =
                                                    crate::leanh::lean_ctor_get(v___x_4456_, 1);
                                                v_isSharedCheck_4479_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_4456_))
                                                        as u8;
                                                if v_isSharedCheck_4479_ == 0 {
                                                    v___x_4460_ = v___x_4456_;
                                                    v_isShared_4461_ = v_isSharedCheck_4479_;
                                                    state = 5;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_res_4458_);
                                                    crate::leanh::lean_inc(v_pos_4457_);
                                                    crate::leanh::lean_dec(v___x_4456_);
                                                    v___x_4460_ = crate::leanh::lean_box(0);
                                                    v_isShared_4461_ = v_isSharedCheck_4479_;
                                                    state = 5;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_res_4455_);
                                                crate::leanh::lean_dec(v_res_4452_);
                                                crate::leanh::lean_dec(v_res_4449_);
                                                crate::leanh::lean_dec(v_res_4446_);
                                                crate::leanh::lean_dec(v_res_4443_);
                                                crate::leanh::lean_dec(v_res_4440_);
                                                crate::leanh::lean_dec(v_res_4429_);
                                                v_pos_4480_ =
                                                    crate::leanh::lean_ctor_get(v___x_4456_, 0);
                                                crate::leanh::lean_inc(v_pos_4480_);
                                                v_err_4481_ =
                                                    crate::leanh::lean_ctor_get(v___x_4456_, 1);
                                                crate::leanh::lean_inc(v_err_4481_);
                                                crate::leanh::lean_dec_ref_known(v___x_4456_, 2);
                                                v_pos_4411_ = v_pos_4480_;
                                                v_err_4412_ = v_err_4481_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_res_4452_);
                                            crate::leanh::lean_dec(v_res_4449_);
                                            crate::leanh::lean_dec(v_res_4446_);
                                            crate::leanh::lean_dec(v_res_4443_);
                                            crate::leanh::lean_dec(v_res_4440_);
                                            crate::leanh::lean_dec(v_res_4429_);
                                            v_pos_4482_ =
                                                crate::leanh::lean_ctor_get(v___x_4453_, 0);
                                            crate::leanh::lean_inc(v_pos_4482_);
                                            v_err_4483_ =
                                                crate::leanh::lean_ctor_get(v___x_4453_, 1);
                                            crate::leanh::lean_inc(v_err_4483_);
                                            crate::leanh::lean_dec_ref_known(v___x_4453_, 2);
                                            v_pos_4411_ = v_pos_4482_;
                                            v_err_4412_ = v_err_4483_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_res_4449_);
                                        crate::leanh::lean_dec(v_res_4446_);
                                        crate::leanh::lean_dec(v_res_4443_);
                                        crate::leanh::lean_dec(v_res_4440_);
                                        crate::leanh::lean_dec(v_res_4429_);
                                        v_pos_4484_ = crate::leanh::lean_ctor_get(v___x_4450_, 0);
                                        crate::leanh::lean_inc(v_pos_4484_);
                                        v_err_4485_ = crate::leanh::lean_ctor_get(v___x_4450_, 1);
                                        crate::leanh::lean_inc(v_err_4485_);
                                        crate::leanh::lean_dec_ref_known(v___x_4450_, 2);
                                        v_pos_4411_ = v_pos_4484_;
                                        v_err_4412_ = v_err_4485_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_res_4446_);
                                    crate::leanh::lean_dec(v_res_4443_);
                                    crate::leanh::lean_dec(v_res_4440_);
                                    crate::leanh::lean_dec_ref(v___x_4437_);
                                    crate::leanh::lean_dec(v_res_4429_);
                                    v_pos_4486_ = crate::leanh::lean_ctor_get(v___x_4447_, 0);
                                    crate::leanh::lean_inc(v_pos_4486_);
                                    v_err_4487_ = crate::leanh::lean_ctor_get(v___x_4447_, 1);
                                    crate::leanh::lean_inc(v_err_4487_);
                                    crate::leanh::lean_dec_ref_known(v___x_4447_, 2);
                                    v_pos_4411_ = v_pos_4486_;
                                    v_err_4412_ = v_err_4487_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_res_4443_);
                                crate::leanh::lean_dec(v_res_4440_);
                                crate::leanh::lean_dec_ref(v___x_4437_);
                                crate::leanh::lean_dec(v_res_4429_);
                                v_pos_4488_ = crate::leanh::lean_ctor_get(v___x_4444_, 0);
                                crate::leanh::lean_inc(v_pos_4488_);
                                v_err_4489_ = crate::leanh::lean_ctor_get(v___x_4444_, 1);
                                crate::leanh::lean_inc(v_err_4489_);
                                crate::leanh::lean_dec_ref_known(v___x_4444_, 2);
                                v_pos_4411_ = v_pos_4488_;
                                v_err_4412_ = v_err_4489_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_res_4440_);
                            crate::leanh::lean_dec_ref(v___x_4437_);
                            crate::leanh::lean_dec(v_res_4429_);
                            v_pos_4490_ = crate::leanh::lean_ctor_get(v___x_4441_, 0);
                            crate::leanh::lean_inc(v_pos_4490_);
                            v_err_4491_ = crate::leanh::lean_ctor_get(v___x_4441_, 1);
                            crate::leanh::lean_inc(v_err_4491_);
                            crate::leanh::lean_dec_ref_known(v___x_4441_, 2);
                            v_pos_4411_ = v_pos_4490_;
                            v_err_4412_ = v_err_4491_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_4437_);
                        crate::leanh::lean_dec(v_res_4429_);
                        v_pos_4492_ = crate::leanh::lean_ctor_get(v___x_4438_, 0);
                        crate::leanh::lean_inc(v_pos_4492_);
                        v_err_4493_ = crate::leanh::lean_ctor_get(v___x_4438_, 1);
                        crate::leanh::lean_inc(v_err_4493_);
                        crate::leanh::lean_dec_ref_known(v___x_4438_, 2);
                        v_pos_4411_ = v_pos_4492_;
                        v_err_4412_ = v_err_4493_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_4494_ = crate::leanh::lean_ctor_get(v___x_4428_, 0);
                    crate::leanh::lean_inc(v_pos_4494_);
                    v_err_4495_ = crate::leanh::lean_ctor_get(v___x_4428_, 1);
                    crate::leanh::lean_inc(v_err_4495_);
                    crate::leanh::lean_dec_ref_known(v___x_4428_, 2);
                    v_pos_4411_ = v_pos_4494_;
                    v_err_4412_ = v_err_4495_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_idx_4413_ = crate::leanh::lean_ctor_get(v_a_4409_, 1);
                v_isSharedCheck_4426_ = (!crate::leanh::lean_is_exclusive(v_a_4409_)) as u8;
                if v_isSharedCheck_4426_ == 0 {
                    v_unused_4427_ = crate::leanh::lean_ctor_get(v_a_4409_, 0);
                    crate::leanh::lean_dec(v_unused_4427_);
                    v___x_4415_ = v_a_4409_;
                    v_isShared_4416_ = v_isSharedCheck_4426_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_4413_);
                    crate::leanh::lean_dec(v_a_4409_);
                    v___x_4415_ = crate::leanh::lean_box(0);
                    v_isShared_4416_ = v_isSharedCheck_4426_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_idx_4417_ = crate::leanh::lean_ctor_get(v_pos_4411_, 1);
                v___x_4418_ = lean_nat_dec_eq(v_idx_4413_, v_idx_4417_);
                crate::leanh::lean_dec(v_idx_4413_);
                if v___x_4418_ == 0 {
                    if v_isShared_4416_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4415_, 1);
                        crate::leanh::lean_ctor_set(v___x_4415_, 1, v_err_4412_);
                        crate::leanh::lean_ctor_set(v___x_4415_, 0, v_pos_4411_);
                        v___x_4420_ = v___x_4415_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4421_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_pos_4411_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4421_, 1, v_err_4412_);
                        v___x_4420_ = v_reuseFailAlloc_4421_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_err_4412_);
                    v___x_4422_ = crate::leanh::lean_box(0);
                    if v_isShared_4416_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4415_, 1, v___x_4422_);
                        crate::leanh::lean_ctor_set(v___x_4415_, 0, v_pos_4411_);
                        v___x_4424_ = v___x_4415_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4425_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_pos_4411_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 1, v___x_4422_);
                        v___x_4424_ = v_reuseFailAlloc_4425_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4420_;
            }
            4 => {
                return v___x_4424_;
            }
            5 => {
                v___x_4462_ =
                    l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter(
                        v_pos_4457_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4462_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_4409_);
                    v_pos_4463_ = crate::leanh::lean_ctor_get(v___x_4462_, 0);
                    v_res_4464_ = crate::leanh::lean_ctor_get(v___x_4462_, 1);
                    v_isSharedCheck_4476_ = (!crate::leanh::lean_is_exclusive(v___x_4462_)) as u8;
                    if v_isSharedCheck_4476_ == 0 {
                        v___x_4466_ = v___x_4462_;
                        v_isShared_4467_ = v_isSharedCheck_4476_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_res_4464_);
                        crate::leanh::lean_inc(v_pos_4463_);
                        crate::leanh::lean_dec(v___x_4462_);
                        v___x_4466_ = crate::leanh::lean_box(0);
                        v_isShared_4467_ = v_isSharedCheck_4476_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4460_);
                    crate::leanh::lean_dec(v_res_4458_);
                    crate::leanh::lean_dec(v_res_4455_);
                    crate::leanh::lean_dec(v_res_4452_);
                    crate::leanh::lean_dec(v_res_4449_);
                    crate::leanh::lean_dec(v_res_4446_);
                    crate::leanh::lean_dec(v_res_4443_);
                    crate::leanh::lean_dec(v_res_4440_);
                    crate::leanh::lean_dec(v_res_4429_);
                    v_pos_4477_ = crate::leanh::lean_ctor_get(v___x_4462_, 0);
                    crate::leanh::lean_inc(v_pos_4477_);
                    v_err_4478_ = crate::leanh::lean_ctor_get(v___x_4462_, 1);
                    crate::leanh::lean_inc(v_err_4478_);
                    crate::leanh::lean_dec_ref_known(v___x_4462_, 2);
                    v_pos_4411_ = v_pos_4477_;
                    v_err_4412_ = v_err_4478_;
                    state = 1;
                    continue;
                }
            }
            6 => {
                v___x_4468_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4468_, 0, v_res_4429_);
                crate::leanh::lean_ctor_set(v___x_4468_, 1, v_res_4440_);
                crate::leanh::lean_ctor_set(v___x_4468_, 2, v_res_4443_);
                crate::leanh::lean_ctor_set(v___x_4468_, 3, v_res_4446_);
                crate::leanh::lean_ctor_set(v___x_4468_, 4, v_res_4449_);
                crate::leanh::lean_ctor_set(v___x_4468_, 5, v_res_4452_);
                crate::leanh::lean_ctor_set(v___x_4468_, 6, v_res_4455_);
                crate::leanh::lean_ctor_set(v___x_4468_, 7, v_res_4458_);
                if v_isShared_4461_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4460_, 1, v_res_4464_);
                    crate::leanh::lean_ctor_set(v___x_4460_, 0, v___x_4468_);
                    v___x_4470_ = v___x_4460_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4475_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4475_, 0, v___x_4468_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4475_, 1, v_res_4464_);
                    v___x_4470_ = v_reuseFailAlloc_4475_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4471_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4471_, 0, v___x_4470_);
                if v_isShared_4467_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4466_, 1, v___x_4471_);
                    v___x_4473_ = v___x_4466_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4474_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_pos_4463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4474_, 1, v___x_4471_);
                    v___x_4473_ = v_reuseFailAlloc_4474_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4473_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_TimeZone_TZif_parse(
    mut v_a_4496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4505_: u8 = 0;
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4510_: u8 = 0;
    let mut v_pos_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4515_: u8 = 0;
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4519_: u8 = 0;
    let mut v_pos_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_err_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4524_: u8 = 0;
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4497_ =
                    l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV1(
                        v_a_4496_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4497_) == 0 {
                    v_pos_4498_ = crate::leanh::lean_ctor_get(v___x_4497_, 0);
                    crate::leanh::lean_inc(v_pos_4498_);
                    v_res_4499_ = crate::leanh::lean_ctor_get(v___x_4497_, 1);
                    crate::leanh::lean_inc(v_res_4499_);
                    crate::leanh::lean_dec_ref_known(v___x_4497_, 2);
                    v___x_4500_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV2(v_pos_4498_);
                    if crate::leanh::lean_obj_tag(v___x_4500_) == 0 {
                        v_pos_4501_ = crate::leanh::lean_ctor_get(v___x_4500_, 0);
                        v_res_4502_ = crate::leanh::lean_ctor_get(v___x_4500_, 1);
                        v_isSharedCheck_4510_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4500_)) as u8;
                        if v_isSharedCheck_4510_ == 0 {
                            v___x_4504_ = v___x_4500_;
                            v_isShared_4505_ = v_isSharedCheck_4510_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_res_4502_);
                            crate::leanh::lean_inc(v_pos_4501_);
                            crate::leanh::lean_dec(v___x_4500_);
                            v___x_4504_ = crate::leanh::lean_box(0);
                            v_isShared_4505_ = v_isSharedCheck_4510_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_res_4499_);
                        v_pos_4511_ = crate::leanh::lean_ctor_get(v___x_4500_, 0);
                        v_err_4512_ = crate::leanh::lean_ctor_get(v___x_4500_, 1);
                        v_isSharedCheck_4519_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4500_)) as u8;
                        if v_isSharedCheck_4519_ == 0 {
                            v___x_4514_ = v___x_4500_;
                            v_isShared_4515_ = v_isSharedCheck_4519_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_err_4512_);
                            crate::leanh::lean_inc(v_pos_4511_);
                            crate::leanh::lean_dec(v___x_4500_);
                            v___x_4514_ = crate::leanh::lean_box(0);
                            v_isShared_4515_ = v_isSharedCheck_4519_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_pos_4520_ = crate::leanh::lean_ctor_get(v___x_4497_, 0);
                    v_err_4521_ = crate::leanh::lean_ctor_get(v___x_4497_, 1);
                    v_isSharedCheck_4528_ = (!crate::leanh::lean_is_exclusive(v___x_4497_)) as u8;
                    if v_isSharedCheck_4528_ == 0 {
                        v___x_4523_ = v___x_4497_;
                        v_isShared_4524_ = v_isSharedCheck_4528_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_err_4521_);
                        crate::leanh::lean_inc(v_pos_4520_);
                        crate::leanh::lean_dec(v___x_4497_);
                        v___x_4523_ = crate::leanh::lean_box(0);
                        v_isShared_4524_ = v_isSharedCheck_4528_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4506_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4506_, 0, v_res_4499_);
                crate::leanh::lean_ctor_set(v___x_4506_, 1, v_res_4502_);
                if v_isShared_4505_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4504_, 1, v___x_4506_);
                    v___x_4508_ = v___x_4504_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4509_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_pos_4501_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4509_, 1, v___x_4506_);
                    v___x_4508_ = v_reuseFailAlloc_4509_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4508_;
            }
            3 => {
                if v_isShared_4515_ == 0 {
                    v___x_4517_ = v___x_4514_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4518_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_pos_4511_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4518_, 1, v_err_4512_);
                    v___x_4517_ = v_reuseFailAlloc_4518_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4517_;
            }
            5 => {
                if v_isShared_4524_ == 0 {
                    v___x_4526_ = v___x_4523_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4527_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_pos_4520_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4527_, 1, v_err_4521_);
                    v___x_4526_ = v_reuseFailAlloc_4527_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4526_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Zoned_Database_TzIf(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Parsec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Repr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Time_TimeZone_TZif_instInhabitedHeader_default =
        _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default();
    crate::leanh::lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedHeader_default);
    l_Std_Time_TimeZone_TZif_instInhabitedHeader =
        _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader();
    crate::leanh::lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedHeader);
    l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default =
        _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default();
    crate::leanh::lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default);
    l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType =
        _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType();
    crate::leanh::lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType);
    l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default =
        _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default();
    crate::leanh::lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default);
    l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond =
        _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond();
    crate::leanh::lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond);
    l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default =
        _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default();
    crate::leanh::lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default);
    l_Std_Time_TimeZone_TZif_instInhabitedTZifV1 =
        _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV1();
    crate::leanh::lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedTZifV1);
    l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default =
        _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default();
    crate::leanh::lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default);
    l_Std_Time_TimeZone_TZif_instInhabitedTZifV2 =
        _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV2();
    crate::leanh::lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedTZifV2);
    l_Std_Time_TimeZone_TZif_instInhabitedTZif_default =
        _init_l_Std_Time_TimeZone_TZif_instInhabitedTZif_default();
    crate::leanh::lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedTZif_default);
    l_Std_Time_TimeZone_TZif_instInhabitedTZif = _init_l_Std_Time_TimeZone_TZif_instInhabitedTZif();
    crate::leanh::lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedTZif);
    l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1 = _init_l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1();
    crate::leanh::lean_mark_persistent(l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Zoned_Database_TzIf(
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
pub unsafe fn initialize_Std_Time_Zoned_Database_TzIf(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Internal_Parsec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Repr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_Database_TzIf(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Zoned_Database_TzIf(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Time_Zoned_Database_TzIf(builtin);
}
