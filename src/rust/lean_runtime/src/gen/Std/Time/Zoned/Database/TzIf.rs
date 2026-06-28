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
    l_Lean_Name_mkStr1, l_Lean_Name_num___override, l_Lean_Name_str___override,
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
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
    lean_nat_sub, lean_panic_fn_borrowed, lean_uint8_dec_eq, lean_uint8_of_nat, lean_uint32_of_nat,
    lean_uint32_to_nat,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_box_uint32, lean_box_uint64, lean_closure_set, lean_cstr_to_nat, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_get_uint32, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint32, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint8_once,
    lean_uint32_once, lean_unbox, lean_unbox_uint32, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__0_value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__2_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__2_value) as *mut LeanObject,2126719535545605916 as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__3_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 105, 109, 101, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__4_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__4_value) as *mut LeanObject,14182064430198580444 as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__5_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__6_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [90, 111, 110, 101, 100, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__6_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__6_value) as *mut LeanObject,12797042221022953416 as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__7_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__8_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [68, 97, 116, 97, 98, 97, 115, 101, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__8_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__8_value) as *mut LeanObject,14246659929497392988 as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__9_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__10_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 122, 73, 102, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__10_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__10_value) as *mut LeanObject,9593979424156350980 as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__11_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__11_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,17284221013824265317 as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__12_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__2_value) as *mut LeanObject,16077304773555400774 as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__13_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__13_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__4_value) as *mut LeanObject,5244953291729708654 as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__14_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__15_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [84, 105, 109, 101, 90, 111, 110, 101, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__15_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__14_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__15_value) as *mut LeanObject,13444310946274085109 as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__16_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__17_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 90, 105, 102, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__17_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__16_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__17_value) as *mut LeanObject,5411744946770301377 as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__18_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__19_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 73, 110, 116, 51, 50, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__19_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__20_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__18_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__19_value) as *mut LeanObject,11496539451519720210 as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__20_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__21_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [73, 110, 116, 51, 50, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__21_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__22_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__21_value) as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__22_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__23_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__20_value) as *mut LeanObject,((( 1024 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__22_value) as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__23: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__23_value) as *mut LeanObject;
pub static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__23_value
) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 110, 116, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__0_value) as *mut LeanObject;
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__0_value) as *mut LeanObject,7009148538150066493 as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__2_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__2_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__3_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__4_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__2_value) as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__4_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__4_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__5_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__5_value) as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__6_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__0_value) as *mut LeanObject,5117844058249666356 as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 101, 114, 109, 73, 110, 116, 54, 52, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__18_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__0_value) as *mut LeanObject,7844554101976475412 as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [73, 110, 116, 54, 52, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__2_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__2_value) as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__3_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__1_value) as *mut LeanObject,((( 1024 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__3_value) as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__4_value) as *mut LeanObject;
pub static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__4_value
) as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__0_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__1_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__2_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__1_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__3_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__2_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__4_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__4_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__6_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__3_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__8_value:
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
    m_data: [44, 0],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__8_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__10_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__11_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__10_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__12_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__13_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__12_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__13_value)
        as *mut LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__15_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__15_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__16_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__15_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__16_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__17_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__17_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__18_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__17_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__18_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__19_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__19_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__20_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__19_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__20_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__21_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__21_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__22_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__21_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__22_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__23_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__23_value)
        as *mut LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__24_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__23_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprHeader___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_TimeZone_TZif_instReprHeader_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_TimeZone_TZif_instReprHeader___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_TimeZone_TZif_instReprHeader: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader___closed__0_value)
        as *mut LeanObject;
static mut l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0: u8 = 0;
static mut l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__1: u32 = 0;
static mut l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedHeader_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedHeader: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__0_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__0_value
) as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__1_value
) as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__2_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__1_value
        ) as *mut LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__2_value
) as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__2_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__3_value
) as *mut LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__5_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__5_value
) as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__6_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__5_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__6_value
) as *mut LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__8_value:
    LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__8_value
) as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__9_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__8_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__9_value
) as *mut LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprLocalTimeType___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_TimeZone_TZif_instReprLocalTimeType: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType___closed__0_value)
        as *mut LeanObject;
static mut l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__0_value:
    LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__2_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__1_value
        ) as *mut LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__2_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__5_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__6_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__5_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprLeapSecond___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprLeapSecond___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_TimeZone_TZif_instReprLeapSecond: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprLeapSecond___closed__0_value)
        as *mut LeanObject;
static mut l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [35, 91, 0]};
static mut l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__0_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9_value) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__2_value
) as *mut LeanObject;
static mut l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__0_value) as *mut LeanObject] };
static mut l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__2_value) as *mut LeanObject] };
static mut l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__7_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [35, 91, 93, 0]};
static mut l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__7_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__7_value) as *mut LeanObject] };
static mut l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8_value
) as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__0_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__1_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__2_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__1_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__3_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__2_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__5_value:
    LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__6_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__5_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__8_value:
    LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__9_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__8_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__10_value:
    LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__11_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__10_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__12_value:
    LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__13_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__12_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__13_value)
        as *mut LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__15_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__15_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__16_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__15_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__16_value)
        as *mut LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__18_value:
    LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__18_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__19_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__18_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__19_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__20_value:
    LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__20_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__21_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__20_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__21_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV1___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_TimeZone_TZif_instReprTZifV1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_TimeZone_TZif_instReprTZifV1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV1___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__0_value: LeanArrayObject<
    0,
> = LeanArrayObject {
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
static mut l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__0_value)
        as *mut LeanObject;
static mut l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedTZifV1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__0_value) as *mut LeanObject] };
static mut l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__1_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 111, 109, 101, 32, 0]};
static mut l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__2_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__2_value) as *mut LeanObject] };
static mut l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__3_value
) as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__0_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__1_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__2_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__1_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__3_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__2_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__4_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__5_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__4_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZifV2___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_TimeZone_TZif_instReprTZifV2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV2___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_TimeZone_TZif_instReprTZifV2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZifV2___closed__0_value)
        as *mut LeanObject;
static mut l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedTZifV2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__0_value: LeanStringObject<
    3,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__1_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__2_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__1_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__3_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__2_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__5_value: LeanStringObject<
    3,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__6_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__5_value
    ) as *mut LeanObject],
};
static mut l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Time_TimeZone_TZif_instReprTZif___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_TimeZone_TZif_instReprTZif_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_TimeZone_TZif_instReprTZif___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZif___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_TimeZone_TZif_instReprTZif: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_TZif_instReprTZif___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedTZif_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_TZif_instInhabitedTZif: *mut LeanObject = core::ptr::null_mut();
pub static mut l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__0_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [83, 116, 100, 46, 84, 105, 109, 101, 46, 90, 111, 110, 101, 100, 46, 68, 97, 116, 97, 98, 97, 115, 101, 46, 84, 122, 73, 102, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__1_value: LeanStringObject<72> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 72, m_capacity: 72, m_length: 71, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 83, 116, 100, 46, 84, 105, 109, 101, 46, 90, 111, 110, 101, 100, 46, 68, 97, 116, 97, 98, 97, 115, 101, 46, 84, 122, 73, 102, 46, 48, 46, 83, 116, 100, 46, 84, 105, 109, 101, 46, 84, 105, 109, 101, 90, 111, 110, 101, 46, 84, 90, 105, 102, 46, 116, 111, 85, 73, 110, 116, 51, 50, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__2_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 98, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 52, 10, 32, 32, 0]};
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__2_value) as *mut LeanObject;
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg___closed__0_value) as *mut LeanObject;
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0_value) as *mut LeanObject] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__1_value) as *mut LeanObject;
pub static l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [99, 111, 110, 100, 105, 116, 105, 111, 110, 32, 110, 111, 116, 32, 115, 97, 116, 105, 115, 102, 105, 101, 100, 0]};
static mut l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__0_value) as *mut LeanObject] };
static mut l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter___closed__0_value) as *mut LeanObject;
pub unsafe fn _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1()
-> *mut LeanObject {
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    v___x_2319_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__0;
    v___x_2320_ = l_String_toRawSubstring_x27(v___x_2319_);
    return v___x_2320_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1(
    mut v_x_2334_: *mut LeanObject,
    mut v_a_2335_: *mut LeanObject,
    mut v_a_2336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: u8 = 0;
    v___x_2337_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__20;
    v___x_2338_ = l_Lean_Syntax_isOfKind(v_x_2334_, v___x_2337_);
    if v___x_2338_ == 0 {
        let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
        v___x_2339_ = lean_box(1);
        v___x_2340_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2340_, 0, v___x_2339_);
        lean_ctor_set(v___x_2340_, 1, v_a_2336_);
        return v___x_2340_;
    } else {
        let mut v_quotContext_2341_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2342_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_2343_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2344_: u8 = 0;
        let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_2341_ = lean_ctor_get(v_a_2335_, 1);
        v_currMacroScope_2342_ = lean_ctor_get(v_a_2335_, 2);
        v_ref_2343_ = lean_ctor_get(v_a_2335_, 5);
        v___x_2344_ = 0;
        v___x_2345_ = l_Lean_SourceInfo_fromRef(v_ref_2343_, v___x_2344_);
        v___x_2346_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1), core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1_once), _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1);
        v___x_2347_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__2;
        lean_inc(v_currMacroScope_2342_);
        lean_inc(v_quotContext_2341_);
        v___x_2348_ =
            l_Lean_addMacroScope(v_quotContext_2341_, v___x_2347_, v_currMacroScope_2342_);
        v___x_2349_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__6;
        v___x_2350_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2350_, 0, v___x_2345_);
        lean_ctor_set(v___x_2350_, 1, v___x_2346_);
        lean_ctor_set(v___x_2350_, 2, v___x_2348_);
        lean_ctor_set(v___x_2350_, 3, v___x_2349_);
        v___x_2351_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2351_, 0, v___x_2350_);
        lean_ctor_set(v___x_2351_, 1, v_a_2336_);
        return v___x_2351_;
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___boxed(
    mut v_x_2352_: *mut LeanObject,
    mut v_a_2353_: *mut LeanObject,
    mut v_a_2354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2355_: *mut LeanObject = core::ptr::null_mut();
    v_res_2355_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1(v_x_2352_, v_a_2353_, v_a_2354_);
    lean_dec_ref(v_a_2353_);
    return v_res_2355_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1(
    mut v_x_2359_: *mut LeanObject,
    mut v_a_2360_: *mut LeanObject,
    mut v_a_2361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: u8 = 0;
    v___x_2362_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__1;
    lean_inc(v_x_2359_);
    v___x_2363_ = l_Lean_Syntax_isOfKind(v_x_2359_, v___x_2362_);
    if v___x_2363_ == 0 {
        let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2359_);
        v___x_2364_ = lean_box(0);
        v___x_2365_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2365_, 0, v___x_2364_);
        lean_ctor_set(v___x_2365_, 1, v_a_2361_);
        return v___x_2365_;
    } else {
        let mut v_ref_2366_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2367_: u8 = 0;
        let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
        v_ref_2366_ = l_Lean_replaceRef(v_x_2359_, v_a_2360_);
        lean_dec(v_x_2359_);
        v___x_2367_ = 0;
        v___x_2368_ = l_Lean_SourceInfo_fromRef(v_ref_2366_, v___x_2367_);
        lean_dec(v_ref_2366_);
        v___x_2369_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__20;
        v___x_2370_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__21;
        lean_inc(v___x_2368_);
        v___x_2371_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2371_, 0, v___x_2368_);
        lean_ctor_set(v___x_2371_, 1, v___x_2370_);
        v___x_2372_ = l_Lean_Syntax_node1(v___x_2368_, v___x_2369_, v___x_2371_);
        v___x_2373_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2373_, 0, v___x_2372_);
        lean_ctor_set(v___x_2373_, 1, v_a_2361_);
        return v___x_2373_;
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___boxed(
    mut v_x_2374_: *mut LeanObject,
    mut v_a_2375_: *mut LeanObject,
    mut v_a_2376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2377_: *mut LeanObject = core::ptr::null_mut();
    v_res_2377_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1(v_x_2374_, v_a_2375_, v_a_2376_);
    lean_dec(v_a_2375_);
    return v_res_2377_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt64__1(
    mut v_x_2390_: *mut LeanObject,
    mut v_a_2391_: *mut LeanObject,
    mut v_a_2392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: u8 = 0;
    v___x_2393_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__1;
    v___x_2394_ = l_Lean_Syntax_isOfKind(v_x_2390_, v___x_2393_);
    if v___x_2394_ == 0 {
        let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
        v___x_2395_ = lean_box(1);
        v___x_2396_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2396_, 0, v___x_2395_);
        lean_ctor_set(v___x_2396_, 1, v_a_2392_);
        return v___x_2396_;
    } else {
        let mut v_quotContext_2397_: *mut LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_2398_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ref_2399_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2400_: u8 = 0;
        let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
        v_quotContext_2397_ = lean_ctor_get(v_a_2391_, 1);
        v_currMacroScope_2398_ = lean_ctor_get(v_a_2391_, 2);
        v_ref_2399_ = lean_ctor_get(v_a_2391_, 5);
        v___x_2400_ = 0;
        v___x_2401_ = l_Lean_SourceInfo_fromRef(v_ref_2399_, v___x_2400_);
        v___x_2402_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1), core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1_once), _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__1);
        v___x_2403_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__2;
        lean_inc(v_currMacroScope_2398_);
        lean_inc(v_quotContext_2397_);
        v___x_2404_ =
            l_Lean_addMacroScope(v_quotContext_2397_, v___x_2403_, v_currMacroScope_2398_);
        v___x_2405_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt32__1___closed__6;
        v___x_2406_ = lean_alloc_ctor(3, 4, (0) as u32);
        lean_ctor_set(v___x_2406_, 0, v___x_2401_);
        lean_ctor_set(v___x_2406_, 1, v___x_2402_);
        lean_ctor_set(v___x_2406_, 2, v___x_2404_);
        lean_ctor_set(v___x_2406_, 3, v___x_2405_);
        v___x_2407_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2407_, 0, v___x_2406_);
        lean_ctor_set(v___x_2407_, 1, v_a_2392_);
        return v___x_2407_;
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt64__1___boxed(
    mut v_x_2408_: *mut LeanObject,
    mut v_a_2409_: *mut LeanObject,
    mut v_a_2410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2411_: *mut LeanObject = core::ptr::null_mut();
    v_res_2411_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______macroRules____private__Std__Time__Zoned__Database__TzIf__0__Std__Time__TimeZone__TZif__termInt64__1(v_x_2408_, v_a_2409_, v_a_2410_);
    lean_dec_ref(v_a_2409_);
    return v_res_2411_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__2(
    mut v_x_2412_: *mut LeanObject,
    mut v_a_2413_: *mut LeanObject,
    mut v_a_2414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: u8 = 0;
    v___x_2415_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__1___closed__1;
    lean_inc(v_x_2412_);
    v___x_2416_ = l_Lean_Syntax_isOfKind(v_x_2412_, v___x_2415_);
    if v___x_2416_ == 0 {
        let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2412_);
        v___x_2417_ = lean_box(0);
        v___x_2418_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2418_, 0, v___x_2417_);
        lean_ctor_set(v___x_2418_, 1, v_a_2414_);
        return v___x_2418_;
    } else {
        let mut v_ref_2419_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2420_: u8 = 0;
        let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
        v_ref_2419_ = l_Lean_replaceRef(v_x_2412_, v_a_2413_);
        lean_dec(v_x_2412_);
        v___x_2420_ = 0;
        v___x_2421_ = l_Lean_SourceInfo_fromRef(v_ref_2419_, v___x_2420_);
        lean_dec(v_ref_2419_);
        v___x_2422_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__1;
        v___x_2423_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt64___closed__2;
        lean_inc(v___x_2421_);
        v___x_2424_ = lean_alloc_ctor(2, 2, (0) as u32);
        lean_ctor_set(v___x_2424_, 0, v___x_2421_);
        lean_ctor_set(v___x_2424_, 1, v___x_2423_);
        v___x_2425_ = l_Lean_Syntax_node1(v___x_2421_, v___x_2422_, v___x_2424_);
        v___x_2426_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2426_, 0, v___x_2425_);
        lean_ctor_set(v___x_2426_, 1, v_a_2414_);
        return v___x_2426_;
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__2___boxed(
    mut v_x_2427_: *mut LeanObject,
    mut v_a_2428_: *mut LeanObject,
    mut v_a_2429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2430_: *mut LeanObject = core::ptr::null_mut();
    v_res_2430_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif___aux__Std__Time__Zoned__Database__TzIf______unexpand__Int__2(v_x_2427_, v_a_2428_, v_a_2429_);
    lean_dec(v_a_2428_);
    return v_res_2430_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_TimeZone_TZif_instReprHeader_repr_spec__0(
    mut v_a_2431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    v___x_2432_ = lean_nat_to_int(v_a_2431_);
    return v___x_2432_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    v___x_2446_ = lean_unsigned_to_nat(11);
    v___x_2447_ = lean_nat_to_int(v___x_2446_);
    return v___x_2447_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14()
-> *mut LeanObject {
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    v___x_2457_ = lean_unsigned_to_nat(12);
    v___x_2458_ = lean_nat_to_int(v___x_2457_);
    return v___x_2458_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__24()
-> *mut LeanObject {
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    v___x_2472_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__0;
    v___x_2473_ = lean_string_length(v___x_2472_);
    return v___x_2473_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25()
-> *mut LeanObject {
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    v___x_2474_ = lean_obj_once(
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
    mut v_x_2480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_version_2481_: u8 = 0;
    let mut v_isutcnt_2482_: u32 = 0;
    let mut v_isstdcnt_2483_: u32 = 0;
    let mut v_leapcnt_2484_: u32 = 0;
    let mut v_timecnt_2485_: u32 = 0;
    let mut v_typecnt_2486_: u32 = 0;
    let mut v_charcnt_2487_: u32 = 0;
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: u8 = 0;
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    v_version_2481_ = lean_ctor_get_uint8(v_x_2480_, 24 as u32);
    v_isutcnt_2482_ = lean_ctor_get_uint32(v_x_2480_, 0 as u32);
    v_isstdcnt_2483_ = lean_ctor_get_uint32(v_x_2480_, 4 as u32);
    v_leapcnt_2484_ = lean_ctor_get_uint32(v_x_2480_, 8 as u32);
    v_timecnt_2485_ = lean_ctor_get_uint32(v_x_2480_, 12 as u32);
    v_typecnt_2486_ = lean_ctor_get_uint32(v_x_2480_, 16 as u32);
    v_charcnt_2487_ = lean_ctor_get_uint32(v_x_2480_, 20 as u32);
    v___x_2488_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5;
    v___x_2489_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__6;
    v___x_2490_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__7_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__7,
    );
    v___x_2491_ = lean_uint8_to_nat(v_version_2481_);
    v___x_2492_ = l_Nat_reprFast(v___x_2491_);
    v___x_2493_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2493_, 0, v___x_2492_);
    v___x_2494_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2494_, 0, v___x_2490_);
    lean_ctor_set(v___x_2494_, 1, v___x_2493_);
    v___x_2495_ = 0;
    v___x_2496_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2496_, 0, v___x_2494_);
    lean_ctor_set_uint8(
        v___x_2496_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2495_,
    );
    v___x_2497_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2497_, 0, v___x_2489_);
    lean_ctor_set(v___x_2497_, 1, v___x_2496_);
    v___x_2498_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9;
    v___x_2499_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2499_, 0, v___x_2497_);
    lean_ctor_set(v___x_2499_, 1, v___x_2498_);
    v___x_2500_ = lean_box(1);
    v___x_2501_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2501_, 0, v___x_2499_);
    lean_ctor_set(v___x_2501_, 1, v___x_2500_);
    v___x_2502_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__11;
    v___x_2503_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2503_, 0, v___x_2501_);
    lean_ctor_set(v___x_2503_, 1, v___x_2502_);
    v___x_2504_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2504_, 0, v___x_2503_);
    lean_ctor_set(v___x_2504_, 1, v___x_2488_);
    v___x_2505_ = lean_uint32_to_nat(v_isutcnt_2482_);
    v___x_2506_ = l_Nat_reprFast(v___x_2505_);
    v___x_2507_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2507_, 0, v___x_2506_);
    v___x_2508_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2508_, 0, v___x_2490_);
    lean_ctor_set(v___x_2508_, 1, v___x_2507_);
    v___x_2509_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2509_, 0, v___x_2508_);
    lean_ctor_set_uint8(
        v___x_2509_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2495_,
    );
    v___x_2510_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2510_, 0, v___x_2504_);
    lean_ctor_set(v___x_2510_, 1, v___x_2509_);
    v___x_2511_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2511_, 0, v___x_2510_);
    lean_ctor_set(v___x_2511_, 1, v___x_2498_);
    v___x_2512_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2512_, 0, v___x_2511_);
    lean_ctor_set(v___x_2512_, 1, v___x_2500_);
    v___x_2513_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__13;
    v___x_2514_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2514_, 0, v___x_2512_);
    lean_ctor_set(v___x_2514_, 1, v___x_2513_);
    v___x_2515_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2515_, 0, v___x_2514_);
    lean_ctor_set(v___x_2515_, 1, v___x_2488_);
    v___x_2516_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14,
    );
    v___x_2517_ = lean_uint32_to_nat(v_isstdcnt_2483_);
    v___x_2518_ = l_Nat_reprFast(v___x_2517_);
    v___x_2519_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2519_, 0, v___x_2518_);
    v___x_2520_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2520_, 0, v___x_2516_);
    lean_ctor_set(v___x_2520_, 1, v___x_2519_);
    v___x_2521_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2521_, 0, v___x_2520_);
    lean_ctor_set_uint8(
        v___x_2521_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2495_,
    );
    v___x_2522_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2522_, 0, v___x_2515_);
    lean_ctor_set(v___x_2522_, 1, v___x_2521_);
    v___x_2523_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2523_, 0, v___x_2522_);
    lean_ctor_set(v___x_2523_, 1, v___x_2498_);
    v___x_2524_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2524_, 0, v___x_2523_);
    lean_ctor_set(v___x_2524_, 1, v___x_2500_);
    v___x_2525_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__16;
    v___x_2526_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2526_, 0, v___x_2524_);
    lean_ctor_set(v___x_2526_, 1, v___x_2525_);
    v___x_2527_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2527_, 0, v___x_2526_);
    lean_ctor_set(v___x_2527_, 1, v___x_2488_);
    v___x_2528_ = lean_uint32_to_nat(v_leapcnt_2484_);
    v___x_2529_ = l_Nat_reprFast(v___x_2528_);
    v___x_2530_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2530_, 0, v___x_2529_);
    v___x_2531_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2531_, 0, v___x_2490_);
    lean_ctor_set(v___x_2531_, 1, v___x_2530_);
    v___x_2532_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2532_, 0, v___x_2531_);
    lean_ctor_set_uint8(
        v___x_2532_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2495_,
    );
    v___x_2533_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2533_, 0, v___x_2527_);
    lean_ctor_set(v___x_2533_, 1, v___x_2532_);
    v___x_2534_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2534_, 0, v___x_2533_);
    lean_ctor_set(v___x_2534_, 1, v___x_2498_);
    v___x_2535_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2535_, 0, v___x_2534_);
    lean_ctor_set(v___x_2535_, 1, v___x_2500_);
    v___x_2536_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__18;
    v___x_2537_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2537_, 0, v___x_2535_);
    lean_ctor_set(v___x_2537_, 1, v___x_2536_);
    v___x_2538_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2538_, 0, v___x_2537_);
    lean_ctor_set(v___x_2538_, 1, v___x_2488_);
    v___x_2539_ = lean_uint32_to_nat(v_timecnt_2485_);
    v___x_2540_ = l_Nat_reprFast(v___x_2539_);
    v___x_2541_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2541_, 0, v___x_2540_);
    v___x_2542_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2542_, 0, v___x_2490_);
    lean_ctor_set(v___x_2542_, 1, v___x_2541_);
    v___x_2543_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2543_, 0, v___x_2542_);
    lean_ctor_set_uint8(
        v___x_2543_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2495_,
    );
    v___x_2544_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2544_, 0, v___x_2538_);
    lean_ctor_set(v___x_2544_, 1, v___x_2543_);
    v___x_2545_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2545_, 0, v___x_2544_);
    lean_ctor_set(v___x_2545_, 1, v___x_2498_);
    v___x_2546_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2546_, 0, v___x_2545_);
    lean_ctor_set(v___x_2546_, 1, v___x_2500_);
    v___x_2547_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__20;
    v___x_2548_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2548_, 0, v___x_2546_);
    lean_ctor_set(v___x_2548_, 1, v___x_2547_);
    v___x_2549_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2549_, 0, v___x_2548_);
    lean_ctor_set(v___x_2549_, 1, v___x_2488_);
    v___x_2550_ = lean_uint32_to_nat(v_typecnt_2486_);
    v___x_2551_ = l_Nat_reprFast(v___x_2550_);
    v___x_2552_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2552_, 0, v___x_2551_);
    v___x_2553_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2553_, 0, v___x_2490_);
    lean_ctor_set(v___x_2553_, 1, v___x_2552_);
    v___x_2554_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2554_, 0, v___x_2553_);
    lean_ctor_set_uint8(
        v___x_2554_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2495_,
    );
    v___x_2555_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2555_, 0, v___x_2549_);
    lean_ctor_set(v___x_2555_, 1, v___x_2554_);
    v___x_2556_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2556_, 0, v___x_2555_);
    lean_ctor_set(v___x_2556_, 1, v___x_2498_);
    v___x_2557_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2557_, 0, v___x_2556_);
    lean_ctor_set(v___x_2557_, 1, v___x_2500_);
    v___x_2558_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__22;
    v___x_2559_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2559_, 0, v___x_2557_);
    lean_ctor_set(v___x_2559_, 1, v___x_2558_);
    v___x_2560_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2560_, 0, v___x_2559_);
    lean_ctor_set(v___x_2560_, 1, v___x_2488_);
    v___x_2561_ = lean_uint32_to_nat(v_charcnt_2487_);
    v___x_2562_ = l_Nat_reprFast(v___x_2561_);
    v___x_2563_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2563_, 0, v___x_2562_);
    v___x_2564_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2564_, 0, v___x_2490_);
    lean_ctor_set(v___x_2564_, 1, v___x_2563_);
    v___x_2565_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2565_, 0, v___x_2564_);
    lean_ctor_set_uint8(
        v___x_2565_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2495_,
    );
    v___x_2566_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2566_, 0, v___x_2560_);
    lean_ctor_set(v___x_2566_, 1, v___x_2565_);
    v___x_2567_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25,
    );
    v___x_2568_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26;
    v___x_2569_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2569_, 0, v___x_2568_);
    lean_ctor_set(v___x_2569_, 1, v___x_2566_);
    v___x_2570_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27;
    v___x_2571_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2571_, 0, v___x_2569_);
    lean_ctor_set(v___x_2571_, 1, v___x_2570_);
    v___x_2572_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2572_, 0, v___x_2567_);
    lean_ctor_set(v___x_2572_, 1, v___x_2571_);
    v___x_2573_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2573_, 0, v___x_2572_);
    lean_ctor_set_uint8(
        v___x_2573_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2495_,
    );
    return v___x_2573_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___boxed(
    mut v_x_2574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2575_: *mut LeanObject = core::ptr::null_mut();
    v_res_2575_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg(v_x_2574_);
    lean_dec_ref(v_x_2574_);
    return v_res_2575_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprHeader_repr(
    mut v_x_2576_: *mut LeanObject,
    mut v_prec_2577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    v___x_2578_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg(v_x_2576_);
    return v___x_2578_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprHeader_repr___boxed(
    mut v_x_2579_: *mut LeanObject,
    mut v_prec_2580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2581_: *mut LeanObject = core::ptr::null_mut();
    v_res_2581_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr(v_x_2579_, v_prec_2580_);
    lean_dec(v_prec_2580_);
    lean_dec_ref(v_x_2579_);
    return v_res_2581_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0() -> u8 {
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: u8 = 0;
    v___x_2584_ = lean_unsigned_to_nat(0);
    v___x_2585_ = lean_uint8_of_nat(v___x_2584_);
    return v___x_2585_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__1() -> u32 {
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: u32 = 0;
    v___x_2586_ = lean_unsigned_to_nat(0);
    v___x_2587_ = lean_uint32_of_nat(v___x_2586_);
    return v___x_2587_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__2()
-> *mut LeanObject {
    let mut v___x_2588_: u32 = 0;
    let mut v___x_2589_: u8 = 0;
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    v___x_2588_ = lean_uint32_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__1_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__1,
    );
    v___x_2589_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0,
    );
    v___x_2590_ = lean_alloc_ctor(0, 0, (25) as u32);
    lean_ctor_set_uint8(v___x_2590_, 24 as u32, v___x_2589_);
    lean_ctor_set_uint32(v___x_2590_, 0 as u32, v___x_2588_);
    lean_ctor_set_uint32(v___x_2590_, 4 as u32, v___x_2588_);
    lean_ctor_set_uint32(v___x_2590_, 8 as u32, v___x_2588_);
    lean_ctor_set_uint32(v___x_2590_, 12 as u32, v___x_2588_);
    lean_ctor_set_uint32(v___x_2590_, 16 as u32, v___x_2588_);
    lean_ctor_set_uint32(v___x_2590_, 20 as u32, v___x_2588_);
    return v___x_2590_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default() -> *mut LeanObject {
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    v___x_2591_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__2_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__2,
    );
    return v___x_2591_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader() -> *mut LeanObject {
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    v___x_2592_ = l_Std_Time_TimeZone_TZif_instInhabitedHeader_default;
    return v___x_2592_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    v___x_2602_ = lean_unsigned_to_nat(13);
    v___x_2603_ = lean_nat_to_int(v___x_2602_);
    return v___x_2603_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    v___x_2607_ = lean_unsigned_to_nat(9);
    v___x_2608_ = lean_nat_to_int(v___x_2607_);
    return v___x_2608_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10()
-> *mut LeanObject {
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    v___x_2612_ = lean_unsigned_to_nat(21);
    v___x_2613_ = lean_nat_to_int(v___x_2612_);
    return v___x_2613_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    v___x_2614_ = lean_unsigned_to_nat(0);
    v___x_2615_ = lean_nat_to_int(v___x_2614_);
    return v___x_2615_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(
    mut v_x_2616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_gmtOffset_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isDst_2618_: u8 = 0;
    let mut v_abbreviationIndex_2619_: u8 = 0;
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: u8 = 0;
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: u8 = 0;
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_gmtOffset_2617_ = lean_ctor_get(v_x_2616_, 0);
                v_isDst_2618_ = lean_ctor_get_uint8(
                    v_x_2616_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_abbreviationIndex_2619_ = lean_ctor_get_uint8(
                    v_x_2616_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v___x_2620_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5;
                v___x_2621_ =
                    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__3;
                v___x_2622_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4), core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4_once), _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__4);
                v___x_2660_ = lean_unsigned_to_nat(0);
                v___x_2661_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11), core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once), _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
                v___x_2662_ = lean_int_dec_lt(v_gmtOffset_2617_, v___x_2661_);
                if v___x_2662_ == 0 {
                    v___x_2663_ = l_Int_repr(v_gmtOffset_2617_);
                    v___x_2664_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2664_, 0, v___x_2663_);
                    v___y_2624_ = v___x_2664_;
                    state = 1;
                    continue;
                } else {
                    v___x_2665_ = l_Int_repr(v_gmtOffset_2617_);
                    v___x_2666_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2666_, 0, v___x_2665_);
                    v___x_2667_ = l_Repr_addAppParen(v___x_2666_, v___x_2660_);
                    v___y_2624_ = v___x_2667_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2625_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2625_, 0, v___x_2622_);
                lean_ctor_set(v___x_2625_, 1, v___y_2624_);
                v___x_2626_ = 0;
                v___x_2627_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2627_, 0, v___x_2625_);
                lean_ctor_set_uint8(
                    v___x_2627_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2626_,
                );
                v___x_2628_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2628_, 0, v___x_2621_);
                lean_ctor_set(v___x_2628_, 1, v___x_2627_);
                v___x_2629_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9;
                v___x_2630_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2630_, 0, v___x_2628_);
                lean_ctor_set(v___x_2630_, 1, v___x_2629_);
                v___x_2631_ = lean_box(1);
                v___x_2632_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2632_, 0, v___x_2630_);
                lean_ctor_set(v___x_2632_, 1, v___x_2631_);
                v___x_2633_ =
                    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__6;
                v___x_2634_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2634_, 0, v___x_2632_);
                lean_ctor_set(v___x_2634_, 1, v___x_2633_);
                v___x_2635_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2635_, 0, v___x_2634_);
                lean_ctor_set(v___x_2635_, 1, v___x_2620_);
                v___x_2636_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7), core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7_once), _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__7);
                v___x_2637_ = l_Bool_repr___redArg(v_isDst_2618_);
                v___x_2638_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2638_, 0, v___x_2636_);
                lean_ctor_set(v___x_2638_, 1, v___x_2637_);
                v___x_2639_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2639_, 0, v___x_2638_);
                lean_ctor_set_uint8(
                    v___x_2639_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2626_,
                );
                v___x_2640_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2640_, 0, v___x_2635_);
                lean_ctor_set(v___x_2640_, 1, v___x_2639_);
                v___x_2641_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2641_, 0, v___x_2640_);
                lean_ctor_set(v___x_2641_, 1, v___x_2629_);
                v___x_2642_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2642_, 0, v___x_2641_);
                lean_ctor_set(v___x_2642_, 1, v___x_2631_);
                v___x_2643_ =
                    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__9;
                v___x_2644_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2644_, 0, v___x_2642_);
                lean_ctor_set(v___x_2644_, 1, v___x_2643_);
                v___x_2645_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2645_, 0, v___x_2644_);
                lean_ctor_set(v___x_2645_, 1, v___x_2620_);
                v___x_2646_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10), core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10_once), _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__10);
                v___x_2647_ = lean_uint8_to_nat(v_abbreviationIndex_2619_);
                v___x_2648_ = l_Nat_reprFast(v___x_2647_);
                v___x_2649_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2649_, 0, v___x_2648_);
                v___x_2650_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2650_, 0, v___x_2646_);
                lean_ctor_set(v___x_2650_, 1, v___x_2649_);
                v___x_2651_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2651_, 0, v___x_2650_);
                lean_ctor_set_uint8(
                    v___x_2651_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2626_,
                );
                v___x_2652_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2652_, 0, v___x_2645_);
                lean_ctor_set(v___x_2652_, 1, v___x_2651_);
                v___x_2653_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25,
                );
                v___x_2654_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26;
                v___x_2655_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2655_, 0, v___x_2654_);
                lean_ctor_set(v___x_2655_, 1, v___x_2652_);
                v___x_2656_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27;
                v___x_2657_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2657_, 0, v___x_2655_);
                lean_ctor_set(v___x_2657_, 1, v___x_2656_);
                v___x_2658_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2658_, 0, v___x_2653_);
                lean_ctor_set(v___x_2658_, 1, v___x_2657_);
                v___x_2659_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2659_, 0, v___x_2658_);
                lean_ctor_set_uint8(
                    v___x_2659_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2626_,
                );
                return v___x_2659_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___boxed(
    mut v_x_2668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2669_: *mut LeanObject = core::ptr::null_mut();
    v_res_2669_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_x_2668_);
    lean_dec_ref(v_x_2668_);
    return v_res_2669_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr(
    mut v_x_2670_: *mut LeanObject,
    mut v_prec_2671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    v___x_2672_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_x_2670_);
    return v___x_2672_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___boxed(
    mut v_x_2673_: *mut LeanObject,
    mut v_prec_2674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2675_: *mut LeanObject = core::ptr::null_mut();
    v_res_2675_ = l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr(v_x_2673_, v_prec_2674_);
    lean_dec(v_prec_2674_);
    lean_dec_ref(v_x_2673_);
    return v_res_2675_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default___closed__0()
-> *mut LeanObject {
    let mut v___x_2678_: u8 = 0;
    let mut v___x_2679_: u8 = 0;
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    v___x_2678_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default___closed__0,
    );
    v___x_2679_ = 0;
    v___x_2680_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11
        ),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11,
    );
    v___x_2681_ = lean_alloc_ctor(0, 1, (2) as u32);
    lean_ctor_set(v___x_2681_, 0, v___x_2680_);
    lean_ctor_set_uint8(
        v___x_2681_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2679_,
    );
    lean_ctor_set_uint8(
        v___x_2681_,
        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
        v___x_2678_,
    );
    return v___x_2681_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default() -> *mut LeanObject
{
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    v___x_2682_ = lean_obj_once(
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
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType() -> *mut LeanObject {
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    v___x_2683_ = l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default;
    return v___x_2683_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    v___x_2693_ = lean_unsigned_to_nat(18);
    v___x_2694_ = lean_nat_to_int(v___x_2693_);
    return v___x_2694_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    v___x_2698_ = lean_unsigned_to_nat(14);
    v___x_2699_ = lean_nat_to_int(v___x_2698_);
    return v___x_2699_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(
    mut v_x_2700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_transitionTime_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_correction_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2705_: u8 = 0;
    let mut v___y_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2709_: u8 = 0;
    let mut v___y_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: u8 = 0;
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: u8 = 0;
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: u8 = 0;
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2756_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_transitionTime_2701_ = lean_ctor_get(v_x_2700_, 0);
                v_correction_2702_ = lean_ctor_get(v_x_2700_, 1);
                v_isSharedCheck_2756_ = (!lean_is_exclusive(v_x_2700_)) as u8;
                if v_isSharedCheck_2756_ == 0 {
                    v___x_2704_ = v_x_2700_;
                    v_isShared_2705_ = v_isSharedCheck_2756_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_correction_2702_);
                    lean_inc(v_transitionTime_2701_);
                    lean_dec(v_x_2700_);
                    v___x_2704_ = lean_box(0);
                    v_isShared_2705_ = v_isSharedCheck_2756_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2723_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5;
                v___x_2724_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__3;
                v___x_2725_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4_once
                    ),
                    _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__4,
                );
                v___x_2748_ = lean_unsigned_to_nat(0);
                v___x_2749_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11), core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once), _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
                v___x_2750_ = lean_int_dec_lt(v_transitionTime_2701_, v___x_2749_);
                if v___x_2750_ == 0 {
                    v___x_2751_ = l_Int_repr(v_transitionTime_2701_);
                    lean_dec(v_transitionTime_2701_);
                    v___x_2752_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2752_, 0, v___x_2751_);
                    v___y_2727_ = v___x_2752_;
                    state = 4;
                    continue;
                } else {
                    v___x_2753_ = l_Int_repr(v_transitionTime_2701_);
                    lean_dec(v_transitionTime_2701_);
                    v___x_2754_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2754_, 0, v___x_2753_);
                    v___x_2755_ = l_Repr_addAppParen(v___x_2754_, v___x_2748_);
                    v___y_2727_ = v___x_2755_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                lean_inc(v___y_2707_);
                if v_isShared_2705_ == 0 {
                    lean_ctor_set_tag(v___x_2704_, 4);
                    lean_ctor_set(v___x_2704_, 1, v___y_2710_);
                    lean_ctor_set(v___x_2704_, 0, v___y_2707_);
                    v___x_2712_ = v___x_2704_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2722_ = lean_alloc_ctor(4, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2722_, 0, v___y_2707_);
                    lean_ctor_set(v_reuseFailAlloc_2722_, 1, v___y_2710_);
                    v___x_2712_ = v_reuseFailAlloc_2722_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2713_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2713_, 0, v___x_2712_);
                lean_ctor_set_uint8(
                    v___x_2713_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___y_2709_,
                );
                v___x_2714_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2714_, 0, v___y_2708_);
                lean_ctor_set(v___x_2714_, 1, v___x_2713_);
                v___x_2715_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25,
                );
                v___x_2716_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26;
                v___x_2717_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2717_, 0, v___x_2716_);
                lean_ctor_set(v___x_2717_, 1, v___x_2714_);
                v___x_2718_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27;
                v___x_2719_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2719_, 0, v___x_2717_);
                lean_ctor_set(v___x_2719_, 1, v___x_2718_);
                v___x_2720_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2720_, 0, v___x_2715_);
                lean_ctor_set(v___x_2720_, 1, v___x_2719_);
                v___x_2721_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2721_, 0, v___x_2720_);
                lean_ctor_set_uint8(
                    v___x_2721_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___y_2709_,
                );
                return v___x_2721_;
            }
            4 => {
                v___x_2728_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2728_, 0, v___x_2725_);
                lean_ctor_set(v___x_2728_, 1, v___y_2727_);
                v___x_2729_ = 0;
                v___x_2730_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2730_, 0, v___x_2728_);
                lean_ctor_set_uint8(
                    v___x_2730_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2729_,
                );
                v___x_2731_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2731_, 0, v___x_2724_);
                lean_ctor_set(v___x_2731_, 1, v___x_2730_);
                v___x_2732_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9;
                v___x_2733_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2733_, 0, v___x_2731_);
                lean_ctor_set(v___x_2733_, 1, v___x_2732_);
                v___x_2734_ = lean_box(1);
                v___x_2735_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2735_, 0, v___x_2733_);
                lean_ctor_set(v___x_2735_, 1, v___x_2734_);
                v___x_2736_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__6;
                v___x_2737_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2737_, 0, v___x_2735_);
                lean_ctor_set(v___x_2737_, 1, v___x_2736_);
                v___x_2738_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2738_, 0, v___x_2737_);
                lean_ctor_set(v___x_2738_, 1, v___x_2723_);
                v___x_2739_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7_once
                    ),
                    _init_l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg___closed__7,
                );
                v___x_2740_ = lean_unsigned_to_nat(0);
                v___x_2741_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11), core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once), _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
                v___x_2742_ = lean_int_dec_lt(v_correction_2702_, v___x_2741_);
                if v___x_2742_ == 0 {
                    v___x_2743_ = l_Int_repr(v_correction_2702_);
                    lean_dec(v_correction_2702_);
                    v___x_2744_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2744_, 0, v___x_2743_);
                    v___y_2707_ = v___x_2739_;
                    v___y_2708_ = v___x_2738_;
                    v___y_2709_ = v___x_2729_;
                    v___y_2710_ = v___x_2744_;
                    state = 2;
                    continue;
                } else {
                    v___x_2745_ = l_Int_repr(v_correction_2702_);
                    lean_dec(v_correction_2702_);
                    v___x_2746_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2746_, 0, v___x_2745_);
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
    mut v_x_2757_: *mut LeanObject,
    mut v_prec_2758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    v___x_2759_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_x_2757_);
    return v___x_2759_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___boxed(
    mut v_x_2760_: *mut LeanObject,
    mut v_prec_2761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2762_: *mut LeanObject = core::ptr::null_mut();
    v_res_2762_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr(v_x_2760_, v_prec_2761_);
    lean_dec(v_prec_2761_);
    return v_res_2762_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default___closed__0()
-> *mut LeanObject {
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    v___x_2765_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11
        ),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11,
    );
    v___x_2766_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2766_, 0, v___x_2765_);
    lean_ctor_set(v___x_2766_, 1, v___x_2765_);
    return v___x_2766_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default() -> *mut LeanObject {
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    v___x_2767_ = lean_obj_once(
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
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond() -> *mut LeanObject {
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    v___x_2768_ = l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default;
    return v___x_2768_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10_spec__16_spec__22(
    mut v_x_2769_: *mut LeanObject,
    mut v_x_2770_: *mut LeanObject,
    mut v_x_2771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2776_: u8 = 0;
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: u8 = 0;
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2784_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2771_) == 0 {
                    lean_dec(v_x_2769_);
                    return v_x_2770_;
                } else {
                    v_head_2772_ = lean_ctor_get(v_x_2771_, 0);
                    v_tail_2773_ = lean_ctor_get(v_x_2771_, 1);
                    v_isSharedCheck_2784_ = (!lean_is_exclusive(v_x_2771_)) as u8;
                    if v_isSharedCheck_2784_ == 0 {
                        v___x_2775_ = v_x_2771_;
                        v_isShared_2776_ = v_isSharedCheck_2784_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2773_);
                        lean_inc(v_head_2772_);
                        lean_dec(v_x_2771_);
                        v___x_2775_ = lean_box(0);
                        v_isShared_2776_ = v_isSharedCheck_2784_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2769_);
                if v_isShared_2776_ == 0 {
                    lean_ctor_set_tag(v___x_2775_, 5);
                    lean_ctor_set(v___x_2775_, 1, v_x_2769_);
                    lean_ctor_set(v___x_2775_, 0, v_x_2770_);
                    v___x_2778_ = v___x_2775_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2783_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_x_2770_);
                    lean_ctor_set(v_reuseFailAlloc_2783_, 1, v_x_2769_);
                    v___x_2778_ = v_reuseFailAlloc_2783_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2779_ = (lean_unbox(v_head_2772_) as u8);
                lean_dec(v_head_2772_);
                v___x_2780_ = l_Bool_repr___redArg(v___x_2779_);
                v___x_2781_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2781_, 0, v___x_2778_);
                lean_ctor_set(v___x_2781_, 1, v___x_2780_);
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
    mut v_x_2785_: *mut LeanObject,
    mut v_x_2786_: *mut LeanObject,
    mut v_x_2787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2792_: u8 = 0;
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: u8 = 0;
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2800_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2787_) == 0 {
                    lean_dec(v_x_2785_);
                    return v_x_2786_;
                } else {
                    v_head_2788_ = lean_ctor_get(v_x_2787_, 0);
                    v_tail_2789_ = lean_ctor_get(v_x_2787_, 1);
                    v_isSharedCheck_2800_ = (!lean_is_exclusive(v_x_2787_)) as u8;
                    if v_isSharedCheck_2800_ == 0 {
                        v___x_2791_ = v_x_2787_;
                        v_isShared_2792_ = v_isSharedCheck_2800_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2789_);
                        lean_inc(v_head_2788_);
                        lean_dec(v_x_2787_);
                        v___x_2791_ = lean_box(0);
                        v_isShared_2792_ = v_isSharedCheck_2800_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2785_);
                if v_isShared_2792_ == 0 {
                    lean_ctor_set_tag(v___x_2791_, 5);
                    lean_ctor_set(v___x_2791_, 1, v_x_2785_);
                    lean_ctor_set(v___x_2791_, 0, v_x_2786_);
                    v___x_2794_ = v___x_2791_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2799_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_x_2786_);
                    lean_ctor_set(v_reuseFailAlloc_2799_, 1, v_x_2785_);
                    v___x_2794_ = v_reuseFailAlloc_2799_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2795_ = (lean_unbox(v_head_2788_) as u8);
                lean_dec(v_head_2788_);
                v___x_2796_ = l_Bool_repr___redArg(v___x_2795_);
                v___x_2797_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2797_, 0, v___x_2794_);
                lean_ctor_set(v___x_2797_, 1, v___x_2796_);
                v___x_2798_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10_spec__16_spec__22(v_x_2785_, v___x_2797_, v_tail_2789_);
                return v___x_2798_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10(
    mut v_x_2801_: *mut LeanObject,
    mut v_x_2802_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2801_) == 0 {
        let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2802_);
        v___x_2803_ = lean_box(0);
        return v___x_2803_;
    } else {
        let mut v_tail_2804_: *mut LeanObject = core::ptr::null_mut();
        v_tail_2804_ = lean_ctor_get(v_x_2801_, 1);
        if lean_obj_tag(v_tail_2804_) == 0 {
            let mut v_head_2805_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2806_: u8 = 0;
            let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_2802_);
            v_head_2805_ = lean_ctor_get(v_x_2801_, 0);
            lean_inc(v_head_2805_);
            lean_dec_ref_known(v_x_2801_, 2);
            v___x_2806_ = (lean_unbox(v_head_2805_) as u8);
            lean_dec(v_head_2805_);
            v___x_2807_ = l_Bool_repr___redArg(v___x_2806_);
            return v___x_2807_;
        } else {
            let mut v_head_2808_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2809_: u8 = 0;
            let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_2804_);
            v_head_2808_ = lean_ctor_get(v_x_2801_, 0);
            lean_inc(v_head_2808_);
            lean_dec_ref_known(v_x_2801_, 2);
            v___x_2809_ = (lean_unbox(v_head_2808_) as u8);
            lean_dec(v_head_2808_);
            v___x_2810_ = l_Bool_repr___redArg(v___x_2809_);
            v___x_2811_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10_spec__16(v_x_2802_, v___x_2810_, v_tail_2804_);
            return v___x_2811_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3()
-> *mut LeanObject {
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    v___x_2817_ =
        l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__0;
    v___x_2818_ = lean_string_length(v___x_2817_);
    return v___x_2818_;
}
pub unsafe fn _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4()
-> *mut LeanObject {
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    v___x_2819_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3_once), _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__3);
    v___x_2820_ = lean_nat_to_int(v___x_2819_);
    return v___x_2820_;
}
pub unsafe fn l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5(
    mut v_xs_2828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: u8 = 0;
    v___x_2829_ = lean_array_get_size(v_xs_2828_);
    v___x_2830_ = lean_unsigned_to_nat(0);
    v___x_2831_ = lean_nat_dec_eq(v___x_2829_, v___x_2830_);
    if v___x_2831_ == 0 {
        let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
        v___x_2832_ = lean_array_to_list(v_xs_2828_);
        v___x_2833_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1;
        v___x_2834_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5_spec__10(v___x_2832_, v___x_2833_);
        v___x_2835_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once), _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
        v___x_2836_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5;
        v___x_2837_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2837_, 0, v___x_2836_);
        lean_ctor_set(v___x_2837_, 1, v___x_2834_);
        v___x_2838_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6;
        v___x_2839_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2839_, 0, v___x_2837_);
        lean_ctor_set(v___x_2839_, 1, v___x_2838_);
        v___x_2840_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_2840_, 0, v___x_2835_);
        lean_ctor_set(v___x_2840_, 1, v___x_2839_);
        v___x_2841_ = l_Std_Format_fill(v___x_2840_);
        return v___x_2841_;
    } else {
        let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_2828_);
        v___x_2842_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8;
        return v___x_2842_;
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6___lam__0(
    mut v___y_2843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    v___x_2844_ = l_String_quote(v___y_2843_);
    v___x_2845_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2845_, 0, v___x_2844_);
    return v___x_2845_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6_spec__10_spec__16(
    mut v_x_2846_: *mut LeanObject,
    mut v_x_2847_: *mut LeanObject,
    mut v_x_2848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2853_: u8 = 0;
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2848_) == 0 {
                    lean_dec(v_x_2846_);
                    return v_x_2847_;
                } else {
                    v_head_2849_ = lean_ctor_get(v_x_2848_, 0);
                    v_tail_2850_ = lean_ctor_get(v_x_2848_, 1);
                    v_isSharedCheck_2861_ = (!lean_is_exclusive(v_x_2848_)) as u8;
                    if v_isSharedCheck_2861_ == 0 {
                        v___x_2852_ = v_x_2848_;
                        v_isShared_2853_ = v_isSharedCheck_2861_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2850_);
                        lean_inc(v_head_2849_);
                        lean_dec(v_x_2848_);
                        v___x_2852_ = lean_box(0);
                        v_isShared_2853_ = v_isSharedCheck_2861_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2846_);
                if v_isShared_2853_ == 0 {
                    lean_ctor_set_tag(v___x_2852_, 5);
                    lean_ctor_set(v___x_2852_, 1, v_x_2846_);
                    lean_ctor_set(v___x_2852_, 0, v_x_2847_);
                    v___x_2855_ = v___x_2852_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2860_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_x_2847_);
                    lean_ctor_set(v_reuseFailAlloc_2860_, 1, v_x_2846_);
                    v___x_2855_ = v_reuseFailAlloc_2860_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2856_ = l_String_quote(v_head_2849_);
                v___x_2857_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2857_, 0, v___x_2856_);
                v___x_2858_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2858_, 0, v___x_2855_);
                lean_ctor_set(v___x_2858_, 1, v___x_2857_);
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
    mut v_x_2862_: *mut LeanObject,
    mut v_x_2863_: *mut LeanObject,
    mut v_x_2864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2869_: u8 = 0;
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2877_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2864_) == 0 {
                    lean_dec(v_x_2862_);
                    return v_x_2863_;
                } else {
                    v_head_2865_ = lean_ctor_get(v_x_2864_, 0);
                    v_tail_2866_ = lean_ctor_get(v_x_2864_, 1);
                    v_isSharedCheck_2877_ = (!lean_is_exclusive(v_x_2864_)) as u8;
                    if v_isSharedCheck_2877_ == 0 {
                        v___x_2868_ = v_x_2864_;
                        v_isShared_2869_ = v_isSharedCheck_2877_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2866_);
                        lean_inc(v_head_2865_);
                        lean_dec(v_x_2864_);
                        v___x_2868_ = lean_box(0);
                        v_isShared_2869_ = v_isSharedCheck_2877_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2862_);
                if v_isShared_2869_ == 0 {
                    lean_ctor_set_tag(v___x_2868_, 5);
                    lean_ctor_set(v___x_2868_, 1, v_x_2862_);
                    lean_ctor_set(v___x_2868_, 0, v_x_2863_);
                    v___x_2871_ = v___x_2868_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2876_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_x_2863_);
                    lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_x_2862_);
                    v___x_2871_ = v_reuseFailAlloc_2876_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2872_ = l_String_quote(v_head_2865_);
                v___x_2873_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2873_, 0, v___x_2872_);
                v___x_2874_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2874_, 0, v___x_2871_);
                lean_ctor_set(v___x_2874_, 1, v___x_2873_);
                v___x_2875_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6_spec__10_spec__16(v_x_2862_, v___x_2874_, v_tail_2866_);
                return v___x_2875_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6(
    mut v_x_2878_: *mut LeanObject,
    mut v_x_2879_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2878_) == 0 {
        let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2879_);
        v___x_2880_ = lean_box(0);
        return v___x_2880_;
    } else {
        let mut v_tail_2881_: *mut LeanObject = core::ptr::null_mut();
        v_tail_2881_ = lean_ctor_get(v_x_2878_, 1);
        if lean_obj_tag(v_tail_2881_) == 0 {
            let mut v_head_2882_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_2879_);
            v_head_2882_ = lean_ctor_get(v_x_2878_, 0);
            lean_inc(v_head_2882_);
            lean_dec_ref_known(v_x_2878_, 2);
            v___x_2883_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6___lam__0(v_head_2882_);
            return v___x_2883_;
        } else {
            let mut v_head_2884_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_2881_);
            v_head_2884_ = lean_ctor_get(v_x_2878_, 0);
            lean_inc(v_head_2884_);
            lean_dec_ref_known(v_x_2878_, 2);
            v___x_2885_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6___lam__0(v_head_2884_);
            v___x_2886_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6_spec__10(v_x_2879_, v___x_2885_, v_tail_2881_);
            return v___x_2886_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3(
    mut v_xs_2887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: u8 = 0;
    v___x_2888_ = lean_array_get_size(v_xs_2887_);
    v___x_2889_ = lean_unsigned_to_nat(0);
    v___x_2890_ = lean_nat_dec_eq(v___x_2888_, v___x_2889_);
    if v___x_2890_ == 0 {
        let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
        v___x_2891_ = lean_array_to_list(v_xs_2887_);
        v___x_2892_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1;
        v___x_2893_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3_spec__6(v___x_2891_, v___x_2892_);
        v___x_2894_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once), _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
        v___x_2895_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5;
        v___x_2896_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2896_, 0, v___x_2895_);
        lean_ctor_set(v___x_2896_, 1, v___x_2893_);
        v___x_2897_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6;
        v___x_2898_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2898_, 0, v___x_2896_);
        lean_ctor_set(v___x_2898_, 1, v___x_2897_);
        v___x_2899_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_2899_, 0, v___x_2894_);
        lean_ctor_set(v___x_2899_, 1, v___x_2898_);
        v___x_2900_ = l_Std_Format_fill(v___x_2899_);
        return v___x_2900_;
    } else {
        let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_2887_);
        v___x_2901_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8;
        return v___x_2901_;
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2_spec__4_spec__10(
    mut v_x_2902_: *mut LeanObject,
    mut v_x_2903_: *mut LeanObject,
    mut v_x_2904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2909_: u8 = 0;
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: u8 = 0;
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2919_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2904_) == 0 {
                    lean_dec(v_x_2902_);
                    return v_x_2903_;
                } else {
                    v_head_2905_ = lean_ctor_get(v_x_2904_, 0);
                    v_tail_2906_ = lean_ctor_get(v_x_2904_, 1);
                    v_isSharedCheck_2919_ = (!lean_is_exclusive(v_x_2904_)) as u8;
                    if v_isSharedCheck_2919_ == 0 {
                        v___x_2908_ = v_x_2904_;
                        v_isShared_2909_ = v_isSharedCheck_2919_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2906_);
                        lean_inc(v_head_2905_);
                        lean_dec(v_x_2904_);
                        v___x_2908_ = lean_box(0);
                        v_isShared_2909_ = v_isSharedCheck_2919_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2902_);
                if v_isShared_2909_ == 0 {
                    lean_ctor_set_tag(v___x_2908_, 5);
                    lean_ctor_set(v___x_2908_, 1, v_x_2902_);
                    lean_ctor_set(v___x_2908_, 0, v_x_2903_);
                    v___x_2911_ = v___x_2908_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2918_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_x_2903_);
                    lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_x_2902_);
                    v___x_2911_ = v_reuseFailAlloc_2918_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2912_ = (lean_unbox(v_head_2905_) as u8);
                lean_dec(v_head_2905_);
                v___x_2913_ = lean_uint8_to_nat(v___x_2912_);
                v___x_2914_ = l_Nat_reprFast(v___x_2913_);
                v___x_2915_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2915_, 0, v___x_2914_);
                v___x_2916_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2916_, 0, v___x_2911_);
                lean_ctor_set(v___x_2916_, 1, v___x_2915_);
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
    mut v_x_2920_: *mut LeanObject,
    mut v_x_2921_: *mut LeanObject,
    mut v_x_2922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2927_: u8 = 0;
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: u8 = 0;
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2937_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2922_) == 0 {
                    lean_dec(v_x_2920_);
                    return v_x_2921_;
                } else {
                    v_head_2923_ = lean_ctor_get(v_x_2922_, 0);
                    v_tail_2924_ = lean_ctor_get(v_x_2922_, 1);
                    v_isSharedCheck_2937_ = (!lean_is_exclusive(v_x_2922_)) as u8;
                    if v_isSharedCheck_2937_ == 0 {
                        v___x_2926_ = v_x_2922_;
                        v_isShared_2927_ = v_isSharedCheck_2937_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2924_);
                        lean_inc(v_head_2923_);
                        lean_dec(v_x_2922_);
                        v___x_2926_ = lean_box(0);
                        v_isShared_2927_ = v_isSharedCheck_2937_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2920_);
                if v_isShared_2927_ == 0 {
                    lean_ctor_set_tag(v___x_2926_, 5);
                    lean_ctor_set(v___x_2926_, 1, v_x_2920_);
                    lean_ctor_set(v___x_2926_, 0, v_x_2921_);
                    v___x_2929_ = v___x_2926_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2936_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_x_2921_);
                    lean_ctor_set(v_reuseFailAlloc_2936_, 1, v_x_2920_);
                    v___x_2929_ = v_reuseFailAlloc_2936_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2930_ = (lean_unbox(v_head_2923_) as u8);
                lean_dec(v_head_2923_);
                v___x_2931_ = lean_uint8_to_nat(v___x_2930_);
                v___x_2932_ = l_Nat_reprFast(v___x_2931_);
                v___x_2933_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2933_, 0, v___x_2932_);
                v___x_2934_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2934_, 0, v___x_2929_);
                lean_ctor_set(v___x_2934_, 1, v___x_2933_);
                v___x_2935_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2_spec__4_spec__10(v_x_2920_, v___x_2934_, v_tail_2924_);
                return v___x_2935_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(
    mut v___y_2938_: u8,
) -> *mut LeanObject {
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    v___x_2939_ = lean_uint8_to_nat(v___y_2938_);
    v___x_2940_ = l_Nat_reprFast(v___x_2939_);
    v___x_2941_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2941_, 0, v___x_2940_);
    return v___x_2941_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0___boxed(
    mut v___y_2942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1967__boxed_2943_: u8 = 0;
    let mut v_res_2944_: *mut LeanObject = core::ptr::null_mut();
    v___y_1967__boxed_2943_ = (lean_unbox(v___y_2942_) as u8);
    v_res_2944_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(v___y_1967__boxed_2943_);
    return v_res_2944_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2(
    mut v_x_2945_: *mut LeanObject,
    mut v_x_2946_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2945_) == 0 {
        let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2946_);
        v___x_2947_ = lean_box(0);
        return v___x_2947_;
    } else {
        let mut v_tail_2948_: *mut LeanObject = core::ptr::null_mut();
        v_tail_2948_ = lean_ctor_get(v_x_2945_, 1);
        if lean_obj_tag(v_tail_2948_) == 0 {
            let mut v_head_2949_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2950_: u8 = 0;
            let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_2946_);
            v_head_2949_ = lean_ctor_get(v_x_2945_, 0);
            lean_inc(v_head_2949_);
            lean_dec_ref_known(v_x_2945_, 2);
            v___x_2950_ = (lean_unbox(v_head_2949_) as u8);
            lean_dec(v_head_2949_);
            v___x_2951_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(v___x_2950_);
            return v___x_2951_;
        } else {
            let mut v_head_2952_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2953_: u8 = 0;
            let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_2948_);
            v_head_2952_ = lean_ctor_get(v_x_2945_, 0);
            lean_inc(v_head_2952_);
            lean_dec_ref_known(v_x_2945_, 2);
            v___x_2953_ = (lean_unbox(v_head_2952_) as u8);
            lean_dec(v_head_2952_);
            v___x_2954_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2___lam__0(v___x_2953_);
            v___x_2955_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2_spec__4(v_x_2946_, v___x_2954_, v_tail_2948_);
            return v___x_2955_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1(
    mut v_xs_2956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: u8 = 0;
    v___x_2957_ = lean_array_get_size(v_xs_2956_);
    v___x_2958_ = lean_unsigned_to_nat(0);
    v___x_2959_ = lean_nat_dec_eq(v___x_2957_, v___x_2958_);
    if v___x_2959_ == 0 {
        let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
        v___x_2960_ = lean_array_to_list(v_xs_2956_);
        v___x_2961_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1;
        v___x_2962_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__1_spec__2(v___x_2960_, v___x_2961_);
        v___x_2963_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once), _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
        v___x_2964_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5;
        v___x_2965_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2965_, 0, v___x_2964_);
        lean_ctor_set(v___x_2965_, 1, v___x_2962_);
        v___x_2966_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6;
        v___x_2967_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2967_, 0, v___x_2965_);
        lean_ctor_set(v___x_2967_, 1, v___x_2966_);
        v___x_2968_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_2968_, 0, v___x_2963_);
        lean_ctor_set(v___x_2968_, 1, v___x_2967_);
        v___x_2969_ = l_Std_Format_fill(v___x_2968_);
        return v___x_2969_;
    } else {
        let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_2956_);
        v___x_2970_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8;
        return v___x_2970_;
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1_spec__7(
    mut v_x_2971_: *mut LeanObject,
    mut v_x_2972_: *mut LeanObject,
    mut v_x_2973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2978_: u8 = 0;
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: u8 = 0;
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2994_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2973_) == 0 {
                    lean_dec(v_x_2971_);
                    return v_x_2972_;
                } else {
                    v_head_2974_ = lean_ctor_get(v_x_2973_, 0);
                    v_tail_2975_ = lean_ctor_get(v_x_2973_, 1);
                    v_isSharedCheck_2994_ = (!lean_is_exclusive(v_x_2973_)) as u8;
                    if v_isSharedCheck_2994_ == 0 {
                        v___x_2977_ = v_x_2973_;
                        v_isShared_2978_ = v_isSharedCheck_2994_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2975_);
                        lean_inc(v_head_2974_);
                        lean_dec(v_x_2973_);
                        v___x_2977_ = lean_box(0);
                        v_isShared_2978_ = v_isSharedCheck_2994_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2971_);
                if v_isShared_2978_ == 0 {
                    lean_ctor_set_tag(v___x_2977_, 5);
                    lean_ctor_set(v___x_2977_, 1, v_x_2971_);
                    lean_ctor_set(v___x_2977_, 0, v_x_2972_);
                    v___x_2980_ = v___x_2977_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2993_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_x_2972_);
                    lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_x_2971_);
                    v___x_2980_ = v_reuseFailAlloc_2993_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2981_ = lean_unsigned_to_nat(0);
                v___x_2982_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11), core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once), _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
                v___x_2983_ = lean_int_dec_lt(v_head_2974_, v___x_2982_);
                if v___x_2983_ == 0 {
                    v___x_2984_ = l_Int_repr(v_head_2974_);
                    lean_dec(v_head_2974_);
                    v___x_2985_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2985_, 0, v___x_2984_);
                    v___x_2986_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2986_, 0, v___x_2980_);
                    lean_ctor_set(v___x_2986_, 1, v___x_2985_);
                    v_x_2972_ = v___x_2986_;
                    v_x_2973_ = v_tail_2975_;
                    state = 0;
                    continue;
                } else {
                    v___x_2988_ = l_Int_repr(v_head_2974_);
                    lean_dec(v_head_2974_);
                    v___x_2989_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2989_, 0, v___x_2988_);
                    v___x_2990_ = l_Repr_addAppParen(v___x_2989_, v___x_2981_);
                    v___x_2991_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_2991_, 0, v___x_2980_);
                    lean_ctor_set(v___x_2991_, 1, v___x_2990_);
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
    mut v_x_2995_: *mut LeanObject,
    mut v_x_2996_: *mut LeanObject,
    mut v_x_2997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3002_: u8 = 0;
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: u8 = 0;
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3018_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2997_) == 0 {
                    lean_dec(v_x_2995_);
                    return v_x_2996_;
                } else {
                    v_head_2998_ = lean_ctor_get(v_x_2997_, 0);
                    v_tail_2999_ = lean_ctor_get(v_x_2997_, 1);
                    v_isSharedCheck_3018_ = (!lean_is_exclusive(v_x_2997_)) as u8;
                    if v_isSharedCheck_3018_ == 0 {
                        v___x_3001_ = v_x_2997_;
                        v_isShared_3002_ = v_isSharedCheck_3018_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2999_);
                        lean_inc(v_head_2998_);
                        lean_dec(v_x_2997_);
                        v___x_3001_ = lean_box(0);
                        v_isShared_3002_ = v_isSharedCheck_3018_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2995_);
                if v_isShared_3002_ == 0 {
                    lean_ctor_set_tag(v___x_3001_, 5);
                    lean_ctor_set(v___x_3001_, 1, v_x_2995_);
                    lean_ctor_set(v___x_3001_, 0, v_x_2996_);
                    v___x_3004_ = v___x_3001_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3017_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_x_2996_);
                    lean_ctor_set(v_reuseFailAlloc_3017_, 1, v_x_2995_);
                    v___x_3004_ = v_reuseFailAlloc_3017_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3005_ = lean_unsigned_to_nat(0);
                v___x_3006_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11), core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11_once), _init_l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg___closed__11);
                v___x_3007_ = lean_int_dec_lt(v_head_2998_, v___x_3006_);
                if v___x_3007_ == 0 {
                    v___x_3008_ = l_Int_repr(v_head_2998_);
                    lean_dec(v_head_2998_);
                    v___x_3009_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_3009_, 0, v___x_3008_);
                    v___x_3010_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_3010_, 0, v___x_3004_);
                    lean_ctor_set(v___x_3010_, 1, v___x_3009_);
                    v___x_3011_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1_spec__7(v_x_2995_, v___x_3010_, v_tail_2999_);
                    return v___x_3011_;
                } else {
                    v___x_3012_ = l_Int_repr(v_head_2998_);
                    lean_dec(v_head_2998_);
                    v___x_3013_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_3013_, 0, v___x_3012_);
                    v___x_3014_ = l_Repr_addAppParen(v___x_3013_, v___x_3005_);
                    v___x_3015_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_3015_, 0, v___x_3004_);
                    lean_ctor_set(v___x_3015_, 1, v___x_3014_);
                    v___x_3016_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1_spec__7(v_x_2995_, v___x_3015_, v_tail_2999_);
                    return v___x_3016_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(
    mut v___y_3019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: u8 = 0;
    v___x_3020_ = lean_unsigned_to_nat(0);
    v___x_3021_ = lean_obj_once(
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
        let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
        v___x_3023_ = l_Int_repr(v___y_3019_);
        v___x_3024_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_3024_, 0, v___x_3023_);
        return v___x_3024_;
    } else {
        let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
        v___x_3025_ = l_Int_repr(v___y_3019_);
        v___x_3026_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_3026_, 0, v___x_3025_);
        v___x_3027_ = l_Repr_addAppParen(v___x_3026_, v___x_3020_);
        return v___x_3027_;
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0___boxed(
    mut v___y_3028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3029_: *mut LeanObject = core::ptr::null_mut();
    v_res_3029_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(v___y_3028_);
    lean_dec(v___y_3028_);
    return v_res_3029_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0(
    mut v_x_3030_: *mut LeanObject,
    mut v_x_3031_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3030_) == 0 {
        let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_3031_);
        v___x_3032_ = lean_box(0);
        return v___x_3032_;
    } else {
        let mut v_tail_3033_: *mut LeanObject = core::ptr::null_mut();
        v_tail_3033_ = lean_ctor_get(v_x_3030_, 1);
        if lean_obj_tag(v_tail_3033_) == 0 {
            let mut v_head_3034_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_3031_);
            v_head_3034_ = lean_ctor_get(v_x_3030_, 0);
            lean_inc(v_head_3034_);
            lean_dec_ref_known(v_x_3030_, 2);
            v___x_3035_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(v_head_3034_);
            lean_dec(v_head_3034_);
            return v___x_3035_;
        } else {
            let mut v_head_3036_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_3033_);
            v_head_3036_ = lean_ctor_get(v_x_3030_, 0);
            lean_inc(v_head_3036_);
            lean_dec_ref_known(v_x_3030_, 2);
            v___x_3037_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0___lam__0(v_head_3036_);
            lean_dec(v_head_3036_);
            v___x_3038_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0_spec__1(v_x_3031_, v___x_3037_, v_tail_3033_);
            return v___x_3038_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0(
    mut v_xs_3039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: u8 = 0;
    v___x_3040_ = lean_array_get_size(v_xs_3039_);
    v___x_3041_ = lean_unsigned_to_nat(0);
    v___x_3042_ = lean_nat_dec_eq(v___x_3040_, v___x_3041_);
    if v___x_3042_ == 0 {
        let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
        v___x_3043_ = lean_array_to_list(v_xs_3039_);
        v___x_3044_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1;
        v___x_3045_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0_spec__0(v___x_3043_, v___x_3044_);
        v___x_3046_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once), _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
        v___x_3047_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5;
        v___x_3048_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_3048_, 0, v___x_3047_);
        lean_ctor_set(v___x_3048_, 1, v___x_3045_);
        v___x_3049_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6;
        v___x_3050_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_3050_, 0, v___x_3048_);
        lean_ctor_set(v___x_3050_, 1, v___x_3049_);
        v___x_3051_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_3051_, 0, v___x_3046_);
        lean_ctor_set(v___x_3051_, 1, v___x_3050_);
        v___x_3052_ = l_Std_Format_fill(v___x_3051_);
        return v___x_3052_;
    } else {
        let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_3039_);
        v___x_3053_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8;
        return v___x_3053_;
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7_spec__13(
    mut v_x_3054_: *mut LeanObject,
    mut v_x_3055_: *mut LeanObject,
    mut v_x_3056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3061_: u8 = 0;
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3056_) == 0 {
                    lean_dec(v_x_3054_);
                    return v_x_3055_;
                } else {
                    v_head_3057_ = lean_ctor_get(v_x_3056_, 0);
                    v_tail_3058_ = lean_ctor_get(v_x_3056_, 1);
                    v_isSharedCheck_3068_ = (!lean_is_exclusive(v_x_3056_)) as u8;
                    if v_isSharedCheck_3068_ == 0 {
                        v___x_3060_ = v_x_3056_;
                        v_isShared_3061_ = v_isSharedCheck_3068_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3058_);
                        lean_inc(v_head_3057_);
                        lean_dec(v_x_3056_);
                        v___x_3060_ = lean_box(0);
                        v_isShared_3061_ = v_isSharedCheck_3068_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_3054_);
                if v_isShared_3061_ == 0 {
                    lean_ctor_set_tag(v___x_3060_, 5);
                    lean_ctor_set(v___x_3060_, 1, v_x_3054_);
                    lean_ctor_set(v___x_3060_, 0, v_x_3055_);
                    v___x_3063_ = v___x_3060_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3067_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_x_3055_);
                    lean_ctor_set(v_reuseFailAlloc_3067_, 1, v_x_3054_);
                    v___x_3063_ = v_reuseFailAlloc_3067_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3064_ =
                    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_3057_);
                lean_dec(v_head_3057_);
                v___x_3065_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3065_, 0, v___x_3063_);
                lean_ctor_set(v___x_3065_, 1, v___x_3064_);
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
    mut v_x_3069_: *mut LeanObject,
    mut v_x_3070_: *mut LeanObject,
    mut v_x_3071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3076_: u8 = 0;
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3083_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3071_) == 0 {
                    lean_dec(v_x_3069_);
                    return v_x_3070_;
                } else {
                    v_head_3072_ = lean_ctor_get(v_x_3071_, 0);
                    v_tail_3073_ = lean_ctor_get(v_x_3071_, 1);
                    v_isSharedCheck_3083_ = (!lean_is_exclusive(v_x_3071_)) as u8;
                    if v_isSharedCheck_3083_ == 0 {
                        v___x_3075_ = v_x_3071_;
                        v_isShared_3076_ = v_isSharedCheck_3083_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3073_);
                        lean_inc(v_head_3072_);
                        lean_dec(v_x_3071_);
                        v___x_3075_ = lean_box(0);
                        v_isShared_3076_ = v_isSharedCheck_3083_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_3069_);
                if v_isShared_3076_ == 0 {
                    lean_ctor_set_tag(v___x_3075_, 5);
                    lean_ctor_set(v___x_3075_, 1, v_x_3069_);
                    lean_ctor_set(v___x_3075_, 0, v_x_3070_);
                    v___x_3078_ = v___x_3075_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3082_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_x_3070_);
                    lean_ctor_set(v_reuseFailAlloc_3082_, 1, v_x_3069_);
                    v___x_3078_ = v_reuseFailAlloc_3082_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3079_ =
                    l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_3072_);
                lean_dec(v_head_3072_);
                v___x_3080_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3080_, 0, v___x_3078_);
                lean_ctor_set(v___x_3080_, 1, v___x_3079_);
                v___x_3081_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7_spec__13(v_x_3069_, v___x_3080_, v_tail_3073_);
                return v___x_3081_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4(
    mut v_x_3084_: *mut LeanObject,
    mut v_x_3085_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3084_) == 0 {
        let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_3085_);
        v___x_3086_ = lean_box(0);
        return v___x_3086_;
    } else {
        let mut v_tail_3087_: *mut LeanObject = core::ptr::null_mut();
        v_tail_3087_ = lean_ctor_get(v_x_3084_, 1);
        if lean_obj_tag(v_tail_3087_) == 0 {
            let mut v_head_3088_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_3085_);
            v_head_3088_ = lean_ctor_get(v_x_3084_, 0);
            lean_inc(v_head_3088_);
            lean_dec_ref_known(v_x_3084_, 2);
            v___x_3089_ =
                l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_3088_);
            lean_dec(v_head_3088_);
            return v___x_3089_;
        } else {
            let mut v_head_3090_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_3087_);
            v_head_3090_ = lean_ctor_get(v_x_3084_, 0);
            lean_inc(v_head_3090_);
            lean_dec_ref_known(v_x_3084_, 2);
            v___x_3091_ =
                l_Std_Time_TimeZone_TZif_instReprLocalTimeType_repr___redArg(v_head_3090_);
            lean_dec(v_head_3090_);
            v___x_3092_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4_spec__7(v_x_3085_, v___x_3091_, v_tail_3087_);
            return v___x_3092_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2(
    mut v_xs_3093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: u8 = 0;
    v___x_3094_ = lean_array_get_size(v_xs_3093_);
    v___x_3095_ = lean_unsigned_to_nat(0);
    v___x_3096_ = lean_nat_dec_eq(v___x_3094_, v___x_3095_);
    if v___x_3096_ == 0 {
        let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
        v___x_3097_ = lean_array_to_list(v_xs_3093_);
        v___x_3098_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1;
        v___x_3099_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__2_spec__4(v___x_3097_, v___x_3098_);
        v___x_3100_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once), _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
        v___x_3101_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5;
        v___x_3102_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_3102_, 0, v___x_3101_);
        lean_ctor_set(v___x_3102_, 1, v___x_3099_);
        v___x_3103_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6;
        v___x_3104_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_3104_, 0, v___x_3102_);
        lean_ctor_set(v___x_3104_, 1, v___x_3103_);
        v___x_3105_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_3105_, 0, v___x_3100_);
        lean_ctor_set(v___x_3105_, 1, v___x_3104_);
        v___x_3106_ = l_Std_Format_fill(v___x_3105_);
        return v___x_3106_;
    } else {
        let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_3093_);
        v___x_3107_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8;
        return v___x_3107_;
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13_spec__19(
    mut v_x_3108_: *mut LeanObject,
    mut v_x_3109_: *mut LeanObject,
    mut v_x_3110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3115_: u8 = 0;
    let mut v___x_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3122_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3110_) == 0 {
                    lean_dec(v_x_3108_);
                    return v_x_3109_;
                } else {
                    v_head_3111_ = lean_ctor_get(v_x_3110_, 0);
                    v_tail_3112_ = lean_ctor_get(v_x_3110_, 1);
                    v_isSharedCheck_3122_ = (!lean_is_exclusive(v_x_3110_)) as u8;
                    if v_isSharedCheck_3122_ == 0 {
                        v___x_3114_ = v_x_3110_;
                        v_isShared_3115_ = v_isSharedCheck_3122_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3112_);
                        lean_inc(v_head_3111_);
                        lean_dec(v_x_3110_);
                        v___x_3114_ = lean_box(0);
                        v_isShared_3115_ = v_isSharedCheck_3122_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_3108_);
                if v_isShared_3115_ == 0 {
                    lean_ctor_set_tag(v___x_3114_, 5);
                    lean_ctor_set(v___x_3114_, 1, v_x_3108_);
                    lean_ctor_set(v___x_3114_, 0, v_x_3109_);
                    v___x_3117_ = v___x_3114_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3121_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_x_3109_);
                    lean_ctor_set(v_reuseFailAlloc_3121_, 1, v_x_3108_);
                    v___x_3117_ = v_reuseFailAlloc_3121_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3118_ =
                    l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_3111_);
                v___x_3119_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3119_, 0, v___x_3117_);
                lean_ctor_set(v___x_3119_, 1, v___x_3118_);
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
    mut v_x_3123_: *mut LeanObject,
    mut v_x_3124_: *mut LeanObject,
    mut v_x_3125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3130_: u8 = 0;
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3137_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3125_) == 0 {
                    lean_dec(v_x_3123_);
                    return v_x_3124_;
                } else {
                    v_head_3126_ = lean_ctor_get(v_x_3125_, 0);
                    v_tail_3127_ = lean_ctor_get(v_x_3125_, 1);
                    v_isSharedCheck_3137_ = (!lean_is_exclusive(v_x_3125_)) as u8;
                    if v_isSharedCheck_3137_ == 0 {
                        v___x_3129_ = v_x_3125_;
                        v_isShared_3130_ = v_isSharedCheck_3137_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3127_);
                        lean_inc(v_head_3126_);
                        lean_dec(v_x_3125_);
                        v___x_3129_ = lean_box(0);
                        v_isShared_3130_ = v_isSharedCheck_3137_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_3123_);
                if v_isShared_3130_ == 0 {
                    lean_ctor_set_tag(v___x_3129_, 5);
                    lean_ctor_set(v___x_3129_, 1, v_x_3123_);
                    lean_ctor_set(v___x_3129_, 0, v_x_3124_);
                    v___x_3132_ = v___x_3129_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3136_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_x_3124_);
                    lean_ctor_set(v_reuseFailAlloc_3136_, 1, v_x_3123_);
                    v___x_3132_ = v_reuseFailAlloc_3136_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3133_ =
                    l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_3126_);
                v___x_3134_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3134_, 0, v___x_3132_);
                lean_ctor_set(v___x_3134_, 1, v___x_3133_);
                v___x_3135_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13_spec__19(v_x_3123_, v___x_3134_, v_tail_3127_);
                return v___x_3135_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8(
    mut v_x_3138_: *mut LeanObject,
    mut v_x_3139_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3138_) == 0 {
        let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_3139_);
        v___x_3140_ = lean_box(0);
        return v___x_3140_;
    } else {
        let mut v_tail_3141_: *mut LeanObject = core::ptr::null_mut();
        v_tail_3141_ = lean_ctor_get(v_x_3138_, 1);
        if lean_obj_tag(v_tail_3141_) == 0 {
            let mut v_head_3142_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_3139_);
            v_head_3142_ = lean_ctor_get(v_x_3138_, 0);
            lean_inc(v_head_3142_);
            lean_dec_ref_known(v_x_3138_, 2);
            v___x_3143_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_3142_);
            return v___x_3143_;
        } else {
            let mut v_head_3144_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_3141_);
            v_head_3144_ = lean_ctor_get(v_x_3138_, 0);
            lean_inc(v_head_3144_);
            lean_dec_ref_known(v_x_3138_, 2);
            v___x_3145_ = l_Std_Time_TimeZone_TZif_instReprLeapSecond_repr___redArg(v_head_3144_);
            v___x_3146_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8_spec__13(v_x_3139_, v___x_3145_, v_tail_3141_);
            return v___x_3146_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4(
    mut v_xs_3147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: u8 = 0;
    v___x_3148_ = lean_array_get_size(v_xs_3147_);
    v___x_3149_ = lean_unsigned_to_nat(0);
    v___x_3150_ = lean_nat_dec_eq(v___x_3148_, v___x_3149_);
    if v___x_3150_ == 0 {
        let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
        v___x_3151_ = lean_array_to_list(v_xs_3147_);
        v___x_3152_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__1;
        v___x_3153_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4_spec__8(v___x_3151_, v___x_3152_);
        v___x_3154_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4_once), _init_l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__4);
        v___x_3155_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__5;
        v___x_3156_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_3156_, 0, v___x_3155_);
        lean_ctor_set(v___x_3156_, 1, v___x_3153_);
        v___x_3157_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__6;
        v___x_3158_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_3158_, 0, v___x_3156_);
        lean_ctor_set(v___x_3158_, 1, v___x_3157_);
        v___x_3159_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_3159_, 0, v___x_3154_);
        lean_ctor_set(v___x_3159_, 1, v___x_3158_);
        v___x_3160_ = l_Std_Format_fill(v___x_3159_);
        return v___x_3160_;
    } else {
        let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_3147_);
        v___x_3161_ =
            l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5___closed__8;
        return v___x_3161_;
    }
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    v___x_3171_ = lean_unsigned_to_nat(10);
    v___x_3172_ = lean_nat_to_int(v___x_3171_);
    return v___x_3172_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    v___x_3176_ = lean_unsigned_to_nat(19);
    v___x_3177_ = lean_nat_to_int(v___x_3176_);
    return v___x_3177_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14()
-> *mut LeanObject {
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    v___x_3187_ = lean_unsigned_to_nat(17);
    v___x_3188_ = lean_nat_to_int(v___x_3187_);
    return v___x_3188_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    v___x_3192_ = lean_unsigned_to_nat(15);
    v___x_3193_ = lean_nat_to_int(v___x_3192_);
    return v___x_3193_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(
    mut v_x_3200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_header_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transitionTimes_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transitionIndices_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localTimeTypes_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abbreviations_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leapSeconds_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stdWallIndicators_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_utLocalIndicators_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: u8 = 0;
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    v_header_3201_ = lean_ctor_get(v_x_3200_, 0);
    lean_inc_ref(v_header_3201_);
    v_transitionTimes_3202_ = lean_ctor_get(v_x_3200_, 1);
    lean_inc_ref(v_transitionTimes_3202_);
    v_transitionIndices_3203_ = lean_ctor_get(v_x_3200_, 2);
    lean_inc_ref(v_transitionIndices_3203_);
    v_localTimeTypes_3204_ = lean_ctor_get(v_x_3200_, 3);
    lean_inc_ref(v_localTimeTypes_3204_);
    v_abbreviations_3205_ = lean_ctor_get(v_x_3200_, 4);
    lean_inc_ref(v_abbreviations_3205_);
    v_leapSeconds_3206_ = lean_ctor_get(v_x_3200_, 5);
    lean_inc_ref(v_leapSeconds_3206_);
    v_stdWallIndicators_3207_ = lean_ctor_get(v_x_3200_, 6);
    lean_inc_ref(v_stdWallIndicators_3207_);
    v_utLocalIndicators_3208_ = lean_ctor_get(v_x_3200_, 7);
    lean_inc_ref(v_utLocalIndicators_3208_);
    lean_dec_ref(v_x_3200_);
    v___x_3209_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5;
    v___x_3210_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__3;
    v___x_3211_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__4,
    );
    v___x_3212_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg(v_header_3201_);
    lean_dec_ref(v_header_3201_);
    v___x_3213_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3213_, 0, v___x_3211_);
    lean_ctor_set(v___x_3213_, 1, v___x_3212_);
    v___x_3214_ = 0;
    v___x_3215_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3215_, 0, v___x_3213_);
    lean_ctor_set_uint8(
        v___x_3215_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3214_,
    );
    v___x_3216_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3216_, 0, v___x_3210_);
    lean_ctor_set(v___x_3216_, 1, v___x_3215_);
    v___x_3217_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9;
    v___x_3218_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3218_, 0, v___x_3216_);
    lean_ctor_set(v___x_3218_, 1, v___x_3217_);
    v___x_3219_ = lean_box(1);
    v___x_3220_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3220_, 0, v___x_3218_);
    lean_ctor_set(v___x_3220_, 1, v___x_3219_);
    v___x_3221_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__6;
    v___x_3222_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3222_, 0, v___x_3220_);
    lean_ctor_set(v___x_3222_, 1, v___x_3221_);
    v___x_3223_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3223_, 0, v___x_3222_);
    lean_ctor_set(v___x_3223_, 1, v___x_3209_);
    v___x_3224_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__7,
    );
    v___x_3225_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__0(
        v_transitionTimes_3202_,
    );
    v___x_3226_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3226_, 0, v___x_3224_);
    lean_ctor_set(v___x_3226_, 1, v___x_3225_);
    v___x_3227_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3227_, 0, v___x_3226_);
    lean_ctor_set_uint8(
        v___x_3227_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3214_,
    );
    v___x_3228_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3228_, 0, v___x_3223_);
    lean_ctor_set(v___x_3228_, 1, v___x_3227_);
    v___x_3229_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3229_, 0, v___x_3228_);
    lean_ctor_set(v___x_3229_, 1, v___x_3217_);
    v___x_3230_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3230_, 0, v___x_3229_);
    lean_ctor_set(v___x_3230_, 1, v___x_3219_);
    v___x_3231_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__9;
    v___x_3232_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3232_, 0, v___x_3230_);
    lean_ctor_set(v___x_3232_, 1, v___x_3231_);
    v___x_3233_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3233_, 0, v___x_3232_);
    lean_ctor_set(v___x_3233_, 1, v___x_3209_);
    v___x_3234_ = lean_obj_once(
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
    v___x_3236_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3236_, 0, v___x_3234_);
    lean_ctor_set(v___x_3236_, 1, v___x_3235_);
    v___x_3237_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3237_, 0, v___x_3236_);
    lean_ctor_set_uint8(
        v___x_3237_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3214_,
    );
    v___x_3238_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3238_, 0, v___x_3233_);
    lean_ctor_set(v___x_3238_, 1, v___x_3237_);
    v___x_3239_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3239_, 0, v___x_3238_);
    lean_ctor_set(v___x_3239_, 1, v___x_3217_);
    v___x_3240_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3240_, 0, v___x_3239_);
    lean_ctor_set(v___x_3240_, 1, v___x_3219_);
    v___x_3241_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__11;
    v___x_3242_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3242_, 0, v___x_3240_);
    lean_ctor_set(v___x_3242_, 1, v___x_3241_);
    v___x_3243_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3243_, 0, v___x_3242_);
    lean_ctor_set(v___x_3243_, 1, v___x_3209_);
    v___x_3244_ = lean_obj_once(
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
    v___x_3246_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3246_, 0, v___x_3244_);
    lean_ctor_set(v___x_3246_, 1, v___x_3245_);
    v___x_3247_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3247_, 0, v___x_3246_);
    lean_ctor_set_uint8(
        v___x_3247_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3214_,
    );
    v___x_3248_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3248_, 0, v___x_3243_);
    lean_ctor_set(v___x_3248_, 1, v___x_3247_);
    v___x_3249_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3249_, 0, v___x_3248_);
    lean_ctor_set(v___x_3249_, 1, v___x_3217_);
    v___x_3250_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3250_, 0, v___x_3249_);
    lean_ctor_set(v___x_3250_, 1, v___x_3219_);
    v___x_3251_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__13;
    v___x_3252_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3252_, 0, v___x_3250_);
    lean_ctor_set(v___x_3252_, 1, v___x_3251_);
    v___x_3253_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3253_, 0, v___x_3252_);
    lean_ctor_set(v___x_3253_, 1, v___x_3209_);
    v___x_3254_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__14,
    );
    v___x_3255_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__3(
        v_abbreviations_3205_,
    );
    v___x_3256_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3256_, 0, v___x_3254_);
    lean_ctor_set(v___x_3256_, 1, v___x_3255_);
    v___x_3257_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3257_, 0, v___x_3256_);
    lean_ctor_set_uint8(
        v___x_3257_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3214_,
    );
    v___x_3258_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3258_, 0, v___x_3253_);
    lean_ctor_set(v___x_3258_, 1, v___x_3257_);
    v___x_3259_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3259_, 0, v___x_3258_);
    lean_ctor_set(v___x_3259_, 1, v___x_3217_);
    v___x_3260_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3260_, 0, v___x_3259_);
    lean_ctor_set(v___x_3260_, 1, v___x_3219_);
    v___x_3261_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__16;
    v___x_3262_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3262_, 0, v___x_3260_);
    lean_ctor_set(v___x_3262_, 1, v___x_3261_);
    v___x_3263_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3263_, 0, v___x_3262_);
    lean_ctor_set(v___x_3263_, 1, v___x_3209_);
    v___x_3264_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__17,
    );
    v___x_3265_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__4(
        v_leapSeconds_3206_,
    );
    v___x_3266_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3266_, 0, v___x_3264_);
    lean_ctor_set(v___x_3266_, 1, v___x_3265_);
    v___x_3267_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3267_, 0, v___x_3266_);
    lean_ctor_set_uint8(
        v___x_3267_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3214_,
    );
    v___x_3268_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3268_, 0, v___x_3263_);
    lean_ctor_set(v___x_3268_, 1, v___x_3267_);
    v___x_3269_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3269_, 0, v___x_3268_);
    lean_ctor_set(v___x_3269_, 1, v___x_3217_);
    v___x_3270_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3270_, 0, v___x_3269_);
    lean_ctor_set(v___x_3270_, 1, v___x_3219_);
    v___x_3271_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__19;
    v___x_3272_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3272_, 0, v___x_3270_);
    lean_ctor_set(v___x_3272_, 1, v___x_3271_);
    v___x_3273_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3273_, 0, v___x_3272_);
    lean_ctor_set(v___x_3273_, 1, v___x_3209_);
    v___x_3274_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5(
        v_stdWallIndicators_3207_,
    );
    v___x_3275_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3275_, 0, v___x_3234_);
    lean_ctor_set(v___x_3275_, 1, v___x_3274_);
    v___x_3276_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3276_, 0, v___x_3275_);
    lean_ctor_set_uint8(
        v___x_3276_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3214_,
    );
    v___x_3277_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3277_, 0, v___x_3273_);
    lean_ctor_set(v___x_3277_, 1, v___x_3276_);
    v___x_3278_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3278_, 0, v___x_3277_);
    lean_ctor_set(v___x_3278_, 1, v___x_3217_);
    v___x_3279_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3279_, 0, v___x_3278_);
    lean_ctor_set(v___x_3279_, 1, v___x_3219_);
    v___x_3280_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg___closed__21;
    v___x_3281_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3281_, 0, v___x_3279_);
    lean_ctor_set(v___x_3281_, 1, v___x_3280_);
    v___x_3282_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3282_, 0, v___x_3281_);
    lean_ctor_set(v___x_3282_, 1, v___x_3209_);
    v___x_3283_ = l_Array_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV1_repr_spec__5(
        v_utLocalIndicators_3208_,
    );
    v___x_3284_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3284_, 0, v___x_3234_);
    lean_ctor_set(v___x_3284_, 1, v___x_3283_);
    v___x_3285_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3285_, 0, v___x_3284_);
    lean_ctor_set_uint8(
        v___x_3285_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3214_,
    );
    v___x_3286_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3286_, 0, v___x_3282_);
    lean_ctor_set(v___x_3286_, 1, v___x_3285_);
    v___x_3287_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25,
    );
    v___x_3288_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26;
    v___x_3289_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3289_, 0, v___x_3288_);
    lean_ctor_set(v___x_3289_, 1, v___x_3286_);
    v___x_3290_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27;
    v___x_3291_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3291_, 0, v___x_3289_);
    lean_ctor_set(v___x_3291_, 1, v___x_3290_);
    v___x_3292_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3292_, 0, v___x_3287_);
    lean_ctor_set(v___x_3292_, 1, v___x_3291_);
    v___x_3293_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3293_, 0, v___x_3292_);
    lean_ctor_set_uint8(
        v___x_3293_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3214_,
    );
    return v___x_3293_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprTZifV1_repr(
    mut v_x_3294_: *mut LeanObject,
    mut v_prec_3295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    v___x_3296_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(v_x_3294_);
    return v___x_3296_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___boxed(
    mut v_x_3297_: *mut LeanObject,
    mut v_prec_3298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3299_: *mut LeanObject = core::ptr::null_mut();
    v_res_3299_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr(v_x_3297_, v_prec_3298_);
    lean_dec(v_prec_3298_);
    return v_res_3299_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1()
-> *mut LeanObject {
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    v___x_3304_ = l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__0;
    v___x_3305_ = l_Std_Time_TimeZone_TZif_instInhabitedHeader_default;
    v___x_3306_ = lean_alloc_ctor(0, 8, (0) as u32);
    lean_ctor_set(v___x_3306_, 0, v___x_3305_);
    lean_ctor_set(v___x_3306_, 1, v___x_3304_);
    lean_ctor_set(v___x_3306_, 2, v___x_3304_);
    lean_ctor_set(v___x_3306_, 3, v___x_3304_);
    lean_ctor_set(v___x_3306_, 4, v___x_3304_);
    lean_ctor_set(v___x_3306_, 5, v___x_3304_);
    lean_ctor_set(v___x_3306_, 6, v___x_3304_);
    lean_ctor_set(v___x_3306_, 7, v___x_3304_);
    return v___x_3306_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default() -> *mut LeanObject {
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    v___x_3307_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default___closed__1,
    );
    return v___x_3307_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV1() -> *mut LeanObject {
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    v___x_3308_ = l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default;
    return v___x_3308_;
}
pub unsafe fn l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0(
    mut v_x_3315_: *mut LeanObject,
    mut v_x_3316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3321_: u8 = 0;
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3329_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3315_) == 0 {
                    v___x_3317_ = l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__1;
                    return v___x_3317_;
                } else {
                    v_val_3318_ = lean_ctor_get(v_x_3315_, 0);
                    v_isSharedCheck_3329_ = (!lean_is_exclusive(v_x_3315_)) as u8;
                    if v_isSharedCheck_3329_ == 0 {
                        v___x_3320_ = v_x_3315_;
                        v_isShared_3321_ = v_isSharedCheck_3329_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3318_);
                        lean_dec(v_x_3315_);
                        v___x_3320_ = lean_box(0);
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
                    lean_ctor_set_tag(v___x_3320_, 3);
                    lean_ctor_set(v___x_3320_, 0, v___x_3323_);
                    v___x_3325_ = v___x_3320_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3328_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3328_, 0, v___x_3323_);
                    v___x_3325_ = v_reuseFailAlloc_3328_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3326_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3326_, 0, v___x_3322_);
                lean_ctor_set(v___x_3326_, 1, v___x_3325_);
                v___x_3327_ = l_Repr_addAppParen(v___x_3326_, v_x_3316_);
                return v___x_3327_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___boxed(
    mut v_x_3330_: *mut LeanObject,
    mut v_x_3331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3332_: *mut LeanObject = core::ptr::null_mut();
    v_res_3332_ = l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0(
        v_x_3330_, v_x_3331_,
    );
    lean_dec(v_x_3331_);
    return v_res_3332_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg(
    mut v_x_3345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toTZifV1_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_footer_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3350_: u8 = 0;
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: u8 = 0;
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toTZifV1_3346_ = lean_ctor_get(v_x_3345_, 0);
                v_footer_3347_ = lean_ctor_get(v_x_3345_, 1);
                v_isSharedCheck_3381_ = (!lean_is_exclusive(v_x_3345_)) as u8;
                if v_isSharedCheck_3381_ == 0 {
                    v___x_3349_ = v_x_3345_;
                    v_isShared_3350_ = v_isSharedCheck_3381_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_footer_3347_);
                    lean_inc(v_toTZifV1_3346_);
                    lean_dec(v_x_3345_);
                    v___x_3349_ = lean_box(0);
                    v_isShared_3350_ = v_isSharedCheck_3381_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3351_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5;
                v___x_3352_ = l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__3;
                v___x_3353_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14_once
                    ),
                    _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__14,
                );
                v___x_3354_ = lean_unsigned_to_nat(0);
                v___x_3355_ =
                    l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(v_toTZifV1_3346_);
                if v_isShared_3350_ == 0 {
                    lean_ctor_set_tag(v___x_3349_, 4);
                    lean_ctor_set(v___x_3349_, 1, v___x_3355_);
                    lean_ctor_set(v___x_3349_, 0, v___x_3353_);
                    v___x_3357_ = v___x_3349_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3380_ = lean_alloc_ctor(4, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3353_);
                    lean_ctor_set(v_reuseFailAlloc_3380_, 1, v___x_3355_);
                    v___x_3357_ = v_reuseFailAlloc_3380_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3358_ = 0;
                v___x_3359_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3359_, 0, v___x_3357_);
                lean_ctor_set_uint8(
                    v___x_3359_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3358_,
                );
                v___x_3360_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3360_, 0, v___x_3352_);
                lean_ctor_set(v___x_3360_, 1, v___x_3359_);
                v___x_3361_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9;
                v___x_3362_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3362_, 0, v___x_3360_);
                lean_ctor_set(v___x_3362_, 1, v___x_3361_);
                v___x_3363_ = lean_box(1);
                v___x_3364_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3364_, 0, v___x_3362_);
                lean_ctor_set(v___x_3364_, 1, v___x_3363_);
                v___x_3365_ = l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg___closed__5;
                v___x_3366_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3366_, 0, v___x_3364_);
                lean_ctor_set(v___x_3366_, 1, v___x_3365_);
                v___x_3367_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3367_, 0, v___x_3366_);
                lean_ctor_set(v___x_3367_, 1, v___x_3351_);
                v___x_3368_ = lean_obj_once(
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
                v___x_3370_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3370_, 0, v___x_3368_);
                lean_ctor_set(v___x_3370_, 1, v___x_3369_);
                v___x_3371_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3371_, 0, v___x_3370_);
                lean_ctor_set_uint8(
                    v___x_3371_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3358_,
                );
                v___x_3372_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3372_, 0, v___x_3367_);
                lean_ctor_set(v___x_3372_, 1, v___x_3371_);
                v___x_3373_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25,
                );
                v___x_3374_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26;
                v___x_3375_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3375_, 0, v___x_3374_);
                lean_ctor_set(v___x_3375_, 1, v___x_3372_);
                v___x_3376_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27;
                v___x_3377_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3377_, 0, v___x_3375_);
                lean_ctor_set(v___x_3377_, 1, v___x_3376_);
                v___x_3378_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3378_, 0, v___x_3373_);
                lean_ctor_set(v___x_3378_, 1, v___x_3377_);
                v___x_3379_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3379_, 0, v___x_3378_);
                lean_ctor_set_uint8(
                    v___x_3379_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3358_,
                );
                return v___x_3379_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprTZifV2_repr(
    mut v_x_3382_: *mut LeanObject,
    mut v_prec_3383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    v___x_3384_ = l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg(v_x_3382_);
    return v___x_3384_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___boxed(
    mut v_x_3385_: *mut LeanObject,
    mut v_prec_3386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3387_: *mut LeanObject = core::ptr::null_mut();
    v_res_3387_ = l_Std_Time_TimeZone_TZif_instReprTZifV2_repr(v_x_3385_, v_prec_3386_);
    lean_dec(v_prec_3386_);
    return v_res_3387_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0()
-> *mut LeanObject {
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    v___x_3390_ = lean_box(0);
    v___x_3391_ = l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default;
    v___x_3392_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3392_, 0, v___x_3391_);
    lean_ctor_set(v___x_3392_, 1, v___x_3390_);
    return v___x_3392_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default() -> *mut LeanObject {
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    v___x_3393_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default___closed__0,
    );
    return v___x_3393_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV2() -> *mut LeanObject {
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    v___x_3394_ = l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default;
    return v___x_3394_;
}
pub unsafe fn l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0(
    mut v_x_3395_: *mut LeanObject,
    mut v_x_3396_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3395_) == 0 {
        let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
        v___x_3397_ =
            l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__1;
        return v___x_3397_;
    } else {
        let mut v_val_3398_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
        v_val_3398_ = lean_ctor_get(v_x_3395_, 0);
        lean_inc(v_val_3398_);
        lean_dec_ref_known(v_x_3395_, 1);
        v___x_3399_ =
            l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZifV2_repr_spec__0___closed__3;
        v___x_3400_ = l_Std_Time_TimeZone_TZif_instReprTZifV2_repr___redArg(v_val_3398_);
        v___x_3401_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_3401_, 0, v___x_3399_);
        lean_ctor_set(v___x_3401_, 1, v___x_3400_);
        v___x_3402_ = l_Repr_addAppParen(v___x_3401_, v_x_3396_);
        return v___x_3402_;
    }
}
pub unsafe fn l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0___boxed(
    mut v_x_3403_: *mut LeanObject,
    mut v_x_3404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3405_: *mut LeanObject = core::ptr::null_mut();
    v_res_3405_ = l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0(
        v_x_3403_, v_x_3404_,
    );
    lean_dec(v_x_3404_);
    return v_res_3405_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    v___x_3415_ = lean_unsigned_to_nat(6);
    v___x_3416_ = lean_nat_to_int(v___x_3415_);
    return v___x_3416_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg(
    mut v_x_3420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v1_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v2_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3425_: u8 = 0;
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: u8 = 0;
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_v1_3421_ = lean_ctor_get(v_x_3420_, 0);
                v_v2_3422_ = lean_ctor_get(v_x_3420_, 1);
                v_isSharedCheck_3455_ = (!lean_is_exclusive(v_x_3420_)) as u8;
                if v_isSharedCheck_3455_ == 0 {
                    v___x_3424_ = v_x_3420_;
                    v_isShared_3425_ = v_isSharedCheck_3455_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_v2_3422_);
                    lean_inc(v_v1_3421_);
                    lean_dec(v_x_3420_);
                    v___x_3424_ = lean_box(0);
                    v_isShared_3425_ = v_isSharedCheck_3455_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3426_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__5;
                v___x_3427_ = l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__3;
                v___x_3428_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4_once
                    ),
                    _init_l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__4,
                );
                v___x_3429_ = lean_unsigned_to_nat(0);
                v___x_3430_ = l_Std_Time_TimeZone_TZif_instReprTZifV1_repr___redArg(v_v1_3421_);
                if v_isShared_3425_ == 0 {
                    lean_ctor_set_tag(v___x_3424_, 4);
                    lean_ctor_set(v___x_3424_, 1, v___x_3430_);
                    lean_ctor_set(v___x_3424_, 0, v___x_3428_);
                    v___x_3432_ = v___x_3424_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3454_ = lean_alloc_ctor(4, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3428_);
                    lean_ctor_set(v_reuseFailAlloc_3454_, 1, v___x_3430_);
                    v___x_3432_ = v_reuseFailAlloc_3454_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3433_ = 0;
                v___x_3434_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3434_, 0, v___x_3432_);
                lean_ctor_set_uint8(
                    v___x_3434_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3433_,
                );
                v___x_3435_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3435_, 0, v___x_3427_);
                lean_ctor_set(v___x_3435_, 1, v___x_3434_);
                v___x_3436_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__9;
                v___x_3437_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3437_, 0, v___x_3435_);
                lean_ctor_set(v___x_3437_, 1, v___x_3436_);
                v___x_3438_ = lean_box(1);
                v___x_3439_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3439_, 0, v___x_3437_);
                lean_ctor_set(v___x_3439_, 1, v___x_3438_);
                v___x_3440_ = l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg___closed__6;
                v___x_3441_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3441_, 0, v___x_3439_);
                lean_ctor_set(v___x_3441_, 1, v___x_3440_);
                v___x_3442_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3442_, 0, v___x_3441_);
                lean_ctor_set(v___x_3442_, 1, v___x_3426_);
                v___x_3443_ =
                    l_Option_repr___at___00Std_Time_TimeZone_TZif_instReprTZif_repr_spec__0(
                        v_v2_3422_,
                        v___x_3429_,
                    );
                v___x_3444_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3444_, 0, v___x_3428_);
                lean_ctor_set(v___x_3444_, 1, v___x_3443_);
                v___x_3445_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3445_, 0, v___x_3444_);
                lean_ctor_set_uint8(
                    v___x_3445_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3433_,
                );
                v___x_3446_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3446_, 0, v___x_3442_);
                lean_ctor_set(v___x_3446_, 1, v___x_3445_);
                v___x_3447_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__25,
                );
                v___x_3448_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__26;
                v___x_3449_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3449_, 0, v___x_3448_);
                lean_ctor_set(v___x_3449_, 1, v___x_3446_);
                v___x_3450_ = l_Std_Time_TimeZone_TZif_instReprHeader_repr___redArg___closed__27;
                v___x_3451_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3451_, 0, v___x_3449_);
                lean_ctor_set(v___x_3451_, 1, v___x_3450_);
                v___x_3452_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3452_, 0, v___x_3447_);
                lean_ctor_set(v___x_3452_, 1, v___x_3451_);
                v___x_3453_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3453_, 0, v___x_3452_);
                lean_ctor_set_uint8(
                    v___x_3453_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3433_,
                );
                return v___x_3453_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprTZif_repr(
    mut v_x_3456_: *mut LeanObject,
    mut v_prec_3457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    v___x_3458_ = l_Std_Time_TimeZone_TZif_instReprTZif_repr___redArg(v_x_3456_);
    return v___x_3458_;
}
pub unsafe fn l_Std_Time_TimeZone_TZif_instReprTZif_repr___boxed(
    mut v_x_3459_: *mut LeanObject,
    mut v_prec_3460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3461_: *mut LeanObject = core::ptr::null_mut();
    v_res_3461_ = l_Std_Time_TimeZone_TZif_instReprTZif_repr(v_x_3459_, v_prec_3460_);
    lean_dec(v_prec_3460_);
    return v_res_3461_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0()
-> *mut LeanObject {
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    v___x_3464_ = lean_box(0);
    v___x_3465_ = l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default;
    v___x_3466_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3466_, 0, v___x_3465_);
    lean_ctor_set(v___x_3466_, 1, v___x_3464_);
    return v___x_3466_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedTZif_default() -> *mut LeanObject {
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    v___x_3467_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0_once
        ),
        _init_l_Std_Time_TimeZone_TZif_instInhabitedTZif_default___closed__0,
    );
    return v___x_3467_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_TZif_instInhabitedTZif() -> *mut LeanObject {
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    v___x_3468_ = l_Std_Time_TimeZone_TZif_instInhabitedTZif_default;
    return v___x_3468_;
}
pub unsafe fn _init_l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1()
-> *mut LeanObject {
    let mut v___x_3469_: u32 = 0;
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    v___x_3469_ = l_instInhabitedUInt32;
    v___x_3470_ = lean_box_uint32(v___x_3469_);
    return v___x_3470_;
}
pub unsafe fn l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0(
    mut v_msg_3471_: *mut LeanObject,
) -> u32 {
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: u32 = 0;
    v___x_3472_ = l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1;
    v___x_3473_ = lean_panic_fn_borrowed(v___x_3472_, v_msg_3471_);
    v___x_3474_ = lean_unbox_uint32(v___x_3473_);
    lean_dec(v___x_3473_);
    return v___x_3474_;
}
pub unsafe fn l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed(
    mut v_msg_3475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3476_: u32 = 0;
    let mut v_r_3477_: *mut LeanObject = core::ptr::null_mut();
    v_res_3476_ = l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0(v_msg_3475_);
    v_r_3477_ = lean_box_uint32(v_res_3476_);
    return v_r_3477_;
}
pub unsafe fn _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3()
-> *mut LeanObject {
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    v___x_3481_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__2;
    v___x_3482_ = lean_unsigned_to_nat(2);
    v___x_3483_ = lean_unsigned_to_nat(181);
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
    mut v_bs_3487_: *mut LeanObject,
) -> u32 {
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: u8 = 0;
    v___x_3488_ = lean_byte_array_size(v_bs_3487_);
    v___x_3489_ = lean_unsigned_to_nat(4);
    v___x_3490_ = lean_nat_dec_eq(v___x_3488_, v___x_3489_);
    if v___x_3490_ == 0 {
        let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3492_: u32 = 0;
        v___x_3491_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3), core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3_once), _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___closed__3);
        v___x_3492_ = l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0(v___x_3491_);
        return v___x_3492_;
    } else {
        let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3494_: u8 = 0;
        let mut v___x_3495_: u32 = 0;
        let mut v___x_3496_: u32 = 0;
        let mut v___x_3497_: u32 = 0;
        let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3499_: u8 = 0;
        let mut v___x_3500_: u32 = 0;
        let mut v___x_3501_: u32 = 0;
        let mut v___x_3502_: u32 = 0;
        let mut v___x_3503_: u32 = 0;
        let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3505_: u8 = 0;
        let mut v___x_3506_: u32 = 0;
        let mut v___x_3507_: u32 = 0;
        let mut v___x_3508_: u32 = 0;
        let mut v___x_3509_: u32 = 0;
        let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3511_: u8 = 0;
        let mut v___x_3512_: u32 = 0;
        let mut v___x_3513_: u32 = 0;
        v___x_3493_ = lean_unsigned_to_nat(0);
        v___x_3494_ = lean_byte_array_get(v_bs_3487_, v___x_3493_);
        v___x_3495_ = lean_uint8_to_uint32(v___x_3494_);
        v___x_3496_ = 24;
        v___x_3497_ = lean_uint32_shift_left(v___x_3495_, v___x_3496_);
        v___x_3498_ = lean_unsigned_to_nat(1);
        v___x_3499_ = lean_byte_array_get(v_bs_3487_, v___x_3498_);
        v___x_3500_ = lean_uint8_to_uint32(v___x_3499_);
        v___x_3501_ = 16;
        v___x_3502_ = lean_uint32_shift_left(v___x_3500_, v___x_3501_);
        v___x_3503_ = lean_uint32_lor(v___x_3497_, v___x_3502_);
        v___x_3504_ = lean_unsigned_to_nat(2);
        v___x_3505_ = lean_byte_array_get(v_bs_3487_, v___x_3504_);
        v___x_3506_ = lean_uint8_to_uint32(v___x_3505_);
        v___x_3507_ = 8;
        v___x_3508_ = lean_uint32_shift_left(v___x_3506_, v___x_3507_);
        v___x_3509_ = lean_uint32_lor(v___x_3503_, v___x_3508_);
        v___x_3510_ = lean_unsigned_to_nat(3);
        v___x_3511_ = lean_byte_array_get(v_bs_3487_, v___x_3510_);
        v___x_3512_ = lean_uint8_to_uint32(v___x_3511_);
        v___x_3513_ = lean_uint32_lor(v___x_3509_, v___x_3512_);
        return v___x_3513_;
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32___boxed(
    mut v_bs_3514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3515_: u32 = 0;
    let mut v_r_3516_: *mut LeanObject = core::ptr::null_mut();
    v_res_3515_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(v_bs_3514_);
    lean_dec_ref(v_bs_3514_);
    v_r_3516_ = lean_box_uint32(v_res_3515_);
    return v_r_3516_;
}
pub unsafe fn _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___closed__0()
-> *mut LeanObject {
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    v___x_3517_ = lean_unsigned_to_nat(31);
    v___x_3518_ = lean_unsigned_to_nat(1);
    v___x_3519_ = lean_nat_shiftl(v___x_3518_, v___x_3517_);
    return v___x_3519_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32(
    mut v_bs_3520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3521_: u32 = 0;
    let mut v_n_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: u8 = 0;
    v___x_3521_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32(v_bs_3520_);
    v_n_3522_ = lean_uint32_to_nat(v___x_3521_);
    v___x_3523_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___closed__0), core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___closed__0_once), _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___closed__0);
    v___x_3524_ = lean_nat_dec_lt(v_n_3522_, v___x_3523_);
    if v___x_3524_ == 0 {
        let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
        v___x_3525_ = lean_cstr_to_nat(b"4294967296\0".as_ptr().cast());
        v___x_3526_ = lean_nat_sub(v___x_3525_, v_n_3522_);
        lean_dec(v_n_3522_);
        v___x_3527_ = l_Int_negOfNat(v___x_3526_);
        lean_dec(v___x_3526_);
        return v___x_3527_;
    } else {
        let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
        v___x_3528_ = lean_nat_to_int(v_n_3522_);
        return v___x_3528_;
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32___boxed(
    mut v_bs_3529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3530_: *mut LeanObject = core::ptr::null_mut();
    v_res_3530_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt32(v_bs_3529_);
    lean_dec_ref(v_bs_3529_);
    return v_res_3530_;
}
pub unsafe fn _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0()
-> *mut LeanObject {
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    v___x_3531_ = lean_unsigned_to_nat(63);
    v___x_3532_ = lean_unsigned_to_nat(1);
    v___x_3533_ = lean_nat_shiftl(v___x_3532_, v___x_3531_);
    return v___x_3533_;
}
pub unsafe fn _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1()
-> *mut LeanObject {
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    v___x_3534_ = lean_cstr_to_nat(b"18446744073709551616\0".as_ptr().cast());
    return v___x_3534_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64(
    mut v_bs_3535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3536_: u64 = 0;
    let mut v_n_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: u8 = 0;
    v___x_3536_ = l_ByteArray_toUInt64BE_x21(v_bs_3535_);
    v_n_3537_ = lean_uint64_to_nat(v___x_3536_);
    v___x_3538_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0), core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0_once), _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__0);
    v___x_3539_ = lean_nat_dec_lt(v_n_3537_, v___x_3538_);
    if v___x_3539_ == 0 {
        let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
        v___x_3540_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1), core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1_once), _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___closed__1);
        v___x_3541_ = lean_nat_sub(v___x_3540_, v_n_3537_);
        lean_dec(v_n_3537_);
        v___x_3542_ = l_Int_negOfNat(v___x_3541_);
        lean_dec(v___x_3541_);
        return v___x_3542_;
    } else {
        let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
        v___x_3543_ = lean_nat_to_int(v_n_3537_);
        return v___x_3543_;
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64___boxed(
    mut v_bs_3544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3545_: *mut LeanObject = core::ptr::null_mut();
    v_res_3545_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toInt64(v_bs_3544_);
    lean_dec_ref(v_bs_3544_);
    return v_res_3545_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(
    mut v_upperBound_3546_: *mut LeanObject,
    mut v_p_3547_: *mut LeanObject,
    mut v_a_3548_: *mut LeanObject,
    mut v_b_3549_: *mut LeanObject,
    mut v___y_3550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3551_: u8 = 0;
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3564_: u8 = 0;
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3568_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3551_ = lean_nat_dec_lt(v_a_3548_, v_upperBound_3546_);
                if v___x_3551_ == 0 {
                    lean_dec(v_a_3548_);
                    lean_dec_ref(v_p_3547_);
                    v___x_3552_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3552_, 0, v___y_3550_);
                    lean_ctor_set(v___x_3552_, 1, v_b_3549_);
                    return v___x_3552_;
                } else {
                    lean_inc_ref(v_p_3547_);
                    v___x_3553_ = lean_apply_1(v_p_3547_, v___y_3550_);
                    if lean_obj_tag(v___x_3553_) == 0 {
                        v_pos_3554_ = lean_ctor_get(v___x_3553_, 0);
                        lean_inc(v_pos_3554_);
                        v_res_3555_ = lean_ctor_get(v___x_3553_, 1);
                        lean_inc(v_res_3555_);
                        lean_dec_ref_known(v___x_3553_, 2);
                        v___x_3556_ = lean_array_push(v_b_3549_, v_res_3555_);
                        v___x_3557_ = lean_unsigned_to_nat(1);
                        v___x_3558_ = lean_nat_add(v_a_3548_, v___x_3557_);
                        lean_dec(v_a_3548_);
                        v_a_3548_ = v___x_3558_;
                        v_b_3549_ = v___x_3556_;
                        v___y_3550_ = v_pos_3554_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_b_3549_);
                        lean_dec(v_a_3548_);
                        lean_dec_ref(v_p_3547_);
                        v_pos_3560_ = lean_ctor_get(v___x_3553_, 0);
                        v_err_3561_ = lean_ctor_get(v___x_3553_, 1);
                        v_isSharedCheck_3568_ = (!lean_is_exclusive(v___x_3553_)) as u8;
                        if v_isSharedCheck_3568_ == 0 {
                            v___x_3563_ = v___x_3553_;
                            v_isShared_3564_ = v_isSharedCheck_3568_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_err_3561_);
                            lean_inc(v_pos_3560_);
                            lean_dec(v___x_3553_);
                            v___x_3563_ = lean_box(0);
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
                    v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_pos_3560_);
                    lean_ctor_set(v_reuseFailAlloc_3567_, 1, v_err_3561_);
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
    mut v_upperBound_3569_: *mut LeanObject,
    mut v_p_3570_: *mut LeanObject,
    mut v_a_3571_: *mut LeanObject,
    mut v_b_3572_: *mut LeanObject,
    mut v___y_3573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3574_: *mut LeanObject = core::ptr::null_mut();
    v_res_3574_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(v_upperBound_3569_, v_p_3570_, v_a_3571_, v_b_3572_, v___y_3573_);
    lean_dec(v_upperBound_3569_);
    return v_res_3574_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(
    mut v_n_3577_: *mut LeanObject,
    mut v_p_3578_: *mut LeanObject,
    mut v_a_3579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    v___x_3580_ = lean_unsigned_to_nat(0);
    v_result_3581_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg___closed__0;
    v___x_3582_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(v_n_3577_, v_p_3578_, v___x_3580_, v_result_3581_, v_a_3579_);
    return v___x_3582_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg___boxed(
    mut v_n_3583_: *mut LeanObject,
    mut v_p_3584_: *mut LeanObject,
    mut v_a_3585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3586_: *mut LeanObject = core::ptr::null_mut();
    v_res_3586_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(
        v_n_3583_, v_p_3584_, v_a_3585_,
    );
    lean_dec(v_n_3583_);
    return v_res_3586_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN(
    mut v_00_u03b1_3587_: *mut LeanObject,
    mut v_n_3588_: *mut LeanObject,
    mut v_p_3589_: *mut LeanObject,
    mut v_a_3590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    v___x_3591_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(
        v_n_3588_, v_p_3589_, v_a_3590_,
    );
    return v___x_3591_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___boxed(
    mut v_00_u03b1_3592_: *mut LeanObject,
    mut v_n_3593_: *mut LeanObject,
    mut v_p_3594_: *mut LeanObject,
    mut v_a_3595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3596_: *mut LeanObject = core::ptr::null_mut();
    v_res_3596_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN(
        v_00_u03b1_3592_,
        v_n_3593_,
        v_p_3594_,
        v_a_3595_,
    );
    lean_dec(v_n_3593_);
    return v_res_3596_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0(
    mut v_00_u03b1_3597_: *mut LeanObject,
    mut v_upperBound_3598_: *mut LeanObject,
    mut v_p_3599_: *mut LeanObject,
    mut v_inst_3600_: *mut LeanObject,
    mut v_R_3601_: *mut LeanObject,
    mut v_a_3602_: *mut LeanObject,
    mut v_b_3603_: *mut LeanObject,
    mut v_c_3604_: *mut LeanObject,
    mut v___y_3605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    v___x_3606_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___redArg(v_upperBound_3598_, v_p_3599_, v_a_3602_, v_b_3603_, v___y_3605_);
    return v___x_3606_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0___boxed(
    mut v_00_u03b1_3607_: *mut LeanObject,
    mut v_upperBound_3608_: *mut LeanObject,
    mut v_p_3609_: *mut LeanObject,
    mut v_inst_3610_: *mut LeanObject,
    mut v_R_3611_: *mut LeanObject,
    mut v_a_3612_: *mut LeanObject,
    mut v_b_3613_: *mut LeanObject,
    mut v_c_3614_: *mut LeanObject,
    mut v___y_3615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3616_: *mut LeanObject = core::ptr::null_mut();
    v_res_3616_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN_spec__0(v_00_u03b1_3607_, v_upperBound_3608_, v_p_3609_, v_inst_3610_, v_R_3611_, v_a_3612_, v_b_3613_, v_c_3614_, v___y_3615_);
    lean_dec(v_upperBound_3608_);
    return v_res_3616_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu64(
    mut v_a_3617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3624_: u8 = 0;
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: u64 = 0;
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3631_: u8 = 0;
    let mut v_pos_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3636_: u8 = 0;
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3640_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3618_ = lean_unsigned_to_nat(8);
                v___x_3619_ = l_Std_Internal_Parsec_ByteArray_take(v___x_3618_, v_a_3617_);
                if lean_obj_tag(v___x_3619_) == 0 {
                    v_pos_3620_ = lean_ctor_get(v___x_3619_, 0);
                    v_res_3621_ = lean_ctor_get(v___x_3619_, 1);
                    v_isSharedCheck_3631_ = (!lean_is_exclusive(v___x_3619_)) as u8;
                    if v_isSharedCheck_3631_ == 0 {
                        v___x_3623_ = v___x_3619_;
                        v_isShared_3624_ = v_isSharedCheck_3631_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_res_3621_);
                        lean_inc(v_pos_3620_);
                        lean_dec(v___x_3619_);
                        v___x_3623_ = lean_box(0);
                        v_isShared_3624_ = v_isSharedCheck_3631_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_3632_ = lean_ctor_get(v___x_3619_, 0);
                    v_err_3633_ = lean_ctor_get(v___x_3619_, 1);
                    v_isSharedCheck_3640_ = (!lean_is_exclusive(v___x_3619_)) as u8;
                    if v_isSharedCheck_3640_ == 0 {
                        v___x_3635_ = v___x_3619_;
                        v_isShared_3636_ = v_isSharedCheck_3640_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_err_3633_);
                        lean_inc(v_pos_3632_);
                        lean_dec(v___x_3619_);
                        v___x_3635_ = lean_box(0);
                        v_isShared_3636_ = v_isSharedCheck_3640_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3625_ = l_ByteSlice_toByteArray(v_res_3621_);
                v___x_3626_ = l_ByteArray_toUInt64LE_x21(v___x_3625_);
                lean_dec_ref(v___x_3625_);
                v___x_3627_ = lean_box_uint64(v___x_3626_);
                if v_isShared_3624_ == 0 {
                    lean_ctor_set(v___x_3623_, 1, v___x_3627_);
                    v___x_3629_ = v___x_3623_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3630_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_pos_3620_);
                    lean_ctor_set(v_reuseFailAlloc_3630_, 1, v___x_3627_);
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
                    v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_pos_3632_);
                    lean_ctor_set(v_reuseFailAlloc_3639_, 1, v_err_3633_);
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
    mut v_a_3641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3648_: u8 = 0;
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3654_: u8 = 0;
    let mut v_pos_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3659_: u8 = 0;
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3663_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3642_ = lean_unsigned_to_nat(8);
                v___x_3643_ = l_Std_Internal_Parsec_ByteArray_take(v___x_3642_, v_a_3641_);
                if lean_obj_tag(v___x_3643_) == 0 {
                    v_pos_3644_ = lean_ctor_get(v___x_3643_, 0);
                    v_res_3645_ = lean_ctor_get(v___x_3643_, 1);
                    v_isSharedCheck_3654_ = (!lean_is_exclusive(v___x_3643_)) as u8;
                    if v_isSharedCheck_3654_ == 0 {
                        v___x_3647_ = v___x_3643_;
                        v_isShared_3648_ = v_isSharedCheck_3654_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_res_3645_);
                        lean_inc(v_pos_3644_);
                        lean_dec(v___x_3643_);
                        v___x_3647_ = lean_box(0);
                        v_isShared_3648_ = v_isSharedCheck_3654_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_3655_ = lean_ctor_get(v___x_3643_, 0);
                    v_err_3656_ = lean_ctor_get(v___x_3643_, 1);
                    v_isSharedCheck_3663_ = (!lean_is_exclusive(v___x_3643_)) as u8;
                    if v_isSharedCheck_3663_ == 0 {
                        v___x_3658_ = v___x_3643_;
                        v_isShared_3659_ = v_isSharedCheck_3663_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_err_3656_);
                        lean_inc(v_pos_3655_);
                        lean_dec(v___x_3643_);
                        v___x_3658_ = lean_box(0);
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
                lean_dec_ref(v___x_3649_);
                if v_isShared_3648_ == 0 {
                    lean_ctor_set(v___x_3647_, 1, v___x_3650_);
                    v___x_3652_ = v___x_3647_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_pos_3644_);
                    lean_ctor_set(v_reuseFailAlloc_3653_, 1, v___x_3650_);
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
                    v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_pos_3655_);
                    lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_err_3656_);
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
    mut v_a_3664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3671_: u8 = 0;
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: u32 = 0;
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3678_: u8 = 0;
    let mut v_pos_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3683_: u8 = 0;
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3687_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3665_ = lean_unsigned_to_nat(4);
                v___x_3666_ = l_Std_Internal_Parsec_ByteArray_take(v___x_3665_, v_a_3664_);
                if lean_obj_tag(v___x_3666_) == 0 {
                    v_pos_3667_ = lean_ctor_get(v___x_3666_, 0);
                    v_res_3668_ = lean_ctor_get(v___x_3666_, 1);
                    v_isSharedCheck_3678_ = (!lean_is_exclusive(v___x_3666_)) as u8;
                    if v_isSharedCheck_3678_ == 0 {
                        v___x_3670_ = v___x_3666_;
                        v_isShared_3671_ = v_isSharedCheck_3678_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_res_3668_);
                        lean_inc(v_pos_3667_);
                        lean_dec(v___x_3666_);
                        v___x_3670_ = lean_box(0);
                        v_isShared_3671_ = v_isSharedCheck_3678_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_3679_ = lean_ctor_get(v___x_3666_, 0);
                    v_err_3680_ = lean_ctor_get(v___x_3666_, 1);
                    v_isSharedCheck_3687_ = (!lean_is_exclusive(v___x_3666_)) as u8;
                    if v_isSharedCheck_3687_ == 0 {
                        v___x_3682_ = v___x_3666_;
                        v_isShared_3683_ = v_isSharedCheck_3687_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_err_3680_);
                        lean_inc(v_pos_3679_);
                        lean_dec(v___x_3666_);
                        v___x_3682_ = lean_box(0);
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
                lean_dec_ref(v___x_3672_);
                v___x_3674_ = lean_box_uint32(v___x_3673_);
                if v_isShared_3671_ == 0 {
                    lean_ctor_set(v___x_3670_, 1, v___x_3674_);
                    v___x_3676_ = v___x_3670_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_pos_3667_);
                    lean_ctor_set(v_reuseFailAlloc_3677_, 1, v___x_3674_);
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
                    v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_pos_3679_);
                    lean_ctor_set(v_reuseFailAlloc_3686_, 1, v_err_3680_);
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
    mut v_a_3688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3695_: u8 = 0;
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3701_: u8 = 0;
    let mut v_pos_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3706_: u8 = 0;
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3710_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3689_ = lean_unsigned_to_nat(4);
                v___x_3690_ = l_Std_Internal_Parsec_ByteArray_take(v___x_3689_, v_a_3688_);
                if lean_obj_tag(v___x_3690_) == 0 {
                    v_pos_3691_ = lean_ctor_get(v___x_3690_, 0);
                    v_res_3692_ = lean_ctor_get(v___x_3690_, 1);
                    v_isSharedCheck_3701_ = (!lean_is_exclusive(v___x_3690_)) as u8;
                    if v_isSharedCheck_3701_ == 0 {
                        v___x_3694_ = v___x_3690_;
                        v_isShared_3695_ = v_isSharedCheck_3701_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_res_3692_);
                        lean_inc(v_pos_3691_);
                        lean_dec(v___x_3690_);
                        v___x_3694_ = lean_box(0);
                        v_isShared_3695_ = v_isSharedCheck_3701_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_3702_ = lean_ctor_get(v___x_3690_, 0);
                    v_err_3703_ = lean_ctor_get(v___x_3690_, 1);
                    v_isSharedCheck_3710_ = (!lean_is_exclusive(v___x_3690_)) as u8;
                    if v_isSharedCheck_3710_ == 0 {
                        v___x_3705_ = v___x_3690_;
                        v_isShared_3706_ = v_isSharedCheck_3710_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_err_3703_);
                        lean_inc(v_pos_3702_);
                        lean_dec(v___x_3690_);
                        v___x_3705_ = lean_box(0);
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
                lean_dec_ref(v___x_3696_);
                if v_isShared_3695_ == 0 {
                    lean_ctor_set(v___x_3694_, 1, v___x_3697_);
                    v___x_3699_ = v___x_3694_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_pos_3691_);
                    lean_ctor_set(v_reuseFailAlloc_3700_, 1, v___x_3697_);
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
                    v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_pos_3702_);
                    lean_ctor_set(v_reuseFailAlloc_3709_, 1, v_err_3703_);
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
    mut v_a_3711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: u8 = 0;
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3720_: u8 = 0;
    let mut v_c_3721_: u8 = 0;
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3729_: u8 = 0;
    let mut v_unused_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3712_ = lean_ctor_get(v_a_3711_, 0);
                v_idx_3713_ = lean_ctor_get(v_a_3711_, 1);
                v___x_3714_ = lean_byte_array_size(v_array_3712_);
                v___x_3715_ = lean_nat_dec_lt(v_idx_3713_, v___x_3714_);
                if v___x_3715_ == 0 {
                    v___x_3716_ = lean_box(0);
                    v___x_3717_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3717_, 0, v_a_3711_);
                    lean_ctor_set(v___x_3717_, 1, v___x_3716_);
                    return v___x_3717_;
                } else {
                    lean_inc(v_idx_3713_);
                    lean_inc_ref(v_array_3712_);
                    v_isSharedCheck_3729_ = (!lean_is_exclusive(v_a_3711_)) as u8;
                    if v_isSharedCheck_3729_ == 0 {
                        v_unused_3730_ = lean_ctor_get(v_a_3711_, 1);
                        lean_dec(v_unused_3730_);
                        v_unused_3731_ = lean_ctor_get(v_a_3711_, 0);
                        lean_dec(v_unused_3731_);
                        v___x_3719_ = v_a_3711_;
                        v_isShared_3720_ = v_isSharedCheck_3729_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_a_3711_);
                        v___x_3719_ = lean_box(0);
                        v_isShared_3720_ = v_isSharedCheck_3729_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_c_3721_ = lean_byte_array_fget(v_array_3712_, v_idx_3713_);
                v___x_3722_ = lean_unsigned_to_nat(1);
                v___x_3723_ = lean_nat_add(v_idx_3713_, v___x_3722_);
                lean_dec(v_idx_3713_);
                if v_isShared_3720_ == 0 {
                    lean_ctor_set(v___x_3719_, 1, v___x_3723_);
                    v_it_x27_3725_ = v___x_3719_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_array_3712_);
                    lean_ctor_set(v_reuseFailAlloc_3728_, 1, v___x_3723_);
                    v_it_x27_3725_ = v_reuseFailAlloc_3728_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3726_ = lean_box((v_c_3721_) as usize);
                v___x_3727_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3727_, 0, v_it_x27_3725_);
                lean_ctor_set(v___x_3727_, 1, v___x_3726_);
                return v___x_3727_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pbool(
    mut v_a_3732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3738_: u8 = 0;
    let mut v___x_3739_: u8 = 0;
    let mut v___x_3740_: u8 = 0;
    let mut v___x_3741_: u8 = 0;
    let mut v___x_3742_: u8 = 0;
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: u8 = 0;
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3752_: u8 = 0;
    let mut v_pos_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3756_: u8 = 0;
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3761_: u8 = 0;
    let mut v_unused_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3733_ =
                    l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(
                        v_a_3732_,
                    );
                if lean_obj_tag(v___x_3733_) == 0 {
                    v_pos_3734_ = lean_ctor_get(v___x_3733_, 0);
                    v_res_3735_ = lean_ctor_get(v___x_3733_, 1);
                    v_isSharedCheck_3752_ = (!lean_is_exclusive(v___x_3733_)) as u8;
                    if v_isSharedCheck_3752_ == 0 {
                        v___x_3737_ = v___x_3733_;
                        v_isShared_3738_ = v_isSharedCheck_3752_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_res_3735_);
                        lean_inc(v_pos_3734_);
                        lean_dec(v___x_3733_);
                        v___x_3737_ = lean_box(0);
                        v_isShared_3738_ = v_isSharedCheck_3752_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_3753_ = lean_ctor_get(v___x_3733_, 0);
                    v_isSharedCheck_3761_ = (!lean_is_exclusive(v___x_3733_)) as u8;
                    if v_isSharedCheck_3761_ == 0 {
                        v_unused_3762_ = lean_ctor_get(v___x_3733_, 1);
                        lean_dec(v_unused_3762_);
                        v___x_3755_ = v___x_3733_;
                        v_isShared_3756_ = v_isSharedCheck_3761_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_pos_3753_);
                        lean_dec(v___x_3733_);
                        v___x_3755_ = lean_box(0);
                        v_isShared_3756_ = v_isSharedCheck_3761_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3739_ = 0;
                v___x_3740_ = (lean_unbox(v_res_3735_) as u8);
                lean_dec(v_res_3735_);
                v___x_3741_ = lean_uint8_dec_eq(v___x_3740_, v___x_3739_);
                if v___x_3741_ == 0 {
                    v___x_3742_ = 1;
                    v___x_3743_ = lean_box((v___x_3742_) as usize);
                    if v_isShared_3738_ == 0 {
                        lean_ctor_set(v___x_3737_, 1, v___x_3743_);
                        v___x_3745_ = v___x_3737_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_pos_3734_);
                        lean_ctor_set(v_reuseFailAlloc_3746_, 1, v___x_3743_);
                        v___x_3745_ = v_reuseFailAlloc_3746_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3747_ = 0;
                    v___x_3748_ = lean_box((v___x_3747_) as usize);
                    if v_isShared_3738_ == 0 {
                        lean_ctor_set(v___x_3737_, 1, v___x_3748_);
                        v___x_3750_ = v___x_3737_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_pos_3734_);
                        lean_ctor_set(v_reuseFailAlloc_3751_, 1, v___x_3748_);
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
                v___x_3757_ = lean_box(0);
                if v_isShared_3756_ == 0 {
                    lean_ctor_set(v___x_3755_, 1, v___x_3757_);
                    v___x_3759_ = v___x_3755_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_pos_3753_);
                    lean_ctor_set(v_reuseFailAlloc_3760_, 1, v___x_3757_);
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
-> *mut LeanObject {
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_utf8_3764_: *mut LeanObject = core::ptr::null_mut();
    v___x_3763_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_termInt32___closed__17;
    v_utf8_3764_ = lean_string_to_utf8(v___x_3763_);
    return v_utf8_3764_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader(
    mut v_a_3765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_utf8_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3795_: u8 = 0;
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: u8 = 0;
    let mut v___x_3798_: u32 = 0;
    let mut v___x_3799_: u32 = 0;
    let mut v___x_3800_: u32 = 0;
    let mut v___x_3801_: u32 = 0;
    let mut v___x_3802_: u32 = 0;
    let mut v___x_3803_: u32 = 0;
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3807_: u8 = 0;
    let mut v_pos_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3812_: u8 = 0;
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3816_: u8 = 0;
    let mut v_pos_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3821_: u8 = 0;
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3825_: u8 = 0;
    let mut v_pos_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3830_: u8 = 0;
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3834_: u8 = 0;
    let mut v_pos_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3839_: u8 = 0;
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3843_: u8 = 0;
    let mut v_pos_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3848_: u8 = 0;
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3852_: u8 = 0;
    let mut v_pos_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3857_: u8 = 0;
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3861_: u8 = 0;
    let mut v_pos_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3866_: u8 = 0;
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3870_: u8 = 0;
    let mut v_pos_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3874_: u8 = 0;
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3879_: u8 = 0;
    let mut v_unused_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3885_: u8 = 0;
    let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3889_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_utf8_3766_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0), core::ptr::addr_of_mut!(l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0_once), _init_l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader___closed__0);
                v___x_3767_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v_utf8_3766_, v_a_3765_);
                if lean_obj_tag(v___x_3767_) == 0 {
                    v_pos_3768_ = lean_ctor_get(v___x_3767_, 0);
                    lean_inc(v_pos_3768_);
                    lean_dec_ref_known(v___x_3767_, 2);
                    v___x_3769_ =
                        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(
                            v_pos_3768_,
                        );
                    if lean_obj_tag(v___x_3769_) == 0 {
                        v_pos_3770_ = lean_ctor_get(v___x_3769_, 0);
                        lean_inc(v_pos_3770_);
                        v_res_3771_ = lean_ctor_get(v___x_3769_, 1);
                        lean_inc(v_res_3771_);
                        lean_dec_ref_known(v___x_3769_, 2);
                        v___x_3772_ = lean_unsigned_to_nat(15);
                        v___x_3773_ =
                            l_Std_Internal_Parsec_ByteArray_take(v___x_3772_, v_pos_3770_);
                        if lean_obj_tag(v___x_3773_) == 0 {
                            v_pos_3774_ = lean_ctor_get(v___x_3773_, 0);
                            lean_inc(v_pos_3774_);
                            lean_dec_ref_known(v___x_3773_, 2);
                            v___x_3775_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_3774_);
                            if lean_obj_tag(v___x_3775_) == 0 {
                                v_pos_3776_ = lean_ctor_get(v___x_3775_, 0);
                                lean_inc(v_pos_3776_);
                                v_res_3777_ = lean_ctor_get(v___x_3775_, 1);
                                lean_inc(v_res_3777_);
                                lean_dec_ref_known(v___x_3775_, 2);
                                v___x_3778_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_3776_);
                                if lean_obj_tag(v___x_3778_) == 0 {
                                    v_pos_3779_ = lean_ctor_get(v___x_3778_, 0);
                                    lean_inc(v_pos_3779_);
                                    v_res_3780_ = lean_ctor_get(v___x_3778_, 1);
                                    lean_inc(v_res_3780_);
                                    lean_dec_ref_known(v___x_3778_, 2);
                                    v___x_3781_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_3779_);
                                    if lean_obj_tag(v___x_3781_) == 0 {
                                        v_pos_3782_ = lean_ctor_get(v___x_3781_, 0);
                                        lean_inc(v_pos_3782_);
                                        v_res_3783_ = lean_ctor_get(v___x_3781_, 1);
                                        lean_inc(v_res_3783_);
                                        lean_dec_ref_known(v___x_3781_, 2);
                                        v___x_3784_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_3782_);
                                        if lean_obj_tag(v___x_3784_) == 0 {
                                            v_pos_3785_ = lean_ctor_get(v___x_3784_, 0);
                                            lean_inc(v_pos_3785_);
                                            v_res_3786_ = lean_ctor_get(v___x_3784_, 1);
                                            lean_inc(v_res_3786_);
                                            lean_dec_ref_known(v___x_3784_, 2);
                                            v___x_3787_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_3785_);
                                            if lean_obj_tag(v___x_3787_) == 0 {
                                                v_pos_3788_ = lean_ctor_get(v___x_3787_, 0);
                                                lean_inc(v_pos_3788_);
                                                v_res_3789_ = lean_ctor_get(v___x_3787_, 1);
                                                lean_inc(v_res_3789_);
                                                lean_dec_ref_known(v___x_3787_, 2);
                                                v___x_3790_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu32(v_pos_3788_);
                                                if lean_obj_tag(v___x_3790_) == 0 {
                                                    v_pos_3791_ = lean_ctor_get(v___x_3790_, 0);
                                                    v_res_3792_ = lean_ctor_get(v___x_3790_, 1);
                                                    v_isSharedCheck_3807_ =
                                                        (!lean_is_exclusive(v___x_3790_)) as u8;
                                                    if v_isSharedCheck_3807_ == 0 {
                                                        v___x_3794_ = v___x_3790_;
                                                        v_isShared_3795_ = v_isSharedCheck_3807_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_res_3792_);
                                                        lean_inc(v_pos_3791_);
                                                        lean_dec(v___x_3790_);
                                                        v___x_3794_ = lean_box(0);
                                                        v_isShared_3795_ = v_isSharedCheck_3807_;
                                                        state = 1;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec(v_res_3789_);
                                                    lean_dec(v_res_3786_);
                                                    lean_dec(v_res_3783_);
                                                    lean_dec(v_res_3780_);
                                                    lean_dec(v_res_3777_);
                                                    lean_dec(v_res_3771_);
                                                    v_pos_3808_ = lean_ctor_get(v___x_3790_, 0);
                                                    v_err_3809_ = lean_ctor_get(v___x_3790_, 1);
                                                    v_isSharedCheck_3816_ =
                                                        (!lean_is_exclusive(v___x_3790_)) as u8;
                                                    if v_isSharedCheck_3816_ == 0 {
                                                        v___x_3811_ = v___x_3790_;
                                                        v_isShared_3812_ = v_isSharedCheck_3816_;
                                                        state = 3;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_err_3809_);
                                                        lean_inc(v_pos_3808_);
                                                        lean_dec(v___x_3790_);
                                                        v___x_3811_ = lean_box(0);
                                                        v_isShared_3812_ = v_isSharedCheck_3816_;
                                                        state = 3;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                lean_dec(v_res_3786_);
                                                lean_dec(v_res_3783_);
                                                lean_dec(v_res_3780_);
                                                lean_dec(v_res_3777_);
                                                lean_dec(v_res_3771_);
                                                v_pos_3817_ = lean_ctor_get(v___x_3787_, 0);
                                                v_err_3818_ = lean_ctor_get(v___x_3787_, 1);
                                                v_isSharedCheck_3825_ =
                                                    (!lean_is_exclusive(v___x_3787_)) as u8;
                                                if v_isSharedCheck_3825_ == 0 {
                                                    v___x_3820_ = v___x_3787_;
                                                    v_isShared_3821_ = v_isSharedCheck_3825_;
                                                    state = 5;
                                                    continue;
                                                } else {
                                                    lean_inc(v_err_3818_);
                                                    lean_inc(v_pos_3817_);
                                                    lean_dec(v___x_3787_);
                                                    v___x_3820_ = lean_box(0);
                                                    v_isShared_3821_ = v_isSharedCheck_3825_;
                                                    state = 5;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_res_3783_);
                                            lean_dec(v_res_3780_);
                                            lean_dec(v_res_3777_);
                                            lean_dec(v_res_3771_);
                                            v_pos_3826_ = lean_ctor_get(v___x_3784_, 0);
                                            v_err_3827_ = lean_ctor_get(v___x_3784_, 1);
                                            v_isSharedCheck_3834_ =
                                                (!lean_is_exclusive(v___x_3784_)) as u8;
                                            if v_isSharedCheck_3834_ == 0 {
                                                v___x_3829_ = v___x_3784_;
                                                v_isShared_3830_ = v_isSharedCheck_3834_;
                                                state = 7;
                                                continue;
                                            } else {
                                                lean_inc(v_err_3827_);
                                                lean_inc(v_pos_3826_);
                                                lean_dec(v___x_3784_);
                                                v___x_3829_ = lean_box(0);
                                                v_isShared_3830_ = v_isSharedCheck_3834_;
                                                state = 7;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_res_3780_);
                                        lean_dec(v_res_3777_);
                                        lean_dec(v_res_3771_);
                                        v_pos_3835_ = lean_ctor_get(v___x_3781_, 0);
                                        v_err_3836_ = lean_ctor_get(v___x_3781_, 1);
                                        v_isSharedCheck_3843_ =
                                            (!lean_is_exclusive(v___x_3781_)) as u8;
                                        if v_isSharedCheck_3843_ == 0 {
                                            v___x_3838_ = v___x_3781_;
                                            v_isShared_3839_ = v_isSharedCheck_3843_;
                                            state = 9;
                                            continue;
                                        } else {
                                            lean_inc(v_err_3836_);
                                            lean_inc(v_pos_3835_);
                                            lean_dec(v___x_3781_);
                                            v___x_3838_ = lean_box(0);
                                            v_isShared_3839_ = v_isSharedCheck_3843_;
                                            state = 9;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_res_3777_);
                                    lean_dec(v_res_3771_);
                                    v_pos_3844_ = lean_ctor_get(v___x_3778_, 0);
                                    v_err_3845_ = lean_ctor_get(v___x_3778_, 1);
                                    v_isSharedCheck_3852_ = (!lean_is_exclusive(v___x_3778_)) as u8;
                                    if v_isSharedCheck_3852_ == 0 {
                                        v___x_3847_ = v___x_3778_;
                                        v_isShared_3848_ = v_isSharedCheck_3852_;
                                        state = 11;
                                        continue;
                                    } else {
                                        lean_inc(v_err_3845_);
                                        lean_inc(v_pos_3844_);
                                        lean_dec(v___x_3778_);
                                        v___x_3847_ = lean_box(0);
                                        v_isShared_3848_ = v_isSharedCheck_3852_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_res_3771_);
                                v_pos_3853_ = lean_ctor_get(v___x_3775_, 0);
                                v_err_3854_ = lean_ctor_get(v___x_3775_, 1);
                                v_isSharedCheck_3861_ = (!lean_is_exclusive(v___x_3775_)) as u8;
                                if v_isSharedCheck_3861_ == 0 {
                                    v___x_3856_ = v___x_3775_;
                                    v_isShared_3857_ = v_isSharedCheck_3861_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_err_3854_);
                                    lean_inc(v_pos_3853_);
                                    lean_dec(v___x_3775_);
                                    v___x_3856_ = lean_box(0);
                                    v_isShared_3857_ = v_isSharedCheck_3861_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_res_3771_);
                            v_pos_3862_ = lean_ctor_get(v___x_3773_, 0);
                            v_err_3863_ = lean_ctor_get(v___x_3773_, 1);
                            v_isSharedCheck_3870_ = (!lean_is_exclusive(v___x_3773_)) as u8;
                            if v_isSharedCheck_3870_ == 0 {
                                v___x_3865_ = v___x_3773_;
                                v_isShared_3866_ = v_isSharedCheck_3870_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_err_3863_);
                                lean_inc(v_pos_3862_);
                                lean_dec(v___x_3773_);
                                v___x_3865_ = lean_box(0);
                                v_isShared_3866_ = v_isSharedCheck_3870_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        v_pos_3871_ = lean_ctor_get(v___x_3769_, 0);
                        v_isSharedCheck_3879_ = (!lean_is_exclusive(v___x_3769_)) as u8;
                        if v_isSharedCheck_3879_ == 0 {
                            v_unused_3880_ = lean_ctor_get(v___x_3769_, 1);
                            lean_dec(v_unused_3880_);
                            v___x_3873_ = v___x_3769_;
                            v_isShared_3874_ = v_isSharedCheck_3879_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_pos_3871_);
                            lean_dec(v___x_3769_);
                            v___x_3873_ = lean_box(0);
                            v_isShared_3874_ = v_isSharedCheck_3879_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    v_pos_3881_ = lean_ctor_get(v___x_3767_, 0);
                    v_err_3882_ = lean_ctor_get(v___x_3767_, 1);
                    v_isSharedCheck_3889_ = (!lean_is_exclusive(v___x_3767_)) as u8;
                    if v_isSharedCheck_3889_ == 0 {
                        v___x_3884_ = v___x_3767_;
                        v_isShared_3885_ = v_isSharedCheck_3889_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_err_3882_);
                        lean_inc(v_pos_3881_);
                        lean_dec(v___x_3767_);
                        v___x_3884_ = lean_box(0);
                        v_isShared_3885_ = v_isSharedCheck_3889_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3796_ = lean_alloc_ctor(0, 0, (25) as u32);
                v___x_3797_ = (lean_unbox(v_res_3771_) as u8);
                lean_dec(v_res_3771_);
                lean_ctor_set_uint8(v___x_3796_, 24 as u32, v___x_3797_);
                v___x_3798_ = lean_unbox_uint32(v_res_3777_);
                lean_dec(v_res_3777_);
                lean_ctor_set_uint32(v___x_3796_, 0 as u32, v___x_3798_);
                v___x_3799_ = lean_unbox_uint32(v_res_3780_);
                lean_dec(v_res_3780_);
                lean_ctor_set_uint32(v___x_3796_, 4 as u32, v___x_3799_);
                v___x_3800_ = lean_unbox_uint32(v_res_3783_);
                lean_dec(v_res_3783_);
                lean_ctor_set_uint32(v___x_3796_, 8 as u32, v___x_3800_);
                v___x_3801_ = lean_unbox_uint32(v_res_3786_);
                lean_dec(v_res_3786_);
                lean_ctor_set_uint32(v___x_3796_, 12 as u32, v___x_3801_);
                v___x_3802_ = lean_unbox_uint32(v_res_3789_);
                lean_dec(v_res_3789_);
                lean_ctor_set_uint32(v___x_3796_, 16 as u32, v___x_3802_);
                v___x_3803_ = lean_unbox_uint32(v_res_3792_);
                lean_dec(v_res_3792_);
                lean_ctor_set_uint32(v___x_3796_, 20 as u32, v___x_3803_);
                if v_isShared_3795_ == 0 {
                    lean_ctor_set(v___x_3794_, 1, v___x_3796_);
                    v___x_3805_ = v___x_3794_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_pos_3791_);
                    lean_ctor_set(v_reuseFailAlloc_3806_, 1, v___x_3796_);
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
                    v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_pos_3808_);
                    lean_ctor_set(v_reuseFailAlloc_3815_, 1, v_err_3809_);
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
                    v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_pos_3817_);
                    lean_ctor_set(v_reuseFailAlloc_3824_, 1, v_err_3818_);
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
                    v_reuseFailAlloc_3833_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_pos_3826_);
                    lean_ctor_set(v_reuseFailAlloc_3833_, 1, v_err_3827_);
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
                    v_reuseFailAlloc_3842_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_pos_3835_);
                    lean_ctor_set(v_reuseFailAlloc_3842_, 1, v_err_3836_);
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
                    v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_pos_3844_);
                    lean_ctor_set(v_reuseFailAlloc_3851_, 1, v_err_3845_);
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
                    v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_pos_3853_);
                    lean_ctor_set(v_reuseFailAlloc_3860_, 1, v_err_3854_);
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
                    v_reuseFailAlloc_3869_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_pos_3862_);
                    lean_ctor_set(v_reuseFailAlloc_3869_, 1, v_err_3863_);
                    v___x_3868_ = v_reuseFailAlloc_3869_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3868_;
            }
            17 => {
                v___x_3875_ = lean_box(0);
                if v_isShared_3874_ == 0 {
                    lean_ctor_set(v___x_3873_, 1, v___x_3875_);
                    v___x_3877_ = v___x_3873_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_pos_3871_);
                    lean_ctor_set(v_reuseFailAlloc_3878_, 1, v___x_3875_);
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
                    v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_pos_3881_);
                    lean_ctor_set(v_reuseFailAlloc_3888_, 1, v_err_3882_);
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
    mut v_a_3890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3902_: u8 = 0;
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: u8 = 0;
    let mut v___x_3905_: u8 = 0;
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3909_: u8 = 0;
    let mut v_pos_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3913_: u8 = 0;
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3918_: u8 = 0;
    let mut v_unused_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3923_: u8 = 0;
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3928_: u8 = 0;
    let mut v_unused_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3934_: u8 = 0;
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3938_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3891_ =
                    l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi32(
                        v_a_3890_,
                    );
                if lean_obj_tag(v___x_3891_) == 0 {
                    v_pos_3892_ = lean_ctor_get(v___x_3891_, 0);
                    lean_inc(v_pos_3892_);
                    v_res_3893_ = lean_ctor_get(v___x_3891_, 1);
                    lean_inc(v_res_3893_);
                    lean_dec_ref_known(v___x_3891_, 2);
                    v___x_3894_ =
                        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pbool(
                            v_pos_3892_,
                        );
                    if lean_obj_tag(v___x_3894_) == 0 {
                        v_pos_3895_ = lean_ctor_get(v___x_3894_, 0);
                        lean_inc(v_pos_3895_);
                        v_res_3896_ = lean_ctor_get(v___x_3894_, 1);
                        lean_inc(v_res_3896_);
                        lean_dec_ref_known(v___x_3894_, 2);
                        v___x_3897_ =
                            l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(
                                v_pos_3895_,
                            );
                        if lean_obj_tag(v___x_3897_) == 0 {
                            v_pos_3898_ = lean_ctor_get(v___x_3897_, 0);
                            v_res_3899_ = lean_ctor_get(v___x_3897_, 1);
                            v_isSharedCheck_3909_ = (!lean_is_exclusive(v___x_3897_)) as u8;
                            if v_isSharedCheck_3909_ == 0 {
                                v___x_3901_ = v___x_3897_;
                                v_isShared_3902_ = v_isSharedCheck_3909_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_res_3899_);
                                lean_inc(v_pos_3898_);
                                lean_dec(v___x_3897_);
                                v___x_3901_ = lean_box(0);
                                v_isShared_3902_ = v_isSharedCheck_3909_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_res_3896_);
                            lean_dec(v_res_3893_);
                            v_pos_3910_ = lean_ctor_get(v___x_3897_, 0);
                            v_isSharedCheck_3918_ = (!lean_is_exclusive(v___x_3897_)) as u8;
                            if v_isSharedCheck_3918_ == 0 {
                                v_unused_3919_ = lean_ctor_get(v___x_3897_, 1);
                                lean_dec(v_unused_3919_);
                                v___x_3912_ = v___x_3897_;
                                v_isShared_3913_ = v_isSharedCheck_3918_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_pos_3910_);
                                lean_dec(v___x_3897_);
                                v___x_3912_ = lean_box(0);
                                v_isShared_3913_ = v_isSharedCheck_3918_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_res_3893_);
                        v_pos_3920_ = lean_ctor_get(v___x_3894_, 0);
                        v_isSharedCheck_3928_ = (!lean_is_exclusive(v___x_3894_)) as u8;
                        if v_isSharedCheck_3928_ == 0 {
                            v_unused_3929_ = lean_ctor_get(v___x_3894_, 1);
                            lean_dec(v_unused_3929_);
                            v___x_3922_ = v___x_3894_;
                            v_isShared_3923_ = v_isSharedCheck_3928_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_pos_3920_);
                            lean_dec(v___x_3894_);
                            v___x_3922_ = lean_box(0);
                            v_isShared_3923_ = v_isSharedCheck_3928_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_pos_3930_ = lean_ctor_get(v___x_3891_, 0);
                    v_err_3931_ = lean_ctor_get(v___x_3891_, 1);
                    v_isSharedCheck_3938_ = (!lean_is_exclusive(v___x_3891_)) as u8;
                    if v_isSharedCheck_3938_ == 0 {
                        v___x_3933_ = v___x_3891_;
                        v_isShared_3934_ = v_isSharedCheck_3938_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_err_3931_);
                        lean_inc(v_pos_3930_);
                        lean_dec(v___x_3891_);
                        v___x_3933_ = lean_box(0);
                        v_isShared_3934_ = v_isSharedCheck_3938_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3903_ = lean_alloc_ctor(0, 1, (2) as u32);
                lean_ctor_set(v___x_3903_, 0, v_res_3893_);
                v___x_3904_ = (lean_unbox(v_res_3896_) as u8);
                lean_dec(v_res_3896_);
                lean_ctor_set_uint8(
                    v___x_3903_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3904_,
                );
                v___x_3905_ = (lean_unbox(v_res_3899_) as u8);
                lean_dec(v_res_3899_);
                lean_ctor_set_uint8(
                    v___x_3903_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v___x_3905_,
                );
                if v_isShared_3902_ == 0 {
                    lean_ctor_set(v___x_3901_, 1, v___x_3903_);
                    v___x_3907_ = v___x_3901_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_pos_3898_);
                    lean_ctor_set(v_reuseFailAlloc_3908_, 1, v___x_3903_);
                    v___x_3907_ = v_reuseFailAlloc_3908_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3907_;
            }
            3 => {
                v___x_3914_ = lean_box(0);
                if v_isShared_3913_ == 0 {
                    lean_ctor_set(v___x_3912_, 1, v___x_3914_);
                    v___x_3916_ = v___x_3912_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3917_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_pos_3910_);
                    lean_ctor_set(v_reuseFailAlloc_3917_, 1, v___x_3914_);
                    v___x_3916_ = v_reuseFailAlloc_3917_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3916_;
            }
            5 => {
                v___x_3924_ = lean_box(0);
                if v_isShared_3923_ == 0 {
                    lean_ctor_set(v___x_3922_, 1, v___x_3924_);
                    v___x_3926_ = v___x_3922_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_pos_3920_);
                    lean_ctor_set(v_reuseFailAlloc_3927_, 1, v___x_3924_);
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
                    v_reuseFailAlloc_3937_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_pos_3930_);
                    lean_ctor_set(v_reuseFailAlloc_3937_, 1, v_err_3931_);
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
    mut v_p_3939_: *mut LeanObject,
    mut v_a_3940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3949_: u8 = 0;
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3954_: u8 = 0;
    let mut v_pos_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3959_: u8 = 0;
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3963_: u8 = 0;
    let mut v_pos_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3968_: u8 = 0;
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3972_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3941_ = lean_apply_1(v_p_3939_, v_a_3940_);
                if lean_obj_tag(v___x_3941_) == 0 {
                    v_pos_3942_ = lean_ctor_get(v___x_3941_, 0);
                    lean_inc(v_pos_3942_);
                    v_res_3943_ = lean_ctor_get(v___x_3941_, 1);
                    lean_inc(v_res_3943_);
                    lean_dec_ref_known(v___x_3941_, 2);
                    v___x_3944_ =
                        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi32(
                            v_pos_3942_,
                        );
                    if lean_obj_tag(v___x_3944_) == 0 {
                        v_pos_3945_ = lean_ctor_get(v___x_3944_, 0);
                        v_res_3946_ = lean_ctor_get(v___x_3944_, 1);
                        v_isSharedCheck_3954_ = (!lean_is_exclusive(v___x_3944_)) as u8;
                        if v_isSharedCheck_3954_ == 0 {
                            v___x_3948_ = v___x_3944_;
                            v_isShared_3949_ = v_isSharedCheck_3954_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_res_3946_);
                            lean_inc(v_pos_3945_);
                            lean_dec(v___x_3944_);
                            v___x_3948_ = lean_box(0);
                            v_isShared_3949_ = v_isSharedCheck_3954_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_res_3943_);
                        v_pos_3955_ = lean_ctor_get(v___x_3944_, 0);
                        v_err_3956_ = lean_ctor_get(v___x_3944_, 1);
                        v_isSharedCheck_3963_ = (!lean_is_exclusive(v___x_3944_)) as u8;
                        if v_isSharedCheck_3963_ == 0 {
                            v___x_3958_ = v___x_3944_;
                            v_isShared_3959_ = v_isSharedCheck_3963_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_err_3956_);
                            lean_inc(v_pos_3955_);
                            lean_dec(v___x_3944_);
                            v___x_3958_ = lean_box(0);
                            v_isShared_3959_ = v_isSharedCheck_3963_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_pos_3964_ = lean_ctor_get(v___x_3941_, 0);
                    v_err_3965_ = lean_ctor_get(v___x_3941_, 1);
                    v_isSharedCheck_3972_ = (!lean_is_exclusive(v___x_3941_)) as u8;
                    if v_isSharedCheck_3972_ == 0 {
                        v___x_3967_ = v___x_3941_;
                        v_isShared_3968_ = v_isSharedCheck_3972_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_err_3965_);
                        lean_inc(v_pos_3964_);
                        lean_dec(v___x_3941_);
                        v___x_3967_ = lean_box(0);
                        v_isShared_3968_ = v_isSharedCheck_3972_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3950_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3950_, 0, v_res_3943_);
                lean_ctor_set(v___x_3950_, 1, v_res_3946_);
                if v_isShared_3949_ == 0 {
                    lean_ctor_set(v___x_3948_, 1, v___x_3950_);
                    v___x_3952_ = v___x_3948_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_pos_3945_);
                    lean_ctor_set(v_reuseFailAlloc_3953_, 1, v___x_3950_);
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
                    v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_pos_3955_);
                    lean_ctor_set(v_reuseFailAlloc_3962_, 1, v_err_3956_);
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
                    v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_pos_3964_);
                    lean_ctor_set(v_reuseFailAlloc_3971_, 1, v_err_3965_);
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
    mut v_size_3973_: *mut LeanObject,
    mut v_n_3974_: u32,
    mut v_a_3975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
    v___x_3976_ = lean_uint32_to_nat(v_n_3974_);
    v___x_3977_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(
        v___x_3976_,
        v_size_3973_,
        v_a_3975_,
    );
    lean_dec(v___x_3976_);
    return v___x_3977_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes___boxed(
    mut v_size_3978_: *mut LeanObject,
    mut v_n_3979_: *mut LeanObject,
    mut v_a_3980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_n_boxed_3981_: u32 = 0;
    let mut v_res_3982_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_3981_ = lean_unbox_uint32(v_n_3979_);
    lean_dec(v_n_3979_);
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
    mut v_a_3984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    v___x_3985_ = lean_uint32_to_nat(v_n_3983_);
    v___x_3986_ = lean_alloc_closure(
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
    lean_dec(v___x_3985_);
    return v___x_3987_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices___boxed(
    mut v_n_3988_: *mut LeanObject,
    mut v_a_3989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_n_boxed_3990_: u32 = 0;
    let mut v_res_3991_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_3990_ = lean_unbox_uint32(v_n_3988_);
    lean_dec(v_n_3988_);
    v_res_3991_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(
            v_n_boxed_3990_,
            v_a_3989_,
        );
    return v_res_3991_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(
    mut v_n_3992_: u32,
    mut v_a_3993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    v___x_3994_ = lean_uint32_to_nat(v_n_3992_);
    v___x_3995_ = lean_alloc_closure(
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
    lean_dec(v___x_3994_);
    return v___x_3996_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes___boxed(
    mut v_n_3997_: *mut LeanObject,
    mut v_a_3998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_n_boxed_3999_: u32 = 0;
    let mut v_res_4000_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_3999_ = lean_unbox_uint32(v_n_3997_);
    lean_dec(v_n_3997_);
    v_res_4000_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(
            v_n_boxed_3999_,
            v_a_3998_,
        );
    return v_res_4000_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(
    mut v_upperBound_4002_: *mut LeanObject,
    mut v_res_4003_: *mut LeanObject,
    mut v_a_4004_: *mut LeanObject,
    mut v_b_4005_: *mut LeanObject,
    mut v___y_4006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4007_: u8 = 0;
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4013_: u8 = 0;
    let mut v___x_4014_: u8 = 0;
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: u8 = 0;
    let mut v___x_4018_: u8 = 0;
    let mut v___x_4019_: u8 = 0;
    let mut v___x_4020_: u8 = 0;
    let mut v___x_4021_: u32 = 0;
    let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_current_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4035_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4007_ = lean_nat_dec_lt(v_a_4004_, v_upperBound_4002_);
                if v___x_4007_ == 0 {
                    lean_dec(v_a_4004_);
                    v___x_4008_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4008_, 0, v___y_4006_);
                    lean_ctor_set(v___x_4008_, 1, v_b_4005_);
                    return v___x_4008_;
                } else {
                    v_fst_4009_ = lean_ctor_get(v_b_4005_, 0);
                    v_snd_4010_ = lean_ctor_get(v_b_4005_, 1);
                    v_isSharedCheck_4035_ = (!lean_is_exclusive(v_b_4005_)) as u8;
                    if v_isSharedCheck_4035_ == 0 {
                        v___x_4012_ = v_b_4005_;
                        v_isShared_4013_ = v_isSharedCheck_4035_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4010_);
                        lean_inc(v_fst_4009_);
                        lean_dec(v_b_4005_);
                        v___x_4012_ = lean_box(0);
                        v_isShared_4013_ = v_isSharedCheck_4035_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4014_ = l_instInhabitedUInt8;
                v___x_4015_ = lean_box((v___x_4014_) as usize);
                v___x_4016_ = lean_array_get(v___x_4015_, v_res_4003_, v_a_4004_);
                lean_dec(v___x_4015_);
                v___x_4017_ = 0;
                v___x_4018_ = (lean_unbox(v___x_4016_) as u8);
                v___x_4019_ = lean_uint8_dec_eq(v___x_4018_, v___x_4017_);
                if v___x_4019_ == 0 {
                    v___x_4020_ = (lean_unbox(v___x_4016_) as u8);
                    lean_dec(v___x_4016_);
                    v___x_4021_ = lean_uint8_to_uint32(v___x_4020_);
                    v___x_4022_ = lean_string_push(v_snd_4010_, v___x_4021_);
                    if v_isShared_4013_ == 0 {
                        lean_ctor_set(v___x_4012_, 1, v___x_4022_);
                        v___x_4024_ = v___x_4012_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4028_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_fst_4009_);
                        lean_ctor_set(v_reuseFailAlloc_4028_, 1, v___x_4022_);
                        v___x_4024_ = v_reuseFailAlloc_4028_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4016_);
                    lean_dec(v_a_4004_);
                    v_current_4029_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0;
                    v___x_4030_ = lean_array_push(v_fst_4009_, v_snd_4010_);
                    if v_isShared_4013_ == 0 {
                        lean_ctor_set(v___x_4012_, 1, v_current_4029_);
                        lean_ctor_set(v___x_4012_, 0, v___x_4030_);
                        v___x_4032_ = v___x_4012_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4034_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4034_, 0, v___x_4030_);
                        lean_ctor_set(v_reuseFailAlloc_4034_, 1, v_current_4029_);
                        v___x_4032_ = v_reuseFailAlloc_4034_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4025_ = lean_unsigned_to_nat(1);
                v___x_4026_ = lean_nat_add(v_a_4004_, v___x_4025_);
                lean_dec(v_a_4004_);
                v_a_4004_ = v___x_4026_;
                v_b_4005_ = v___x_4024_;
                state = 0;
                continue;
            }
            3 => {
                v___x_4033_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4033_, 0, v___y_4006_);
                lean_ctor_set(v___x_4033_, 1, v___x_4032_);
                return v___x_4033_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___boxed(
    mut v_upperBound_4036_: *mut LeanObject,
    mut v_res_4037_: *mut LeanObject,
    mut v_a_4038_: *mut LeanObject,
    mut v_b_4039_: *mut LeanObject,
    mut v___y_4040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4041_: *mut LeanObject = core::ptr::null_mut();
    v_res_4041_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(v_upperBound_4036_, v_res_4037_, v_a_4038_, v_b_4039_, v___y_4040_);
    lean_dec_ref(v_res_4037_);
    lean_dec(v_upperBound_4036_);
    return v_res_4041_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1(
    mut v___x_4042_: *mut LeanObject,
    mut v_res_4043_: *mut LeanObject,
    mut v_as_4044_: *mut LeanObject,
    mut v_sz_4045_: usize,
    mut v_i_4046_: usize,
    mut v_b_4047_: *mut LeanObject,
    mut v___y_4048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4049_: u8 = 0;
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abbreviationIndex_4052_: u8 = 0;
    let mut v_fst_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4057_: u8 = 0;
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4068_: u8 = 0;
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: usize = 0;
    let mut v___x_4072_: usize = 0;
    let mut v_reuseFailAlloc_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4075_: u8 = 0;
    let mut v_reuseFailAlloc_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4077_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4049_ = lean_usize_dec_lt(v_i_4046_, v_sz_4045_);
                if v___x_4049_ == 0 {
                    v___x_4050_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4050_, 0, v___y_4048_);
                    lean_ctor_set(v___x_4050_, 1, v_b_4047_);
                    return v___x_4050_;
                } else {
                    v_a_4051_ = lean_array_uget_borrowed(v_as_4044_, v_i_4046_);
                    v_abbreviationIndex_4052_ = lean_ctor_get_uint8(
                        v_a_4051_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    );
                    v_fst_4053_ = lean_ctor_get(v_b_4047_, 0);
                    v_snd_4054_ = lean_ctor_get(v_b_4047_, 1);
                    v_isSharedCheck_4077_ = (!lean_is_exclusive(v_b_4047_)) as u8;
                    if v_isSharedCheck_4077_ == 0 {
                        v___x_4056_ = v_b_4047_;
                        v_isShared_4057_ = v_isSharedCheck_4077_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4054_);
                        lean_inc(v_fst_4053_);
                        lean_dec(v_b_4047_);
                        v___x_4056_ = lean_box(0);
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
                    v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_fst_4053_);
                    lean_ctor_set(v_reuseFailAlloc_4076_, 1, v_snd_4054_);
                    v___x_4060_ = v_reuseFailAlloc_4076_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4061_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(v___x_4042_, v_res_4043_, v___x_4058_, v___x_4060_, v___y_4048_);
                if lean_obj_tag(v___x_4061_) == 0 {
                    v_res_4062_ = lean_ctor_get(v___x_4061_, 1);
                    lean_inc(v_res_4062_);
                    v_pos_4063_ = lean_ctor_get(v___x_4061_, 0);
                    lean_inc(v_pos_4063_);
                    lean_dec_ref_known(v___x_4061_, 2);
                    v_fst_4064_ = lean_ctor_get(v_res_4062_, 0);
                    v_snd_4065_ = lean_ctor_get(v_res_4062_, 1);
                    v_isSharedCheck_4075_ = (!lean_is_exclusive(v_res_4062_)) as u8;
                    if v_isSharedCheck_4075_ == 0 {
                        v___x_4067_ = v_res_4062_;
                        v_isShared_4068_ = v_isSharedCheck_4075_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_snd_4065_);
                        lean_inc(v_fst_4064_);
                        lean_dec(v_res_4062_);
                        v___x_4067_ = lean_box(0);
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
                    v_reuseFailAlloc_4074_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_fst_4064_);
                    lean_ctor_set(v_reuseFailAlloc_4074_, 1, v_snd_4065_);
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
    mut v___x_4078_: *mut LeanObject,
    mut v_res_4079_: *mut LeanObject,
    mut v_as_4080_: *mut LeanObject,
    mut v_sz_4081_: *mut LeanObject,
    mut v_i_4082_: *mut LeanObject,
    mut v_b_4083_: *mut LeanObject,
    mut v___y_4084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4085_: usize = 0;
    let mut v_i_boxed_4086_: usize = 0;
    let mut v_res_4087_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4085_ = lean_unbox_usize(v_sz_4081_);
    lean_dec(v_sz_4081_);
    v_i_boxed_4086_ = lean_unbox_usize(v_i_4082_);
    lean_dec(v_i_4082_);
    v_res_4087_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1(v___x_4078_, v_res_4079_, v_as_4080_, v_sz_boxed_4085_, v_i_boxed_4086_, v_b_4083_, v___y_4084_);
    lean_dec_ref(v_as_4080_);
    lean_dec_ref(v_res_4079_);
    lean_dec(v___x_4078_);
    return v_res_4087_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(
    mut v_times_4093_: *mut LeanObject,
    mut v_n_4094_: u32,
    mut v_a_4095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4102_: usize = 0;
    let mut v___x_4103_: usize = 0;
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4109_: u8 = 0;
    let mut v_fst_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4114_: u8 = 0;
    let mut v_pos_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4119_: u8 = 0;
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4123_: u8 = 0;
    let mut v_pos_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4128_: u8 = 0;
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4132_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4096_ = lean_uint32_to_nat(v_n_4094_);
                v___x_4097_ = lean_alloc_closure(
                    l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8
                        as *mut core::ffi::c_void,
                    1,
                    0,
                );
                v___x_4098_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(v___x_4096_, v___x_4097_, v_a_4095_);
                if lean_obj_tag(v___x_4098_) == 0 {
                    v_pos_4099_ = lean_ctor_get(v___x_4098_, 0);
                    lean_inc(v_pos_4099_);
                    v_res_4100_ = lean_ctor_get(v___x_4098_, 1);
                    lean_inc(v_res_4100_);
                    lean_dec_ref_known(v___x_4098_, 2);
                    v___x_4101_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations___closed__1;
                    v_sz_4102_ = lean_array_size(v_times_4093_);
                    v___x_4103_ = 0usize;
                    v___x_4104_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__1(v___x_4096_, v_res_4100_, v_times_4093_, v_sz_4102_, v___x_4103_, v___x_4101_, v_pos_4099_);
                    lean_dec(v_res_4100_);
                    lean_dec(v___x_4096_);
                    if lean_obj_tag(v___x_4104_) == 0 {
                        v_res_4105_ = lean_ctor_get(v___x_4104_, 1);
                        v_pos_4106_ = lean_ctor_get(v___x_4104_, 0);
                        v_isSharedCheck_4114_ = (!lean_is_exclusive(v___x_4104_)) as u8;
                        if v_isSharedCheck_4114_ == 0 {
                            v___x_4108_ = v___x_4104_;
                            v_isShared_4109_ = v_isSharedCheck_4114_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_res_4105_);
                            lean_inc(v_pos_4106_);
                            lean_dec(v___x_4104_);
                            v___x_4108_ = lean_box(0);
                            v_isShared_4109_ = v_isSharedCheck_4114_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_pos_4115_ = lean_ctor_get(v___x_4104_, 0);
                        v_err_4116_ = lean_ctor_get(v___x_4104_, 1);
                        v_isSharedCheck_4123_ = (!lean_is_exclusive(v___x_4104_)) as u8;
                        if v_isSharedCheck_4123_ == 0 {
                            v___x_4118_ = v___x_4104_;
                            v_isShared_4119_ = v_isSharedCheck_4123_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_err_4116_);
                            lean_inc(v_pos_4115_);
                            lean_dec(v___x_4104_);
                            v___x_4118_ = lean_box(0);
                            v_isShared_4119_ = v_isSharedCheck_4123_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_4096_);
                    v_pos_4124_ = lean_ctor_get(v___x_4098_, 0);
                    v_err_4125_ = lean_ctor_get(v___x_4098_, 1);
                    v_isSharedCheck_4132_ = (!lean_is_exclusive(v___x_4098_)) as u8;
                    if v_isSharedCheck_4132_ == 0 {
                        v___x_4127_ = v___x_4098_;
                        v_isShared_4128_ = v_isSharedCheck_4132_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_err_4125_);
                        lean_inc(v_pos_4124_);
                        lean_dec(v___x_4098_);
                        v___x_4127_ = lean_box(0);
                        v_isShared_4128_ = v_isSharedCheck_4132_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4110_ = lean_ctor_get(v_res_4105_, 0);
                lean_inc(v_fst_4110_);
                lean_dec(v_res_4105_);
                if v_isShared_4109_ == 0 {
                    lean_ctor_set(v___x_4108_, 1, v_fst_4110_);
                    v___x_4112_ = v___x_4108_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4113_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_pos_4106_);
                    lean_ctor_set(v_reuseFailAlloc_4113_, 1, v_fst_4110_);
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
                    v_reuseFailAlloc_4122_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_pos_4115_);
                    lean_ctor_set(v_reuseFailAlloc_4122_, 1, v_err_4116_);
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
                    v_reuseFailAlloc_4131_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_pos_4124_);
                    lean_ctor_set(v_reuseFailAlloc_4131_, 1, v_err_4125_);
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
    mut v_times_4133_: *mut LeanObject,
    mut v_n_4134_: *mut LeanObject,
    mut v_a_4135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_n_boxed_4136_: u32 = 0;
    let mut v_res_4137_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_4136_ = lean_unbox_uint32(v_n_4134_);
    lean_dec(v_n_4134_);
    v_res_4137_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(
            v_times_4133_,
            v_n_boxed_4136_,
            v_a_4135_,
        );
    lean_dec_ref(v_times_4133_);
    return v_res_4137_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0(
    mut v_upperBound_4138_: *mut LeanObject,
    mut v_res_4139_: *mut LeanObject,
    mut v_inst_4140_: *mut LeanObject,
    mut v_R_4141_: *mut LeanObject,
    mut v_a_4142_: *mut LeanObject,
    mut v_b_4143_: *mut LeanObject,
    mut v_c_4144_: *mut LeanObject,
    mut v___y_4145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    v___x_4146_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg(v_upperBound_4138_, v_res_4139_, v_a_4142_, v_b_4143_, v___y_4145_);
    return v___x_4146_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___boxed(
    mut v_upperBound_4147_: *mut LeanObject,
    mut v_res_4148_: *mut LeanObject,
    mut v_inst_4149_: *mut LeanObject,
    mut v_R_4150_: *mut LeanObject,
    mut v_a_4151_: *mut LeanObject,
    mut v_b_4152_: *mut LeanObject,
    mut v_c_4153_: *mut LeanObject,
    mut v___y_4154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4155_: *mut LeanObject = core::ptr::null_mut();
    v_res_4155_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0(v_upperBound_4147_, v_res_4148_, v_inst_4149_, v_R_4150_, v_a_4151_, v_b_4152_, v_c_4153_, v___y_4154_);
    lean_dec_ref(v_res_4148_);
    lean_dec(v_upperBound_4147_);
    return v_res_4155_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(
    mut v_size_4156_: *mut LeanObject,
    mut v_n_4157_: u32,
    mut v_a_4158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    v___x_4159_ = lean_uint32_to_nat(v_n_4157_);
    v___x_4160_ = lean_alloc_closure(
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSecond
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___x_4160_, 0, v_size_4156_);
    v___x_4161_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_manyN___redArg(
        v___x_4159_,
        v___x_4160_,
        v_a_4158_,
    );
    lean_dec(v___x_4159_);
    return v___x_4161_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds___boxed(
    mut v_size_4162_: *mut LeanObject,
    mut v_n_4163_: *mut LeanObject,
    mut v_a_4164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_n_boxed_4165_: u32 = 0;
    let mut v_res_4166_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_4165_ = lean_unbox_uint32(v_n_4163_);
    lean_dec(v_n_4163_);
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
    mut v_a_4168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
    v___x_4169_ = lean_uint32_to_nat(v_n_4167_);
    v___x_4170_ = lean_alloc_closure(
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
    lean_dec(v___x_4169_);
    return v___x_4171_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators___boxed(
    mut v_n_4172_: *mut LeanObject,
    mut v_a_4173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_n_boxed_4174_: u32 = 0;
    let mut v_res_4175_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_4174_ = lean_unbox_uint32(v_n_4172_);
    lean_dec(v_n_4172_);
    v_res_4175_ =
        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(
            v_n_boxed_4174_,
            v_a_4173_,
        );
    return v_res_4175_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV1(
    mut v_a_4176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isutcnt_4180_: u32 = 0;
    let mut v_isstdcnt_4181_: u32 = 0;
    let mut v_leapcnt_4182_: u32 = 0;
    let mut v_timecnt_4183_: u32 = 0;
    let mut v_typecnt_4184_: u32 = 0;
    let mut v_charcnt_4185_: u32 = 0;
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4210_: u8 = 0;
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4215_: u8 = 0;
    let mut v_pos_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4220_: u8 = 0;
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4224_: u8 = 0;
    let mut v_pos_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4229_: u8 = 0;
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4233_: u8 = 0;
    let mut v_pos_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4238_: u8 = 0;
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4242_: u8 = 0;
    let mut v_pos_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4247_: u8 = 0;
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4251_: u8 = 0;
    let mut v_pos_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4256_: u8 = 0;
    let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4260_: u8 = 0;
    let mut v_pos_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4265_: u8 = 0;
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4269_: u8 = 0;
    let mut v_pos_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4274_: u8 = 0;
    let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4278_: u8 = 0;
    let mut v_pos_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4283_: u8 = 0;
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4287_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4177_ =
                    l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader(
                        v_a_4176_,
                    );
                if lean_obj_tag(v___x_4177_) == 0 {
                    v_res_4178_ = lean_ctor_get(v___x_4177_, 1);
                    lean_inc(v_res_4178_);
                    v_pos_4179_ = lean_ctor_get(v___x_4177_, 0);
                    lean_inc(v_pos_4179_);
                    lean_dec_ref_known(v___x_4177_, 2);
                    v_isutcnt_4180_ = lean_ctor_get_uint32(v_res_4178_, 0 as u32);
                    v_isstdcnt_4181_ = lean_ctor_get_uint32(v_res_4178_, 4 as u32);
                    v_leapcnt_4182_ = lean_ctor_get_uint32(v_res_4178_, 8 as u32);
                    v_timecnt_4183_ = lean_ctor_get_uint32(v_res_4178_, 12 as u32);
                    v_typecnt_4184_ = lean_ctor_get_uint32(v_res_4178_, 16 as u32);
                    v_charcnt_4185_ = lean_ctor_get_uint32(v_res_4178_, 20 as u32);
                    v___x_4186_ = lean_alloc_closure(
                        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi32
                            as *mut core::ffi::c_void,
                        1,
                        0,
                    );
                    lean_inc_ref(v___x_4186_);
                    v___x_4187_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes(v___x_4186_, v_timecnt_4183_, v_pos_4179_);
                    if lean_obj_tag(v___x_4187_) == 0 {
                        v_pos_4188_ = lean_ctor_get(v___x_4187_, 0);
                        lean_inc(v_pos_4188_);
                        v_res_4189_ = lean_ctor_get(v___x_4187_, 1);
                        lean_inc(v_res_4189_);
                        lean_dec_ref_known(v___x_4187_, 2);
                        v___x_4190_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(v_timecnt_4183_, v_pos_4188_);
                        if lean_obj_tag(v___x_4190_) == 0 {
                            v_pos_4191_ = lean_ctor_get(v___x_4190_, 0);
                            lean_inc(v_pos_4191_);
                            v_res_4192_ = lean_ctor_get(v___x_4190_, 1);
                            lean_inc(v_res_4192_);
                            lean_dec_ref_known(v___x_4190_, 2);
                            v___x_4193_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(v_typecnt_4184_, v_pos_4191_);
                            if lean_obj_tag(v___x_4193_) == 0 {
                                v_pos_4194_ = lean_ctor_get(v___x_4193_, 0);
                                lean_inc(v_pos_4194_);
                                v_res_4195_ = lean_ctor_get(v___x_4193_, 1);
                                lean_inc(v_res_4195_);
                                lean_dec_ref_known(v___x_4193_, 2);
                                v___x_4196_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(v_res_4195_, v_charcnt_4185_, v_pos_4194_);
                                if lean_obj_tag(v___x_4196_) == 0 {
                                    v_pos_4197_ = lean_ctor_get(v___x_4196_, 0);
                                    lean_inc(v_pos_4197_);
                                    v_res_4198_ = lean_ctor_get(v___x_4196_, 1);
                                    lean_inc(v_res_4198_);
                                    lean_dec_ref_known(v___x_4196_, 2);
                                    v___x_4199_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(v___x_4186_, v_leapcnt_4182_, v_pos_4197_);
                                    if lean_obj_tag(v___x_4199_) == 0 {
                                        v_pos_4200_ = lean_ctor_get(v___x_4199_, 0);
                                        lean_inc(v_pos_4200_);
                                        v_res_4201_ = lean_ctor_get(v___x_4199_, 1);
                                        lean_inc(v_res_4201_);
                                        lean_dec_ref_known(v___x_4199_, 2);
                                        v___x_4202_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_isstdcnt_4181_, v_pos_4200_);
                                        if lean_obj_tag(v___x_4202_) == 0 {
                                            v_pos_4203_ = lean_ctor_get(v___x_4202_, 0);
                                            lean_inc(v_pos_4203_);
                                            v_res_4204_ = lean_ctor_get(v___x_4202_, 1);
                                            lean_inc(v_res_4204_);
                                            lean_dec_ref_known(v___x_4202_, 2);
                                            v___x_4205_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_isutcnt_4180_, v_pos_4203_);
                                            if lean_obj_tag(v___x_4205_) == 0 {
                                                v_pos_4206_ = lean_ctor_get(v___x_4205_, 0);
                                                v_res_4207_ = lean_ctor_get(v___x_4205_, 1);
                                                v_isSharedCheck_4215_ =
                                                    (!lean_is_exclusive(v___x_4205_)) as u8;
                                                if v_isSharedCheck_4215_ == 0 {
                                                    v___x_4209_ = v___x_4205_;
                                                    v_isShared_4210_ = v_isSharedCheck_4215_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    lean_inc(v_res_4207_);
                                                    lean_inc(v_pos_4206_);
                                                    lean_dec(v___x_4205_);
                                                    v___x_4209_ = lean_box(0);
                                                    v_isShared_4210_ = v_isSharedCheck_4215_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec(v_res_4204_);
                                                lean_dec(v_res_4201_);
                                                lean_dec(v_res_4198_);
                                                lean_dec(v_res_4195_);
                                                lean_dec(v_res_4192_);
                                                lean_dec(v_res_4189_);
                                                lean_dec(v_res_4178_);
                                                v_pos_4216_ = lean_ctor_get(v___x_4205_, 0);
                                                v_err_4217_ = lean_ctor_get(v___x_4205_, 1);
                                                v_isSharedCheck_4224_ =
                                                    (!lean_is_exclusive(v___x_4205_)) as u8;
                                                if v_isSharedCheck_4224_ == 0 {
                                                    v___x_4219_ = v___x_4205_;
                                                    v_isShared_4220_ = v_isSharedCheck_4224_;
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    lean_inc(v_err_4217_);
                                                    lean_inc(v_pos_4216_);
                                                    lean_dec(v___x_4205_);
                                                    v___x_4219_ = lean_box(0);
                                                    v_isShared_4220_ = v_isSharedCheck_4224_;
                                                    state = 3;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_res_4201_);
                                            lean_dec(v_res_4198_);
                                            lean_dec(v_res_4195_);
                                            lean_dec(v_res_4192_);
                                            lean_dec(v_res_4189_);
                                            lean_dec(v_res_4178_);
                                            v_pos_4225_ = lean_ctor_get(v___x_4202_, 0);
                                            v_err_4226_ = lean_ctor_get(v___x_4202_, 1);
                                            v_isSharedCheck_4233_ =
                                                (!lean_is_exclusive(v___x_4202_)) as u8;
                                            if v_isSharedCheck_4233_ == 0 {
                                                v___x_4228_ = v___x_4202_;
                                                v_isShared_4229_ = v_isSharedCheck_4233_;
                                                state = 5;
                                                continue;
                                            } else {
                                                lean_inc(v_err_4226_);
                                                lean_inc(v_pos_4225_);
                                                lean_dec(v___x_4202_);
                                                v___x_4228_ = lean_box(0);
                                                v_isShared_4229_ = v_isSharedCheck_4233_;
                                                state = 5;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_res_4198_);
                                        lean_dec(v_res_4195_);
                                        lean_dec(v_res_4192_);
                                        lean_dec(v_res_4189_);
                                        lean_dec(v_res_4178_);
                                        v_pos_4234_ = lean_ctor_get(v___x_4199_, 0);
                                        v_err_4235_ = lean_ctor_get(v___x_4199_, 1);
                                        v_isSharedCheck_4242_ =
                                            (!lean_is_exclusive(v___x_4199_)) as u8;
                                        if v_isSharedCheck_4242_ == 0 {
                                            v___x_4237_ = v___x_4199_;
                                            v_isShared_4238_ = v_isSharedCheck_4242_;
                                            state = 7;
                                            continue;
                                        } else {
                                            lean_inc(v_err_4235_);
                                            lean_inc(v_pos_4234_);
                                            lean_dec(v___x_4199_);
                                            v___x_4237_ = lean_box(0);
                                            v_isShared_4238_ = v_isSharedCheck_4242_;
                                            state = 7;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_res_4195_);
                                    lean_dec(v_res_4192_);
                                    lean_dec(v_res_4189_);
                                    lean_dec_ref(v___x_4186_);
                                    lean_dec(v_res_4178_);
                                    v_pos_4243_ = lean_ctor_get(v___x_4196_, 0);
                                    v_err_4244_ = lean_ctor_get(v___x_4196_, 1);
                                    v_isSharedCheck_4251_ = (!lean_is_exclusive(v___x_4196_)) as u8;
                                    if v_isSharedCheck_4251_ == 0 {
                                        v___x_4246_ = v___x_4196_;
                                        v_isShared_4247_ = v_isSharedCheck_4251_;
                                        state = 9;
                                        continue;
                                    } else {
                                        lean_inc(v_err_4244_);
                                        lean_inc(v_pos_4243_);
                                        lean_dec(v___x_4196_);
                                        v___x_4246_ = lean_box(0);
                                        v_isShared_4247_ = v_isSharedCheck_4251_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_res_4192_);
                                lean_dec(v_res_4189_);
                                lean_dec_ref(v___x_4186_);
                                lean_dec(v_res_4178_);
                                v_pos_4252_ = lean_ctor_get(v___x_4193_, 0);
                                v_err_4253_ = lean_ctor_get(v___x_4193_, 1);
                                v_isSharedCheck_4260_ = (!lean_is_exclusive(v___x_4193_)) as u8;
                                if v_isSharedCheck_4260_ == 0 {
                                    v___x_4255_ = v___x_4193_;
                                    v_isShared_4256_ = v_isSharedCheck_4260_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_inc(v_err_4253_);
                                    lean_inc(v_pos_4252_);
                                    lean_dec(v___x_4193_);
                                    v___x_4255_ = lean_box(0);
                                    v_isShared_4256_ = v_isSharedCheck_4260_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_res_4189_);
                            lean_dec_ref(v___x_4186_);
                            lean_dec(v_res_4178_);
                            v_pos_4261_ = lean_ctor_get(v___x_4190_, 0);
                            v_err_4262_ = lean_ctor_get(v___x_4190_, 1);
                            v_isSharedCheck_4269_ = (!lean_is_exclusive(v___x_4190_)) as u8;
                            if v_isSharedCheck_4269_ == 0 {
                                v___x_4264_ = v___x_4190_;
                                v_isShared_4265_ = v_isSharedCheck_4269_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_err_4262_);
                                lean_inc(v_pos_4261_);
                                lean_dec(v___x_4190_);
                                v___x_4264_ = lean_box(0);
                                v_isShared_4265_ = v_isSharedCheck_4269_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_4186_);
                        lean_dec(v_res_4178_);
                        v_pos_4270_ = lean_ctor_get(v___x_4187_, 0);
                        v_err_4271_ = lean_ctor_get(v___x_4187_, 1);
                        v_isSharedCheck_4278_ = (!lean_is_exclusive(v___x_4187_)) as u8;
                        if v_isSharedCheck_4278_ == 0 {
                            v___x_4273_ = v___x_4187_;
                            v_isShared_4274_ = v_isSharedCheck_4278_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_err_4271_);
                            lean_inc(v_pos_4270_);
                            lean_dec(v___x_4187_);
                            v___x_4273_ = lean_box(0);
                            v_isShared_4274_ = v_isSharedCheck_4278_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    v_pos_4279_ = lean_ctor_get(v___x_4177_, 0);
                    v_err_4280_ = lean_ctor_get(v___x_4177_, 1);
                    v_isSharedCheck_4287_ = (!lean_is_exclusive(v___x_4177_)) as u8;
                    if v_isSharedCheck_4287_ == 0 {
                        v___x_4282_ = v___x_4177_;
                        v_isShared_4283_ = v_isSharedCheck_4287_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_err_4280_);
                        lean_inc(v_pos_4279_);
                        lean_dec(v___x_4177_);
                        v___x_4282_ = lean_box(0);
                        v_isShared_4283_ = v_isSharedCheck_4287_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4211_ = lean_alloc_ctor(0, 8, (0) as u32);
                lean_ctor_set(v___x_4211_, 0, v_res_4178_);
                lean_ctor_set(v___x_4211_, 1, v_res_4189_);
                lean_ctor_set(v___x_4211_, 2, v_res_4192_);
                lean_ctor_set(v___x_4211_, 3, v_res_4195_);
                lean_ctor_set(v___x_4211_, 4, v_res_4198_);
                lean_ctor_set(v___x_4211_, 5, v_res_4201_);
                lean_ctor_set(v___x_4211_, 6, v_res_4204_);
                lean_ctor_set(v___x_4211_, 7, v_res_4207_);
                if v_isShared_4210_ == 0 {
                    lean_ctor_set(v___x_4209_, 1, v___x_4211_);
                    v___x_4213_ = v___x_4209_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4214_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_pos_4206_);
                    lean_ctor_set(v_reuseFailAlloc_4214_, 1, v___x_4211_);
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
                    v_reuseFailAlloc_4223_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_pos_4216_);
                    lean_ctor_set(v_reuseFailAlloc_4223_, 1, v_err_4217_);
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
                    v_reuseFailAlloc_4232_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_pos_4225_);
                    lean_ctor_set(v_reuseFailAlloc_4232_, 1, v_err_4226_);
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
                    v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_pos_4234_);
                    lean_ctor_set(v_reuseFailAlloc_4241_, 1, v_err_4235_);
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
                    v_reuseFailAlloc_4250_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_pos_4243_);
                    lean_ctor_set(v_reuseFailAlloc_4250_, 1, v_err_4244_);
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
                    v_reuseFailAlloc_4259_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_pos_4252_);
                    lean_ctor_set(v_reuseFailAlloc_4259_, 1, v_err_4253_);
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
                    v_reuseFailAlloc_4268_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4268_, 0, v_pos_4261_);
                    lean_ctor_set(v_reuseFailAlloc_4268_, 1, v_err_4262_);
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
                    v_reuseFailAlloc_4277_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_pos_4270_);
                    lean_ctor_set(v_reuseFailAlloc_4277_, 1, v_err_4271_);
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
                    v_reuseFailAlloc_4286_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_pos_4279_);
                    lean_ctor_set(v_reuseFailAlloc_4286_, 1, v_err_4280_);
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
    mut v_as_4288_: *mut LeanObject,
    mut v_sz_4289_: usize,
    mut v_i_4290_: usize,
    mut v_b_4291_: *mut LeanObject,
    mut v___y_4292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4293_: u8 = 0;
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: u8 = 0;
    let mut v___x_4297_: u32 = 0;
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: usize = 0;
    let mut v___x_4300_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4293_ = lean_usize_dec_lt(v_i_4290_, v_sz_4289_);
                if v___x_4293_ == 0 {
                    v___x_4294_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4294_, 0, v___y_4292_);
                    lean_ctor_set(v___x_4294_, 1, v_b_4291_);
                    return v___x_4294_;
                } else {
                    v_a_4295_ = lean_array_uget_borrowed(v_as_4288_, v_i_4290_);
                    v___x_4296_ = (lean_unbox(v_a_4295_) as u8);
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
    mut v_as_4302_: *mut LeanObject,
    mut v_sz_4303_: *mut LeanObject,
    mut v_i_4304_: *mut LeanObject,
    mut v_b_4305_: *mut LeanObject,
    mut v___y_4306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4307_: usize = 0;
    let mut v_i_boxed_4308_: usize = 0;
    let mut v_res_4309_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4307_ = lean_unbox_usize(v_sz_4303_);
    lean_dec(v_sz_4303_);
    v_i_boxed_4308_ = lean_unbox_usize(v_i_4304_);
    lean_dec(v_i_4304_);
    v_res_4309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1(v_as_4302_, v_sz_boxed_4307_, v_i_boxed_4308_, v_b_4305_, v___y_4306_);
    lean_dec_ref(v_as_4302_);
    return v_res_4309_;
}
pub unsafe fn l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0(
    mut v_acc_4313_: *mut LeanObject,
    mut v_a_4314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: u8 = 0;
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: u8 = 0;
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: u8 = 0;
    let mut v_c_4330_: u8 = 0;
    let mut v___x_4331_: u8 = 0;
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4334_: u8 = 0;
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4343_: u8 = 0;
    let mut v_unused_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4315_ = lean_ctor_get(v_a_4314_, 0);
                v_idx_4316_ = lean_ctor_get(v_a_4314_, 1);
                lean_inc(v_idx_4316_);
                v___x_4326_ = lean_byte_array_size(v_array_4315_);
                v___x_4327_ = lean_nat_dec_lt(v_idx_4316_, v___x_4326_);
                if v___x_4327_ == 0 {
                    v___x_4328_ = lean_box(0);
                    lean_inc(v_idx_4316_);
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
                            lean_inc_ref(v_array_4315_);
                            v_isSharedCheck_4343_ = (!lean_is_exclusive(v_a_4314_)) as u8;
                            if v_isSharedCheck_4343_ == 0 {
                                v_unused_4344_ = lean_ctor_get(v_a_4314_, 1);
                                lean_dec(v_unused_4344_);
                                v_unused_4345_ = lean_ctor_get(v_a_4314_, 0);
                                lean_dec(v_unused_4345_);
                                v___x_4333_ = v_a_4314_;
                                v_isShared_4334_ = v_isSharedCheck_4343_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v_a_4314_);
                                v___x_4333_ = lean_box(0);
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
                lean_dec(v_idx_4319_);
                lean_dec(v_idx_4316_);
                if v___x_4321_ == 0 {
                    lean_dec_ref(v_acc_4313_);
                    lean_inc(v_err_4320_);
                    v___x_4322_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4322_, 0, v_pos_4318_);
                    lean_ctor_set(v___x_4322_, 1, v_err_4320_);
                    return v___x_4322_;
                } else {
                    v___x_4323_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4323_, 0, v_pos_4318_);
                    lean_ctor_set(v___x_4323_, 1, v_acc_4313_);
                    return v___x_4323_;
                }
            }
            2 => {
                v___x_4325_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0___closed__1;
                lean_inc(v_idx_4316_);
                v_pos_4318_ = v_a_4314_;
                v_idx_4319_ = v_idx_4316_;
                v_err_4320_ = v___x_4325_;
                state = 1;
                continue;
            }
            3 => {
                v___x_4335_ = lean_unsigned_to_nat(1);
                v___x_4336_ = lean_nat_add(v_idx_4316_, v___x_4335_);
                lean_dec(v_idx_4316_);
                if v_isShared_4334_ == 0 {
                    lean_ctor_set(v___x_4333_, 1, v___x_4336_);
                    v_it_x27_4338_ = v___x_4333_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4342_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_array_4315_);
                    lean_ctor_set(v_reuseFailAlloc_4342_, 1, v___x_4336_);
                    v_it_x27_4338_ = v_reuseFailAlloc_4342_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4339_ = lean_box((v_c_4330_) as usize);
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
    mut v_a_4348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4354_: u8 = 0;
    let mut v___x_4355_: u8 = 0;
    let mut v___x_4356_: u8 = 0;
    let mut v___x_4357_: u8 = 0;
    let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4367_: usize = 0;
    let mut v___x_4368_: usize = 0;
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4374_: u8 = 0;
    let mut v___x_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4379_: u8 = 0;
    let mut v_pos_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4384_: u8 = 0;
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4388_: u8 = 0;
    let mut v_pos_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4393_: u8 = 0;
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4397_: u8 = 0;
    let mut v_isSharedCheck_4398_: u8 = 0;
    let mut v_pos_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4402_: u8 = 0;
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4407_: u8 = 0;
    let mut v_unused_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4349_ =
                    l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pu8(
                        v_a_4348_,
                    );
                if lean_obj_tag(v___x_4349_) == 0 {
                    v_pos_4350_ = lean_ctor_get(v___x_4349_, 0);
                    v_res_4351_ = lean_ctor_get(v___x_4349_, 1);
                    v_isSharedCheck_4398_ = (!lean_is_exclusive(v___x_4349_)) as u8;
                    if v_isSharedCheck_4398_ == 0 {
                        v___x_4353_ = v___x_4349_;
                        v_isShared_4354_ = v_isSharedCheck_4398_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_res_4351_);
                        lean_inc(v_pos_4350_);
                        lean_dec(v___x_4349_);
                        v___x_4353_ = lean_box(0);
                        v_isShared_4354_ = v_isSharedCheck_4398_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_4399_ = lean_ctor_get(v___x_4349_, 0);
                    v_isSharedCheck_4407_ = (!lean_is_exclusive(v___x_4349_)) as u8;
                    if v_isSharedCheck_4407_ == 0 {
                        v_unused_4408_ = lean_ctor_get(v___x_4349_, 1);
                        lean_dec(v_unused_4408_);
                        v___x_4401_ = v___x_4349_;
                        v_isShared_4402_ = v_isSharedCheck_4407_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_pos_4399_);
                        lean_dec(v___x_4349_);
                        v___x_4401_ = lean_box(0);
                        v_isShared_4402_ = v_isSharedCheck_4407_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4355_ = 10;
                v___x_4356_ = (lean_unbox(v_res_4351_) as u8);
                lean_dec(v_res_4351_);
                v___x_4357_ = lean_uint8_dec_eq(v___x_4356_, v___x_4355_);
                if v___x_4357_ == 0 {
                    v___x_4358_ = lean_box(0);
                    if v_isShared_4354_ == 0 {
                        lean_ctor_set(v___x_4353_, 1, v___x_4358_);
                        v___x_4360_ = v___x_4353_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4361_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_pos_4350_);
                        lean_ctor_set(v_reuseFailAlloc_4361_, 1, v___x_4358_);
                        v___x_4360_ = v_reuseFailAlloc_4361_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4353_);
                    v___x_4362_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter___closed__0;
                    v___x_4363_ = l_Std_Internal_Parsec_manyCore___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__0(v___x_4362_, v_pos_4350_);
                    if lean_obj_tag(v___x_4363_) == 0 {
                        v_pos_4364_ = lean_ctor_get(v___x_4363_, 0);
                        lean_inc(v_pos_4364_);
                        v_res_4365_ = lean_ctor_get(v___x_4363_, 1);
                        lean_inc(v_res_4365_);
                        lean_dec_ref_known(v___x_4363_, 2);
                        v___x_4366_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations_spec__0___redArg___closed__0;
                        v_sz_4367_ = lean_array_size(v_res_4365_);
                        v___x_4368_ = 0usize;
                        v___x_4369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseFooter_spec__1(v_res_4365_, v_sz_4367_, v___x_4368_, v___x_4366_, v_pos_4364_);
                        lean_dec(v_res_4365_);
                        if lean_obj_tag(v___x_4369_) == 0 {
                            v_pos_4370_ = lean_ctor_get(v___x_4369_, 0);
                            v_res_4371_ = lean_ctor_get(v___x_4369_, 1);
                            v_isSharedCheck_4379_ = (!lean_is_exclusive(v___x_4369_)) as u8;
                            if v_isSharedCheck_4379_ == 0 {
                                v___x_4373_ = v___x_4369_;
                                v_isShared_4374_ = v_isSharedCheck_4379_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_res_4371_);
                                lean_inc(v_pos_4370_);
                                lean_dec(v___x_4369_);
                                v___x_4373_ = lean_box(0);
                                v_isShared_4374_ = v_isSharedCheck_4379_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_pos_4380_ = lean_ctor_get(v___x_4369_, 0);
                            v_err_4381_ = lean_ctor_get(v___x_4369_, 1);
                            v_isSharedCheck_4388_ = (!lean_is_exclusive(v___x_4369_)) as u8;
                            if v_isSharedCheck_4388_ == 0 {
                                v___x_4383_ = v___x_4369_;
                                v_isShared_4384_ = v_isSharedCheck_4388_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_err_4381_);
                                lean_inc(v_pos_4380_);
                                lean_dec(v___x_4369_);
                                v___x_4383_ = lean_box(0);
                                v_isShared_4384_ = v_isSharedCheck_4388_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v_pos_4389_ = lean_ctor_get(v___x_4363_, 0);
                        v_err_4390_ = lean_ctor_get(v___x_4363_, 1);
                        v_isSharedCheck_4397_ = (!lean_is_exclusive(v___x_4363_)) as u8;
                        if v_isSharedCheck_4397_ == 0 {
                            v___x_4392_ = v___x_4363_;
                            v_isShared_4393_ = v_isSharedCheck_4397_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_err_4390_);
                            lean_inc(v_pos_4389_);
                            lean_dec(v___x_4363_);
                            v___x_4392_ = lean_box(0);
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
                v___x_4375_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4375_, 0, v_res_4371_);
                if v_isShared_4374_ == 0 {
                    lean_ctor_set(v___x_4373_, 1, v___x_4375_);
                    v___x_4377_ = v___x_4373_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4378_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_pos_4370_);
                    lean_ctor_set(v_reuseFailAlloc_4378_, 1, v___x_4375_);
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
                    v_reuseFailAlloc_4387_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_pos_4380_);
                    lean_ctor_set(v_reuseFailAlloc_4387_, 1, v_err_4381_);
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
                    v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_pos_4389_);
                    lean_ctor_set(v_reuseFailAlloc_4396_, 1, v_err_4390_);
                    v___x_4395_ = v_reuseFailAlloc_4396_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4395_;
            }
            9 => {
                v___x_4403_ = lean_box(0);
                if v_isShared_4402_ == 0 {
                    lean_ctor_set(v___x_4401_, 1, v___x_4403_);
                    v___x_4405_ = v___x_4401_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4406_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_pos_4399_);
                    lean_ctor_set(v_reuseFailAlloc_4406_, 1, v___x_4403_);
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
    mut v_a_4409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4416_: u8 = 0;
    let mut v_idx_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: u8 = 0;
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4426_: u8 = 0;
    let mut v_unused_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isutcnt_4431_: u32 = 0;
    let mut v_isstdcnt_4432_: u32 = 0;
    let mut v_leapcnt_4433_: u32 = 0;
    let mut v_timecnt_4434_: u32 = 0;
    let mut v_typecnt_4435_: u32 = 0;
    let mut v_charcnt_4436_: u32 = 0;
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4461_: u8 = 0;
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4467_: u8 = 0;
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4476_: u8 = 0;
    let mut v_pos_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4479_: u8 = 0;
    let mut v_pos_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_a_4409_);
                v___x_4428_ =
                    l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseHeader(
                        v_a_4409_,
                    );
                if lean_obj_tag(v___x_4428_) == 0 {
                    v_res_4429_ = lean_ctor_get(v___x_4428_, 1);
                    lean_inc(v_res_4429_);
                    v_pos_4430_ = lean_ctor_get(v___x_4428_, 0);
                    lean_inc(v_pos_4430_);
                    lean_dec_ref_known(v___x_4428_, 2);
                    v_isutcnt_4431_ = lean_ctor_get_uint32(v_res_4429_, 0 as u32);
                    v_isstdcnt_4432_ = lean_ctor_get_uint32(v_res_4429_, 4 as u32);
                    v_leapcnt_4433_ = lean_ctor_get_uint32(v_res_4429_, 8 as u32);
                    v_timecnt_4434_ = lean_ctor_get_uint32(v_res_4429_, 12 as u32);
                    v_typecnt_4435_ = lean_ctor_get_uint32(v_res_4429_, 16 as u32);
                    v_charcnt_4436_ = lean_ctor_get_uint32(v_res_4429_, 20 as u32);
                    v___x_4437_ = lean_alloc_closure(
                        l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_pi64
                            as *mut core::ffi::c_void,
                        1,
                        0,
                    );
                    lean_inc_ref(v___x_4437_);
                    v___x_4438_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionTimes(v___x_4437_, v_timecnt_4434_, v_pos_4430_);
                    if lean_obj_tag(v___x_4438_) == 0 {
                        v_pos_4439_ = lean_ctor_get(v___x_4438_, 0);
                        lean_inc(v_pos_4439_);
                        v_res_4440_ = lean_ctor_get(v___x_4438_, 1);
                        lean_inc(v_res_4440_);
                        lean_dec_ref_known(v___x_4438_, 2);
                        v___x_4441_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTransitionIndices(v_timecnt_4434_, v_pos_4439_);
                        if lean_obj_tag(v___x_4441_) == 0 {
                            v_pos_4442_ = lean_ctor_get(v___x_4441_, 0);
                            lean_inc(v_pos_4442_);
                            v_res_4443_ = lean_ctor_get(v___x_4441_, 1);
                            lean_inc(v_res_4443_);
                            lean_dec_ref_known(v___x_4441_, 2);
                            v___x_4444_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLocalTimeTypes(v_typecnt_4435_, v_pos_4442_);
                            if lean_obj_tag(v___x_4444_) == 0 {
                                v_pos_4445_ = lean_ctor_get(v___x_4444_, 0);
                                lean_inc(v_pos_4445_);
                                v_res_4446_ = lean_ctor_get(v___x_4444_, 1);
                                lean_inc(v_res_4446_);
                                lean_dec_ref_known(v___x_4444_, 2);
                                v___x_4447_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseAbbreviations(v_res_4446_, v_charcnt_4436_, v_pos_4445_);
                                if lean_obj_tag(v___x_4447_) == 0 {
                                    v_pos_4448_ = lean_ctor_get(v___x_4447_, 0);
                                    lean_inc(v_pos_4448_);
                                    v_res_4449_ = lean_ctor_get(v___x_4447_, 1);
                                    lean_inc(v_res_4449_);
                                    lean_dec_ref_known(v___x_4447_, 2);
                                    v___x_4450_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseLeapSeconds(v___x_4437_, v_leapcnt_4433_, v_pos_4448_);
                                    if lean_obj_tag(v___x_4450_) == 0 {
                                        v_pos_4451_ = lean_ctor_get(v___x_4450_, 0);
                                        lean_inc(v_pos_4451_);
                                        v_res_4452_ = lean_ctor_get(v___x_4450_, 1);
                                        lean_inc(v_res_4452_);
                                        lean_dec_ref_known(v___x_4450_, 2);
                                        v___x_4453_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_isstdcnt_4432_, v_pos_4451_);
                                        if lean_obj_tag(v___x_4453_) == 0 {
                                            v_pos_4454_ = lean_ctor_get(v___x_4453_, 0);
                                            lean_inc(v_pos_4454_);
                                            v_res_4455_ = lean_ctor_get(v___x_4453_, 1);
                                            lean_inc(v_res_4455_);
                                            lean_dec_ref_known(v___x_4453_, 2);
                                            v___x_4456_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseIndicators(v_isutcnt_4431_, v_pos_4454_);
                                            if lean_obj_tag(v___x_4456_) == 0 {
                                                v_pos_4457_ = lean_ctor_get(v___x_4456_, 0);
                                                v_res_4458_ = lean_ctor_get(v___x_4456_, 1);
                                                v_isSharedCheck_4479_ =
                                                    (!lean_is_exclusive(v___x_4456_)) as u8;
                                                if v_isSharedCheck_4479_ == 0 {
                                                    v___x_4460_ = v___x_4456_;
                                                    v_isShared_4461_ = v_isSharedCheck_4479_;
                                                    state = 5;
                                                    continue;
                                                } else {
                                                    lean_inc(v_res_4458_);
                                                    lean_inc(v_pos_4457_);
                                                    lean_dec(v___x_4456_);
                                                    v___x_4460_ = lean_box(0);
                                                    v_isShared_4461_ = v_isSharedCheck_4479_;
                                                    state = 5;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec(v_res_4455_);
                                                lean_dec(v_res_4452_);
                                                lean_dec(v_res_4449_);
                                                lean_dec(v_res_4446_);
                                                lean_dec(v_res_4443_);
                                                lean_dec(v_res_4440_);
                                                lean_dec(v_res_4429_);
                                                v_pos_4480_ = lean_ctor_get(v___x_4456_, 0);
                                                lean_inc(v_pos_4480_);
                                                v_err_4481_ = lean_ctor_get(v___x_4456_, 1);
                                                lean_inc(v_err_4481_);
                                                lean_dec_ref_known(v___x_4456_, 2);
                                                v_pos_4411_ = v_pos_4480_;
                                                v_err_4412_ = v_err_4481_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v_res_4452_);
                                            lean_dec(v_res_4449_);
                                            lean_dec(v_res_4446_);
                                            lean_dec(v_res_4443_);
                                            lean_dec(v_res_4440_);
                                            lean_dec(v_res_4429_);
                                            v_pos_4482_ = lean_ctor_get(v___x_4453_, 0);
                                            lean_inc(v_pos_4482_);
                                            v_err_4483_ = lean_ctor_get(v___x_4453_, 1);
                                            lean_inc(v_err_4483_);
                                            lean_dec_ref_known(v___x_4453_, 2);
                                            v_pos_4411_ = v_pos_4482_;
                                            v_err_4412_ = v_err_4483_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_res_4449_);
                                        lean_dec(v_res_4446_);
                                        lean_dec(v_res_4443_);
                                        lean_dec(v_res_4440_);
                                        lean_dec(v_res_4429_);
                                        v_pos_4484_ = lean_ctor_get(v___x_4450_, 0);
                                        lean_inc(v_pos_4484_);
                                        v_err_4485_ = lean_ctor_get(v___x_4450_, 1);
                                        lean_inc(v_err_4485_);
                                        lean_dec_ref_known(v___x_4450_, 2);
                                        v_pos_4411_ = v_pos_4484_;
                                        v_err_4412_ = v_err_4485_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_res_4446_);
                                    lean_dec(v_res_4443_);
                                    lean_dec(v_res_4440_);
                                    lean_dec_ref(v___x_4437_);
                                    lean_dec(v_res_4429_);
                                    v_pos_4486_ = lean_ctor_get(v___x_4447_, 0);
                                    lean_inc(v_pos_4486_);
                                    v_err_4487_ = lean_ctor_get(v___x_4447_, 1);
                                    lean_inc(v_err_4487_);
                                    lean_dec_ref_known(v___x_4447_, 2);
                                    v_pos_4411_ = v_pos_4486_;
                                    v_err_4412_ = v_err_4487_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_res_4443_);
                                lean_dec(v_res_4440_);
                                lean_dec_ref(v___x_4437_);
                                lean_dec(v_res_4429_);
                                v_pos_4488_ = lean_ctor_get(v___x_4444_, 0);
                                lean_inc(v_pos_4488_);
                                v_err_4489_ = lean_ctor_get(v___x_4444_, 1);
                                lean_inc(v_err_4489_);
                                lean_dec_ref_known(v___x_4444_, 2);
                                v_pos_4411_ = v_pos_4488_;
                                v_err_4412_ = v_err_4489_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_res_4440_);
                            lean_dec_ref(v___x_4437_);
                            lean_dec(v_res_4429_);
                            v_pos_4490_ = lean_ctor_get(v___x_4441_, 0);
                            lean_inc(v_pos_4490_);
                            v_err_4491_ = lean_ctor_get(v___x_4441_, 1);
                            lean_inc(v_err_4491_);
                            lean_dec_ref_known(v___x_4441_, 2);
                            v_pos_4411_ = v_pos_4490_;
                            v_err_4412_ = v_err_4491_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_4437_);
                        lean_dec(v_res_4429_);
                        v_pos_4492_ = lean_ctor_get(v___x_4438_, 0);
                        lean_inc(v_pos_4492_);
                        v_err_4493_ = lean_ctor_get(v___x_4438_, 1);
                        lean_inc(v_err_4493_);
                        lean_dec_ref_known(v___x_4438_, 2);
                        v_pos_4411_ = v_pos_4492_;
                        v_err_4412_ = v_err_4493_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_4494_ = lean_ctor_get(v___x_4428_, 0);
                    lean_inc(v_pos_4494_);
                    v_err_4495_ = lean_ctor_get(v___x_4428_, 1);
                    lean_inc(v_err_4495_);
                    lean_dec_ref_known(v___x_4428_, 2);
                    v_pos_4411_ = v_pos_4494_;
                    v_err_4412_ = v_err_4495_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_idx_4413_ = lean_ctor_get(v_a_4409_, 1);
                v_isSharedCheck_4426_ = (!lean_is_exclusive(v_a_4409_)) as u8;
                if v_isSharedCheck_4426_ == 0 {
                    v_unused_4427_ = lean_ctor_get(v_a_4409_, 0);
                    lean_dec(v_unused_4427_);
                    v___x_4415_ = v_a_4409_;
                    v_isShared_4416_ = v_isSharedCheck_4426_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_idx_4413_);
                    lean_dec(v_a_4409_);
                    v___x_4415_ = lean_box(0);
                    v_isShared_4416_ = v_isSharedCheck_4426_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_idx_4417_ = lean_ctor_get(v_pos_4411_, 1);
                v___x_4418_ = lean_nat_dec_eq(v_idx_4413_, v_idx_4417_);
                lean_dec(v_idx_4413_);
                if v___x_4418_ == 0 {
                    if v_isShared_4416_ == 0 {
                        lean_ctor_set_tag(v___x_4415_, 1);
                        lean_ctor_set(v___x_4415_, 1, v_err_4412_);
                        lean_ctor_set(v___x_4415_, 0, v_pos_4411_);
                        v___x_4420_ = v___x_4415_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_pos_4411_);
                        lean_ctor_set(v_reuseFailAlloc_4421_, 1, v_err_4412_);
                        v___x_4420_ = v_reuseFailAlloc_4421_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_err_4412_);
                    v___x_4422_ = lean_box(0);
                    if v_isShared_4416_ == 0 {
                        lean_ctor_set(v___x_4415_, 1, v___x_4422_);
                        lean_ctor_set(v___x_4415_, 0, v_pos_4411_);
                        v___x_4424_ = v___x_4415_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_pos_4411_);
                        lean_ctor_set(v_reuseFailAlloc_4425_, 1, v___x_4422_);
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
                if lean_obj_tag(v___x_4462_) == 0 {
                    lean_dec_ref(v_a_4409_);
                    v_pos_4463_ = lean_ctor_get(v___x_4462_, 0);
                    v_res_4464_ = lean_ctor_get(v___x_4462_, 1);
                    v_isSharedCheck_4476_ = (!lean_is_exclusive(v___x_4462_)) as u8;
                    if v_isSharedCheck_4476_ == 0 {
                        v___x_4466_ = v___x_4462_;
                        v_isShared_4467_ = v_isSharedCheck_4476_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_res_4464_);
                        lean_inc(v_pos_4463_);
                        lean_dec(v___x_4462_);
                        v___x_4466_ = lean_box(0);
                        v_isShared_4467_ = v_isSharedCheck_4476_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4460_);
                    lean_dec(v_res_4458_);
                    lean_dec(v_res_4455_);
                    lean_dec(v_res_4452_);
                    lean_dec(v_res_4449_);
                    lean_dec(v_res_4446_);
                    lean_dec(v_res_4443_);
                    lean_dec(v_res_4440_);
                    lean_dec(v_res_4429_);
                    v_pos_4477_ = lean_ctor_get(v___x_4462_, 0);
                    lean_inc(v_pos_4477_);
                    v_err_4478_ = lean_ctor_get(v___x_4462_, 1);
                    lean_inc(v_err_4478_);
                    lean_dec_ref_known(v___x_4462_, 2);
                    v_pos_4411_ = v_pos_4477_;
                    v_err_4412_ = v_err_4478_;
                    state = 1;
                    continue;
                }
            }
            6 => {
                v___x_4468_ = lean_alloc_ctor(0, 8, (0) as u32);
                lean_ctor_set(v___x_4468_, 0, v_res_4429_);
                lean_ctor_set(v___x_4468_, 1, v_res_4440_);
                lean_ctor_set(v___x_4468_, 2, v_res_4443_);
                lean_ctor_set(v___x_4468_, 3, v_res_4446_);
                lean_ctor_set(v___x_4468_, 4, v_res_4449_);
                lean_ctor_set(v___x_4468_, 5, v_res_4452_);
                lean_ctor_set(v___x_4468_, 6, v_res_4455_);
                lean_ctor_set(v___x_4468_, 7, v_res_4458_);
                if v_isShared_4461_ == 0 {
                    lean_ctor_set(v___x_4460_, 1, v_res_4464_);
                    lean_ctor_set(v___x_4460_, 0, v___x_4468_);
                    v___x_4470_ = v___x_4460_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4475_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4475_, 0, v___x_4468_);
                    lean_ctor_set(v_reuseFailAlloc_4475_, 1, v_res_4464_);
                    v___x_4470_ = v_reuseFailAlloc_4475_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4471_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4471_, 0, v___x_4470_);
                if v_isShared_4467_ == 0 {
                    lean_ctor_set(v___x_4466_, 1, v___x_4471_);
                    v___x_4473_ = v___x_4466_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4474_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_pos_4463_);
                    lean_ctor_set(v_reuseFailAlloc_4474_, 1, v___x_4471_);
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
pub unsafe fn l_Std_Time_TimeZone_TZif_parse(mut v_a_4496_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4505_: u8 = 0;
    let mut v___x_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4510_: u8 = 0;
    let mut v_pos_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4515_: u8 = 0;
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4519_: u8 = 0;
    let mut v_pos_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4524_: u8 = 0;
    let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4497_ =
                    l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV1(
                        v_a_4496_,
                    );
                if lean_obj_tag(v___x_4497_) == 0 {
                    v_pos_4498_ = lean_ctor_get(v___x_4497_, 0);
                    lean_inc(v_pos_4498_);
                    v_res_4499_ = lean_ctor_get(v___x_4497_, 1);
                    lean_inc(v_res_4499_);
                    lean_dec_ref_known(v___x_4497_, 2);
                    v___x_4500_ = l___private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_parseTZifV2(v_pos_4498_);
                    if lean_obj_tag(v___x_4500_) == 0 {
                        v_pos_4501_ = lean_ctor_get(v___x_4500_, 0);
                        v_res_4502_ = lean_ctor_get(v___x_4500_, 1);
                        v_isSharedCheck_4510_ = (!lean_is_exclusive(v___x_4500_)) as u8;
                        if v_isSharedCheck_4510_ == 0 {
                            v___x_4504_ = v___x_4500_;
                            v_isShared_4505_ = v_isSharedCheck_4510_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_res_4502_);
                            lean_inc(v_pos_4501_);
                            lean_dec(v___x_4500_);
                            v___x_4504_ = lean_box(0);
                            v_isShared_4505_ = v_isSharedCheck_4510_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_res_4499_);
                        v_pos_4511_ = lean_ctor_get(v___x_4500_, 0);
                        v_err_4512_ = lean_ctor_get(v___x_4500_, 1);
                        v_isSharedCheck_4519_ = (!lean_is_exclusive(v___x_4500_)) as u8;
                        if v_isSharedCheck_4519_ == 0 {
                            v___x_4514_ = v___x_4500_;
                            v_isShared_4515_ = v_isSharedCheck_4519_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_err_4512_);
                            lean_inc(v_pos_4511_);
                            lean_dec(v___x_4500_);
                            v___x_4514_ = lean_box(0);
                            v_isShared_4515_ = v_isSharedCheck_4519_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_pos_4520_ = lean_ctor_get(v___x_4497_, 0);
                    v_err_4521_ = lean_ctor_get(v___x_4497_, 1);
                    v_isSharedCheck_4528_ = (!lean_is_exclusive(v___x_4497_)) as u8;
                    if v_isSharedCheck_4528_ == 0 {
                        v___x_4523_ = v___x_4497_;
                        v_isShared_4524_ = v_isSharedCheck_4528_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_err_4521_);
                        lean_inc(v_pos_4520_);
                        lean_dec(v___x_4497_);
                        v___x_4523_ = lean_box(0);
                        v_isShared_4524_ = v_isSharedCheck_4528_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4506_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4506_, 0, v_res_4499_);
                lean_ctor_set(v___x_4506_, 1, v_res_4502_);
                if v_isShared_4505_ == 0 {
                    lean_ctor_set(v___x_4504_, 1, v___x_4506_);
                    v___x_4508_ = v___x_4504_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4509_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_pos_4501_);
                    lean_ctor_set(v_reuseFailAlloc_4509_, 1, v___x_4506_);
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
                    v_reuseFailAlloc_4518_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_pos_4511_);
                    lean_ctor_set(v_reuseFailAlloc_4518_, 1, v_err_4512_);
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
                    v_reuseFailAlloc_4527_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_pos_4520_);
                    lean_ctor_set(v_reuseFailAlloc_4527_, 1, v_err_4521_);
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
pub unsafe fn runtime_initialize_Std_Time_Zoned_Database_TzIf(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Parsec(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Repr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_Time_TimeZone_TZif_instInhabitedHeader_default =
        _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader_default();
    lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedHeader_default);
    l_Std_Time_TimeZone_TZif_instInhabitedHeader =
        _init_l_Std_Time_TimeZone_TZif_instInhabitedHeader();
    lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedHeader);
    l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default =
        _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default();
    lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType_default);
    l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType =
        _init_l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType();
    lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedLocalTimeType);
    l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default =
        _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default();
    lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond_default);
    l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond =
        _init_l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond();
    lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedLeapSecond);
    l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default =
        _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default();
    lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedTZifV1_default);
    l_Std_Time_TimeZone_TZif_instInhabitedTZifV1 =
        _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV1();
    lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedTZifV1);
    l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default =
        _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default();
    lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedTZifV2_default);
    l_Std_Time_TimeZone_TZif_instInhabitedTZifV2 =
        _init_l_Std_Time_TimeZone_TZif_instInhabitedTZifV2();
    lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedTZifV2);
    l_Std_Time_TimeZone_TZif_instInhabitedTZif_default =
        _init_l_Std_Time_TimeZone_TZif_instInhabitedTZif_default();
    lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedTZif_default);
    l_Std_Time_TimeZone_TZif_instInhabitedTZif = _init_l_Std_Time_TimeZone_TZif_instInhabitedTZif();
    lean_mark_persistent(l_Std_Time_TimeZone_TZif_instInhabitedTZif);
    l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1 = _init_l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1();
    lean_mark_persistent(l_panic___at___00__private_Std_Time_Zoned_Database_TzIf_0__Std_Time_TimeZone_TZif_toUInt32_spec__0___boxed__const__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Zoned_Database_TzIf(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Zoned_Database_TzIf(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Internal_Parsec(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_Repr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_Database_TzIf(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Time_Zoned_Database_TzIf(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Time_Zoned_Database_TzIf(builtin);
}
